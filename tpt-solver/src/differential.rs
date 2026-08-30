//! Differential and rate-tracking test harness (spec §5.4, §6.3).
//!
//! Two complementary checks run over a randomized CNF corpus:
//!
//! 1. **Differential** — every problem is solved by *both* the optimized CDCL engine
//!    and the reference DPLL solver; their (untrusted) claims must agree, and *every*
//!    answer the trusted checker emits must be `Accept`. A disagreement between the
//!    two engines, or a non-`Accept` verdict, is exactly the kind of soundness bug
//!    differential testing exists to surface.
//! 2. **Rate gate** (§6.3) — the accept/reject/inconclusive triad is tracked and the
//!    reject rate is gated below a merge threshold, so a heuristic change that stays
//!    safe but degrades productivity is caught, not just a wrong-answer bug.
//!
//! A third lane, [`differential_vs_z3_when_available`], shells out to `z3` when it is
//! on `PATH` (e.g. a CI runner that installs it) and compares against a real external
//! oracle; it is a no-op where `z3` is absent so the suite stays green offline.

use crate::policy::VerdictTracker;
use crate::reference::{
    solve_and_check, solve_and_check_arrays, solve_and_check_bv, solve_and_check_cdcl,
    solve_and_check_lra, Problem,
};
use std::process::Command;
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::engine::SolveResult;
use tpt_solver_core::lra::LinConstraint;
use tpt_solver_core::rational::Rational;

/// Deterministic LCG so the corpus is reproducible across runs and CI.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        // Knuth's multiplicative LCG constants.
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    /// A value in `[0, n)`.
    fn below(&mut self, n: u32) -> u32 {
        (self.next() % n as u64) as u32
    }
}

/// Generate a random CNF with `vars` variables, `clauses` clauses, each of `width`
/// literals, chosen by the LCG.
fn gen_problem(rng: &mut Lcg, vars: u32, clauses: usize, width: usize) -> Problem {
    let mut cls = Vec::with_capacity(clauses);
    for _ in 0..clauses {
        let mut c = Vec::with_capacity(width);
        for _ in 0..width {
            let v = 1 + rng.below(vars);
            let sign: i32 = if rng.below(2) == 0 { 1 } else { -1 };
            c.push(sign * v as i32);
        }
        cls.push(c);
    }
    Problem {
        var_count: vars,
        clauses: cls,
    }
}

/// One differential step: solve with both engines, assert agreement and that the
/// checker accepts, then return the verdict produced by the certified pipeline.
fn check_one(p: &Problem, fuel: u64) -> Outcome {
    let (cdcl_claim, cdcl_verdict) = solve_and_check_cdcl(p, fuel);
    let (ref_claim, ref_verdict) = solve_and_check(p, fuel);

    // Differential: the two untrusted engines must agree on Sat/Unsat.
    assert_eq!(
        cdcl_claim, ref_claim,
        "engines disagreed on claim for var_count={} clauses={:?}",
        p.var_count, p.clauses
    );
    // The trusted kernel must accept any non-Unknown answer from either path.
    if cdcl_claim != SolveResult::Unknown {
        if !cdcl_verdict.is_accept() {
            eprintln!(
                "CDCL BUG: claim={:?} verdict={:?} problem={:?}",
                cdcl_claim, cdcl_verdict, p
            );
        }
        assert!(
            cdcl_verdict.is_accept(),
            "CDCL verdict was not Accept: {:?}",
            cdcl_verdict
        );
    }
    if ref_claim != SolveResult::Unknown {
        assert!(
            ref_verdict.is_accept(),
            "reference verdict was not Accept: {:?}",
            ref_verdict
        );
    }
    // The certified pipeline (CDCL -> fallback) must also be Accept or Unknown.
    let (_claim, verdict, _dump) = crate::policy::solve_certified(p, fuel);
    verdict
}

#[test]
fn differential_corpus_agrees_and_is_accepted() {
    let mut rng = Lcg(0x1234_5678);
    let mut tracker = VerdictTracker::new();
    let corpus_size = 200usize;
    for _ in 0..corpus_size {
        let vars = 1 + rng.below(8);
        let clauses = 1 + rng.below(12);
        let width = 2 + rng.below(3);
        let p = gen_problem(&mut rng, vars, clauses as usize, width as usize);
        let verdict = check_one(&p, 200_000);
        tracker.record(verdict);
    }

    // §6.3 gate: the kernel must never accept a wrong answer, and the two engines
    // must agree, so the reject rate on the corpus is exactly zero.
    assert_eq!(tracker.reject(), 0, "reject rate must be 0 on the corpus");
    assert!(
        tracker.accept() + tracker.inconclusive() > 0,
        "corpus produced no verdicts at all"
    );
    assert!(
        tracker.within_reject_threshold(0.0),
        "reject-rate threshold violated: rate = {}",
        tracker.reject_rate()
    );
}

/// Serialize a [`Problem`] as a QF_SAT SMT-LIB2 script for an external oracle.
fn problem_to_smt2(p: &Problem) -> String {
    let mut s = String::from("(set-logic QF_SAT)\n");
    for v in 1..=p.var_count {
        s.push_str(&format!("(declare-fun v{} () Bool)\n", v));
    }
    for c in &p.clauses {
        let mut disj = String::from("(assert (or");
        for &l in c {
            let v = l.unsigned_abs();
            if l > 0 {
                disj.push_str(&format!(" v{}", v));
            } else {
                disj.push_str(&format!(" (not v{})", v));
            }
        }
        disj.push_str("))\n");
        s.push_str(&disj);
    }
    s.push_str("(check-sat)\n");
    s
}

/// Whether the `z3` binary is available on `PATH`.
fn z3_present() -> bool {
    matches!(
        Command::new("z3").arg("-version").output(),
        Ok(o) if o.status.success()
    )
}

/// Run `z3` on an SMT-LIB2 script and parse its `sat`/`unsat` verdict. `None` if
/// `z3` couldn't be run, or answered `unknown` / produced no clear verdict.
fn run_z3(smt2: &str) -> Option<SolveResult> {
    let output = Command::new("z3")
        .arg("-in")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            child
                .stdin
                .as_mut()
                .unwrap()
                .write_all(smt2.as_bytes())
                .ok();
            child.wait_with_output()
        })
        .ok()?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    stdout.lines().find_map(|l| {
        let t = l.trim();
        if t == "sat" {
            Some(SolveResult::Sat)
        } else if t == "unsat" {
            Some(SolveResult::Unsat)
        } else {
            None
        }
    })
}

/// Differential testing against Z3 (spec §5.4). Runs only when the `z3` binary is on
/// `PATH`; otherwise it is a no-op so the suite stays green where Z3 is absent (e.g.
/// local machines). CI installs Z3 to exercise this lane for real.
#[test]
fn differential_vs_z3_when_available() {
    if !z3_present() {
        eprintln!("z3 not found on PATH; skipping Z3 differential test");
        return;
    }

    let mut rng = Lcg(0x9e37_79b9);
    for _ in 0..40 {
        let vars = 1 + rng.below(6);
        let clauses = 1 + rng.below(8);
        let width = 2 + rng.below(2);
        let p = gen_problem(&mut rng, vars, clauses as usize, width as usize);
        let smt2 = problem_to_smt2(&p);

        let z3_claim = match run_z3(&smt2) {
            Some(c) => c,
            None => continue,
        };

        let (claim, verdict) = solve_and_check_cdcl(&p, 200_000);
        assert_eq!(
            claim, z3_claim,
            "disagreement with Z3 on var_count={} clauses={:?}",
            p.var_count, p.clauses
        );
        assert!(
            verdict.is_accept(),
            "checker did not Accept the CDCL verdict vs Z3: {:?}",
            verdict
        );
    }
}

/// Generate a random small QF_LRA system: `n_cons` constraints over `n_vars`
/// variables, small integer coefficients/RHS so the generated SMT-LIB2 script
/// stays simple. Returned as raw `(coeffs, rhs)` pairs so the caller can both
/// build a [`LinConstraint`] system and serialize the identical numbers to
/// SMT-LIB2 without going through `Rational` (which has no public accessors).
fn gen_lra_problem(rng: &mut Lcg, n_vars: usize, n_cons: usize) -> Vec<(Vec<i64>, i64)> {
    let mut cons = Vec::with_capacity(n_cons);
    for _ in 0..n_cons {
        let coeffs: Vec<i64> = (0..n_vars).map(|_| rng.below(11) as i64 - 5).collect();
        let rhs = rng.below(21) as i64 - 10;
        cons.push((coeffs, rhs));
    }
    cons
}

fn lra_to_constraints(cons: &[(Vec<i64>, i64)]) -> Vec<LinConstraint> {
    cons.iter()
        .map(|(coeffs, rhs)| LinConstraint {
            coeffs: coeffs.iter().map(|&c| Rational::from_i64(c)).collect(),
            rhs: Rational::from_i64(*rhs),
        })
        .collect()
}

/// An SMT-LIB2 integer literal, using `(- n)` for negatives per the SMT-LIB2
/// grammar (a bare `-3` numeral is not valid syntax).
fn smt2_int(v: i64) -> String {
    if v < 0 {
        format!("(- {})", -v)
    } else {
        v.to_string()
    }
}

/// Serialize a random LRA system as a QF_LRA SMT-LIB2 script for an external oracle.
fn lra_to_smt2(cons: &[(Vec<i64>, i64)], n_vars: usize) -> String {
    let mut s = String::from("(set-logic QF_LRA)\n");
    for i in 0..n_vars {
        s.push_str(&format!("(declare-fun x{i} () Real)\n"));
    }
    for (coeffs, rhs) in cons {
        let mut lhs = String::from("(+ 0");
        for (i, &c) in coeffs.iter().enumerate() {
            lhs.push_str(&format!(" (* {} x{})", smt2_int(c), i));
        }
        lhs.push(')');
        s.push_str(&format!("(assert (<= {} {}))\n", lhs, smt2_int(*rhs)));
    }
    s.push_str("(check-sat)\n");
    s
}

/// Differential testing of the LRA path against Z3 (spec §5.4). Runs only when `z3`
/// is on `PATH`; otherwise a no-op, mirroring [`differential_vs_z3_when_available`].
#[test]
fn differential_lra_vs_z3_when_available() {
    if !z3_present() {
        eprintln!("z3 not found on PATH; skipping Z3 LRA differential test");
        return;
    }

    let mut rng = Lcg(0xabcd_ef01);
    for _ in 0..40 {
        let n_vars = 1 + rng.below(3) as usize;
        let n_cons = 1 + rng.below(4) as usize;
        let raw = gen_lra_problem(&mut rng, n_vars, n_cons);
        let cons = lra_to_constraints(&raw);
        let smt2 = lra_to_smt2(&raw, n_vars);

        let z3_claim = match run_z3(&smt2) {
            Some(c) => c,
            None => continue,
        };

        let (claim, verdict) = solve_and_check_lra(&cons, 200_000);
        assert_eq!(
            claim, z3_claim,
            "disagreement with Z3 on LRA system: {:?}",
            raw
        );
        assert!(
            verdict.is_accept(),
            "checker did not Accept the LRA verdict vs Z3: {:?}",
            verdict
        );
    }
}

// ---------------------------------------------------------------------------
// Bit-vector differential lane (QF_BV)
// ---------------------------------------------------------------------------

use tpt_solver_core::array::{ArrAssertion, ArrayExpr, ElemExpr};
use tpt_solver_core::bv::{BvAssertion, BvBinOp, BvTerm};

/// Serialize a core bit-vector term back to SMT-LIB2 syntax (`x{id}w{width}`
/// variables).
fn bv_term_to_smt2(t: &BvTerm) -> String {
    match t {
        BvTerm::Var { id, width } => format!("x{}w{}", id, width),
        BvTerm::Const { width, value } => {
            // Binary keeps the width exact (hex would round up to multiples
            // of four and change the sort on re-parse).
            format!("#b{:0wb$b}", value, wb = *width as usize)
        }
        BvTerm::Not { arg } => format!("(bvnot {})", bv_term_to_smt2(arg)),
        BvTerm::Neg { arg } => format!("(bvneg {})", bv_term_to_smt2(arg)),
        BvTerm::BinOp { op, lhs, rhs } => {
            let name = match op {
                BvBinOp::And => "bvand",
                BvBinOp::Or => "bvor",
                BvBinOp::Xor => "bvxor",
                BvBinOp::Add => "bvadd",
                _ => "bvsub",
            };
            format!(
                "({} {} {})",
                name,
                bv_term_to_smt2(lhs),
                bv_term_to_smt2(rhs)
            )
        }
        BvTerm::Shift { left, arg, amount } => {
            let w = arg.width();
            let name = if *left { "bvshl" } else { "bvlshr" };
            // Shift by a constant: emit an exactly-`w`-wide binary literal.
            format!(
                "({} {} #b{:0wb$b})",
                name,
                bv_term_to_smt2(arg),
                *amount as u64,
                wb = w as usize
            )
        }
        BvTerm::Concat { hi, lo } => {
            format!("(concat {} {})", bv_term_to_smt2(hi), bv_term_to_smt2(lo))
        }
        BvTerm::Extract { arg, hi, lo } => {
            format!("((_ extract {} {}) {})", hi, lo, bv_term_to_smt2(arg))
        }
    }
}

/// Collect `(id, width)` pairs for every variable occurring in `t`.
fn collect_bv_vars(t: &BvTerm, out: &mut Vec<(u32, u8)>) {
    match t {
        BvTerm::Var { id, width } => {
            if !out.iter().any(|&(i, _)| i == *id) {
                out.push((*id, *width));
            }
        }
        BvTerm::Const { .. } => {}
        BvTerm::Not { arg } | BvTerm::Neg { arg } => collect_bv_vars(arg, out),
        BvTerm::BinOp { lhs, rhs, .. } => {
            collect_bv_vars(lhs, out);
            collect_bv_vars(rhs, out);
        }
        BvTerm::Shift { arg, .. } => collect_bv_vars(arg, out),
        BvTerm::Concat { hi, lo } => {
            collect_bv_vars(hi, out);
            collect_bv_vars(lo, out);
        }
        BvTerm::Extract { arg, .. } => collect_bv_vars(arg, out),
    }
}

/// Build a small random bit-vector term over the given variables.
fn gen_bv_term(rng: &mut Lcg, vars: u32, width: u8, depth: u32) -> BvTerm {
    if depth == 0 || rng.below(4) == 0 {
        return BvTerm::var(rng.below(vars), width).expect("width 1..=64");
    }
    let mask = crate_mask(width);
    match rng.below(6) {
        0 => {
            let inner = gen_bv_term(rng, vars, width, depth - 1);
            BvTerm::not(inner).expect("well-formed")
        }
        1 => {
            let k = rng.next() & mask;
            BvTerm::constant(width, k).expect("well-formed")
        }
        2 | 3 => {
            let op = match rng.below(5) {
                0 => BvBinOp::And,
                1 => BvBinOp::Or,
                2 => BvBinOp::Xor,
                3 => BvBinOp::Add,
                _ => BvBinOp::Sub,
            };
            let l = gen_bv_term(rng, vars, width, depth - 1);
            let r = gen_bv_term(rng, vars, width, depth - 1);
            match op {
                BvBinOp::And => BvTerm::and(l, r),
                BvBinOp::Or => BvTerm::or(l, r),
                BvBinOp::Xor => BvTerm::xor(l, r),
                BvBinOp::Add => BvTerm::add(l, r),
                BvBinOp::Sub => BvTerm::sub(l, r),
            }
            .expect("same-width operands")
        }
        4 => {
            let inner = gen_bv_term(rng, vars, width, depth - 1);
            let amt = rng.below((width as u32) + 1) as u8;
            if rng.below(2) == 0 {
                BvTerm::shl(inner, amt).expect("well-formed")
            } else {
                BvTerm::lshr(inner, amt).expect("well-formed")
            }
        }
        _ => {
            // Extract from a double-width concatenation, zero-padded back to
            // the full width so the result stays usable as an operand.
            let hi = gen_bv_term(rng, vars, width, depth - 1);
            let lo = gen_bv_term(rng, vars, width, depth - 1);
            let cat = BvTerm::concat(hi, lo).expect("2*w <= 64 for w <= 32");
            let hi_i = rng.below(width as u32) as u8;
            let lo_i = rng.below(hi_i as u32 + 1) as u8;
            let slice = BvTerm::extract(cat, hi_i, lo_i).expect("in-range extract");
            let hw = hi_i - lo_i + 1;
            if hw >= width {
                slice
            } else {
                // Zero-extend back to `width`.
                let pad = BvTerm::constant(width - hw, 0).expect("pad width 1..=64");
                BvTerm::concat(pad, slice).expect("padded width == original")
            }
        }
    }
}

fn crate_mask(w: u8) -> u64 {
    if w >= 64 {
        u64::MAX
    } else {
        (1u64 << w) - 1
    }
}

/// Differential testing of the QF_BV path against Z3. No-op without `z3`.
#[test]
fn differential_bv_vs_z3_when_available() {
    if !z3_present() {
        eprintln!("z3 not found on PATH; skipping Z3 BV differential test");
        return;
    }

    let mut rng = Lcg(0x5eed_bee5);
    for case in 0..40u32 {
        let width = 1 + rng.below(3) as u8;
        let vars = 1 + rng.below(2);
        let t1 = gen_bv_term(&mut rng, vars, width, 2);
        let t2 = gen_bv_term(&mut rng, vars, width, 2);

        let mut decls: Vec<(u32, u8)> = Vec::new();
        collect_bv_vars(&t1, &mut decls);
        collect_bv_vars(&t2, &mut decls);

        let assertion = if rng.below(2) == 0 {
            BvAssertion::Eq(t1.clone(), t2.clone())
        } else {
            BvAssertion::Ult(t1.clone(), t2.clone())
        };

        let mut smt2 = String::from("(set-logic QF_BV)\n");
        for &(id, w) in &decls {
            smt2.push_str(&format!(
                "(declare-fun x{}w{} () (_ BitVec {}))\n",
                id, w, w
            ));
        }
        smt2.push_str(&bv_assertion_to_smt2(&assertion));
        smt2.push_str("(check-sat)\n");

        let z3_claim = match run_z3(&smt2) {
            Some(c) => c,
            None => continue,
        };
        let assertions = [assertion];
        let (claim, verdict) = solve_and_check_bv(vars, &assertions, 10_000_000);
        assert_eq!(
            claim, z3_claim,
            "disagreement with Z3 on BV problem (case {}):\n{}",
            case, smt2
        );
        assert!(
            verdict.is_accept(),
            "checker did not Accept the BV verdict vs Z3: {:?}",
            verdict
        );
    }
}

fn bv_assertion_to_smt2(a: &BvAssertion) -> String {
    let (l, r, op) = match a {
        BvAssertion::Eq(l, r) => (l, r, "="),
        BvAssertion::Ult(l, r) => (l, r, "bvult"),
    };
    format!(
        "(assert ({} {} {}))\n",
        op,
        bv_term_to_smt2(l),
        bv_term_to_smt2(r)
    )
}

/// Offline guard for the Z3 serialization: the emitted QF_BV scripts must be
/// accepted by our *own* SMT-LIB2 parser/lowering, and solving the round-tripped
/// problem must agree with solving the original assertions.
#[test]
fn bv_z3_serialization_roundtrips_through_own_parser() {
    let mut rng = Lcg(0xfeed_face);
    for case in 0..25u32 {
        let width = 1 + rng.below(3) as u8;
        let vars = 1 + rng.below(2);
        let t1 = gen_bv_term(&mut rng, vars, width, 2);
        let t2 = gen_bv_term(&mut rng, vars, width, 2);

        let mut decls: Vec<(u32, u8)> = Vec::new();
        collect_bv_vars(&t1, &mut decls);
        collect_bv_vars(&t2, &mut decls);

        let assertion = if rng.below(2) == 0 {
            BvAssertion::Eq(t1.clone(), t2.clone())
        } else {
            BvAssertion::Ult(t1.clone(), t2.clone())
        };

        let mut smt2 = String::from("(set-logic QF_BV)\n");
        for &(id, w) in &decls {
            smt2.push_str(&format!(
                "(declare-fun x{}w{} () (_ BitVec {}))\n",
                id, w, w
            ));
        }
        smt2.push_str(&bv_assertion_to_smt2(&assertion));
        smt2.push_str("(check-sat)\n");

        let script = crate::parsers::smtlib2::parse_script(&smt2)
            .unwrap_or_else(|e| panic!("case {}: own parser rejected its own script: {}", case, e));
        let prob = script.to_bv().unwrap_or_else(|e| {
            panic!("case {}: own lowering rejected its own script: {}", case, e)
        });
        // Only *occurring* variables are declared, so the round-tripped count
        // matches the declaration list, not necessarily the full var space.
        assert_eq!(prob.var_count, decls.len() as u32);

        let assertions = [assertion];
        let (direct, dv) = solve_and_check_bv(vars, &assertions, 10_000_000);
        let (rt, _rv) = solve_and_check_bv(prob.var_count, &prob.assertions, 10_000_000);
        assert_eq!(direct, rt, "round-trip changed the verdict (case {})", case);
        if direct == SolveResult::Unknown {
            // The engine is complete on this fragment: an Unknown here is a
            // bug worth capturing verbatim for debugging.
            panic!(
                "case {}: engine gave up\ndirect verdict={:?}\n{}",
                case, dv, smt2
            );
        }
        assert!(
            dv.is_accept(),
            "case {}: checker did not Accept the direct verdict\n{:?}",
            case,
            smt2
        );
    }
}

// ---------------------------------------------------------------------------
// Array differential lane (QF_AX)
// ---------------------------------------------------------------------------

/// Serialize an element term (`e{id}` element vars, `a{id}` array vars).
fn ax_elem_to_smt2(e: &ElemExpr) -> String {
    match e {
        ElemExpr::Var(id) => format!("e{}", id),
        ElemExpr::Const(v) => v.to_string(),
        ElemExpr::Select(arr, idx) => {
            format!("(select {} {})", ax_arr_to_smt2(arr), ax_elem_to_smt2(idx))
        }
    }
}

fn ax_arr_to_smt2(a: &ArrayExpr) -> String {
    match a {
        ArrayExpr::AVar(id) => format!("a{}", id),
        ArrayExpr::ConstArray(v) => {
            format!("((as const (Array Int Int)) {})", ax_elem_to_smt2(v))
        }
        ArrayExpr::Store(base, idx, val) => format!(
            "(store {} {} {})",
            ax_arr_to_smt2(base),
            ax_elem_to_smt2(idx),
            ax_elem_to_smt2(val)
        ),
    }
}

/// Build a small random element expression over `navars` arrays and `nevars`
/// element variables with values/indices in `{0,1,2}`.
fn gen_ax_elem(rng: &mut Lcg, navars: u32, nevars: u32, depth: u32) -> ElemExpr {
    if depth == 0 || rng.below(3) == 0 {
        return match rng.below(2) {
            0 => ElemExpr::Const(rng.below(3) as u64),
            _ => ElemExpr::Var(rng.below(nevars)),
        };
    }
    let arr = gen_ax_arr(rng, navars, nevars, depth - 1);
    let idx = gen_ax_elem(rng, navars, nevars, depth - 1);
    ElemExpr::select(arr, idx)
}

fn gen_ax_arr(rng: &mut Lcg, navars: u32, nevars: u32, depth: u32) -> ArrayExpr {
    if depth == 0 || rng.below(3) == 0 {
        return ArrayExpr::AVar(rng.below(navars));
    }
    let base = gen_ax_arr(rng, navars, nevars, depth - 1);
    let idx = gen_ax_elem(rng, navars, nevars, depth - 1);
    let val = gen_ax_elem(rng, navars, nevars, depth - 1);
    ArrayExpr::store(base, idx, val)
}

/// Differential testing of the QF_AX path against Z3. No-op without `z3`.
#[test]
fn differential_array_vs_z3_when_available() {
    if !z3_present() {
        eprintln!("z3 not found on PATH; skipping Z3 array differential test");
        return;
    }

    let mut rng = Lcg(0x0a11_ace5);
    for case in 0..40u32 {
        let navars = 1 + rng.below(2);
        let nevars = 1 + rng.below(2);

        // Two random element equalities plus one array equality per instance.
        let el = gen_ax_elem(&mut rng, navars, nevars, 2);
        let er = gen_ax_elem(&mut rng, navars, nevars, 2);
        let al = gen_ax_arr(&mut rng, navars, nevars, 2);
        let ar = gen_ax_arr(&mut rng, navars, nevars, 2);
        let assertions = vec![
            ArrAssertion::ElemsEqual(el.clone(), er.clone()),
            ArrAssertion::ArraysEqual(al.clone(), ar.clone()),
        ];

        let mut smt2 = String::from("(set-logic QF_AX)\n");
        for i in 0..nevars {
            smt2.push_str(&format!("(declare-fun e{} () Int)\n", i));
        }
        for i in 0..navars {
            smt2.push_str(&format!("(declare-fun a{} () (Array Int Int))\n", i));
        }
        for a in &assertions {
            match a {
                ArrAssertion::ElemsEqual(l, r) => {
                    smt2.push_str(&format!(
                        "(assert (= {} {}))\n",
                        ax_elem_to_smt2(l),
                        ax_elem_to_smt2(r)
                    ));
                }
                ArrAssertion::ArraysEqual(l, r) => {
                    smt2.push_str(&format!(
                        "(assert (= {} {}))\n",
                        ax_arr_to_smt2(l),
                        ax_arr_to_smt2(r)
                    ));
                }
            }
        }
        smt2.push_str("(check-sat)\n");

        let z3_claim = match run_z3(&smt2) {
            Some(c) => c,
            None => continue,
        };
        let (claim, verdict) = solve_and_check_arrays(navars, nevars, &assertions, 200_000);
        assert_eq!(
            claim, z3_claim,
            "disagreement with Z3 on AX problem (case {}):\n{}",
            case, smt2
        );
        if claim != SolveResult::Unknown {
            assert!(
                verdict.is_accept(),
                "checker did not Accept the AX verdict vs Z3: {:?}",
                verdict
            );
        }
    }
}

/// Offline guard for the QF_AX serialization: emitted scripts must round-trip
/// through our own parser/lowering with identical verdicts.
#[test]
fn ax_z3_serialization_roundtrips_through_own_parser() {
    let mut rng = Lcg(0xdec0_ded0);
    for case in 0..25u32 {
        let navars = 1 + rng.below(2);
        let nevars = 1 + rng.below(2);

        let el = gen_ax_elem(&mut rng, navars, nevars, 2);
        let er = gen_ax_elem(&mut rng, navars, nevars, 2);
        let al = gen_ax_arr(&mut rng, navars, nevars, 2);
        let ar = gen_ax_arr(&mut rng, navars, nevars, 2);
        let assertions = vec![
            ArrAssertion::ElemsEqual(el.clone(), er.clone()),
            ArrAssertion::ArraysEqual(al.clone(), ar.clone()),
        ];

        let mut smt2 = String::from("(set-logic QF_AX)\n");
        for i in 0..nevars {
            smt2.push_str(&format!("(declare-fun e{} () Int)\n", i));
        }
        for i in 0..navars {
            smt2.push_str(&format!("(declare-fun a{} () (Array Int Int))\n", i));
        }
        for a in &assertions {
            match a {
                ArrAssertion::ElemsEqual(l, r) => {
                    smt2.push_str(&format!(
                        "(assert (= {} {}))\n",
                        ax_elem_to_smt2(l),
                        ax_elem_to_smt2(r)
                    ));
                }
                ArrAssertion::ArraysEqual(l, r) => {
                    smt2.push_str(&format!(
                        "(assert (= {} {}))\n",
                        ax_arr_to_smt2(l),
                        ax_arr_to_smt2(r)
                    ));
                }
            }
        }
        smt2.push_str("(check-sat)\n");

        let script = crate::parsers::smtlib2::parse_script(&smt2)
            .unwrap_or_else(|e| panic!("case {}: own parser rejected its own script: {}", case, e));
        let prob = script.to_array().unwrap_or_else(|e| {
            panic!("case {}: own lowering rejected its own script: {}", case, e)
        });
        assert_eq!(prob.avars.len() as u32, navars);
        assert_eq!(prob.evars.len() as u32, nevars);

        let (direct, dv) = solve_and_check_arrays(navars, nevars, &assertions, 200_000);
        let (rt, rv) = solve_and_check_arrays(
            prob.avars.len() as u32,
            prob.evars.len() as u32,
            &prob.assertions,
            200_000,
        );
        assert_eq!(direct, rt, "round-trip changed the verdict (case {})", case);
        // The engine may honestly return Unknown on hard random instances;
        // any decided answer must be kernel-Accepted.
        if direct != SolveResult::Unknown {
            assert!(dv.is_accept());
            assert!(rv.is_accept(), "round-tripped model was not accepted");
        }
    }
}
