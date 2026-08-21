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
use crate::reference::{solve_and_check, solve_and_check_cdcl, Problem};
use std::process::Command;
use tpt_solver_check::outcome::Outcome;
use tpt_solver_core::engine::SolveResult;

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

/// Differential testing against Z3 (spec §5.4). Runs only when the `z3` binary is on
/// `PATH`; otherwise it is a no-op so the suite stays green where Z3 is absent (e.g.
/// local machines). CI installs Z3 to exercise this lane for real.
#[test]
fn differential_vs_z3_when_available() {
    let z3_present = match Command::new("z3").arg("-version").output() {
        Ok(o) if o.status.success() => true,
        _ => false,
    };
    if !z3_present {
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
            });
        let output = match output {
            Ok(o) => o,
            Err(_) => continue,
        };
        let stdout = String::from_utf8_lossy(&output.stdout);
        let z3_claim = match stdout.lines().find_map(|l| {
            let t = l.trim();
            if t == "sat" {
                Some(SolveResult::Sat)
            } else if t == "unsat" {
                Some(SolveResult::Unsat)
            } else {
                None
            }
        }) {
            Some(c) => c,
            None => continue, // z3 said "unknown" or produced no clear verdict
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
