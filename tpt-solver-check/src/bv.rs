//! Bit-vector answer checking — the trusted kernel's QF_BV half.
//!
//! * **SAT** — substitute the claimed word model into the original assertions
//!   and evaluate them with this file's own evaluator (deliberately written
//!   separately from the engine's; a shared bug would defeat the whole
//!   certificate architecture). A too-short model is `Inconclusive`, not
//!   silently zero-padded.
//! * **UNSAT** — re-validate the CDCL proof against the bit-blasted CNF that
//!   shipped with the claim ([`BvUnsatCert`]) via the LRAT checker. The blast
//!   itself is covered by differential brute-force property tests in the
//!   engine (documented there); this is the one theory where part of the
//!   encoding trust rests on testing rather than on-the-spot re-derivation.

use crate::lrat::{check_proof, LratProof, LratStep};
use crate::outcome::Outcome;
use alloc::vec::Vec;
use tpt_solver_core::bv::{BvAssertion, BvBinOp, BvFormula, BvModel, BvTerm, BvUnsatCert};

/// Maximum accepted term depth; deeper inputs are [`Outcome::Inconclusive`].
const MAX_DEPTH: u32 = 2048;

fn mask(w: u8) -> u128 {
    if w >= 128 {
        u128::MAX
    } else if w == 0 {
        0
    } else {
        (1u128 << w) - 1
    }
}

/// Independent evaluation of a term under `env` (`env[id]` = value).
fn eval(term: &BvTerm, env: &[u128], d: u32) -> Option<u128> {
    if d > MAX_DEPTH {
        return None;
    }
    match term {
        BvTerm::Var { id, .. } => env.get(*id as usize).copied(),
        BvTerm::Const { value, .. } => Some(*value),
        BvTerm::Not { arg } => Some((!eval(arg, env, d + 1)?) & mask(arg.width())),
        BvTerm::Neg { arg } => Some(eval(arg, env, d + 1)?.wrapping_neg() & mask(arg.width())),
        BvTerm::BinOp { op, lhs, rhs } => {
            let (l, r) = (eval(lhs, env, d + 1)?, eval(rhs, env, d + 1)?);
            let w = lhs.width();
            match op {
                BvBinOp::And => Some(l & r),
                BvBinOp::Or => Some(l | r),
                BvBinOp::Xor => Some(l ^ r),
                BvBinOp::Add => Some(l.wrapping_add(r) & mask(w)),
                BvBinOp::Sub => Some(l.wrapping_sub(r) & mask(w)),
            }
        }
        BvTerm::Shift { left, arg, amount } => {
            let w = arg.width();
            let amt = *amount as u32;
            let a = eval(arg, env, d + 1)?;
            if amt >= w as u32 {
                Some(0)
            } else if *left {
                Some((a << amt) & mask(w))
            } else {
                Some(a >> amt)
            }
        }
        BvTerm::Concat { hi, lo } => {
            let (h, l) = (eval(hi, env, d + 1)?, eval(lo, env, d + 1)?);
            Some((h << lo.width()) | l)
        }
        BvTerm::Extract { arg, hi, lo } => {
            let a = eval(arg, env, d + 1)?;
            if *hi >= arg.width() || *lo > *hi {
                None
            } else {
                Some((a >> *lo) & mask(*hi - *lo + 1))
            }
        }
    }
}

/// Does one assertion hold under the model? `None` on malformed input or an
/// out-of-range variable id.
fn holds(a: &BvAssertion, values: &[u128]) -> Option<bool> {
    match a {
        BvAssertion::Eq(l, r) => Some(eval(l, values, 0)? == eval(r, values, 0)?),
        BvAssertion::Ult(l, r) => Some(eval(l, values, 0)? < eval(r, values, 0)?),
    }
}

/// Whether a Boolean formula holds under the model. Written separately from
/// the engine's copy, for the same reason as [`holds`].
fn formula_holds(f: &BvFormula, values: &[u128]) -> Option<bool> {
    Some(match f {
        BvFormula::Const(b) => *b,
        BvFormula::Atom(a) => holds(a, values)?,
        BvFormula::Not(inner) => !formula_holds(inner, values)?,
        BvFormula::And(parts) => {
            let mut all = true;
            for part in parts {
                all &= formula_holds(part, values)?;
            }
            all
        }
        BvFormula::Or(parts) => {
            let mut any = false;
            for part in parts {
                any |= formula_holds(part, values)?;
            }
            any
        }
    })
}

/// Verify a claimed SAT model against a conjunction of Boolean formulas. The
/// verdicts are those of [`check_bv_model`].
pub fn check_bv_formula_model(formulas: &[BvFormula], model: &BvModel, var_count: u32) -> Outcome {
    if model.values.len() < var_count as usize {
        return Outcome::Inconclusive;
    }
    for f in formulas {
        match formula_holds(f, &model.values) {
            Some(true) => {}
            Some(false) => return Outcome::Reject,
            None => return Outcome::Inconclusive,
        }
    }
    Outcome::Accept
}

/// Verify a claimed SAT model by substituting it into the original assertions.
///
/// [`Outcome::Accept`] iff every assertion evaluates satisfied;
/// [`Outcome::Reject`] if any is violated under a well-formed model;
/// [`Outcome::Inconclusive`] for malformed terms or a model shorter than
/// `var_count` (missing coordinates are never silently zero-filled).
pub fn check_bv_model(assertions: &[BvAssertion], model: &BvModel, var_count: u32) -> Outcome {
    if model.values.len() < var_count as usize {
        return Outcome::Inconclusive;
    }
    for a in assertions {
        match holds(a, &model.values) {
            Some(true) => {}
            Some(false) => return Outcome::Reject,
            None => return Outcome::Inconclusive,
        }
    }
    Outcome::Accept
}

/// Verify an UNSAT claim: re-run RUP validation of the shipped proof over the
/// shipped blast.
pub fn check_bv_unsat(cert: &BvUnsatCert) -> Outcome {
    fn lit_of(l: i32) -> Option<tpt_solver_core::ir::Lit<()>> {
        let v = tpt_solver_core::ir::VarId::new(l.unsigned_abs())?;
        Some(tpt_solver_core::ir::Lit::new(v, l > 0))
    }
    let mut cnf: Vec<Vec<tpt_solver_core::ir::Lit<()>>> = Vec::with_capacity(cert.clauses.len());
    for c in &cert.clauses {
        let mut row: Vec<tpt_solver_core::ir::Lit<()>> = Vec::with_capacity(c.len());
        for &l in c {
            match lit_of(l) {
                Some(lit) => row.push(lit),
                None => return Outcome::Inconclusive,
            }
        }
        cnf.push(row);
    }
    let mut steps: Vec<LratStep> = Vec::with_capacity(cert.proof.len());
    for c in &cert.proof {
        let mut row: Vec<tpt_solver_core::ir::Lit<()>> = Vec::with_capacity(c.len());
        for &l in c {
            match lit_of(l) {
                Some(lit) => row.push(lit),
                None => return Outcome::Inconclusive,
            }
        }
        steps.push(LratStep {
            clause: row,
            hints: Vec::new(),
        });
    }
    check_proof(&cnf, &LratProof::new(steps), cert.var_count)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
mod tests {
    use super::*;
    use alloc::vec;

    fn v(id: u32, w: u8) -> BvTerm {
        BvTerm::var(id, w).unwrap()
    }
    fn k(w: u8, val: u128) -> BvTerm {
        BvTerm::constant(w, val).unwrap()
    }

    #[test]
    fn accepts_satisfied_model() {
        // x + 1 == 0 at width 4 with x = 15.
        let t = BvTerm::add(v(0, 4), k(4, 1)).unwrap();
        let asserts = [BvAssertion::Eq(t, k(4, 0))];
        let model = BvModel { values: vec![15] };
        assert!(check_bv_model(&asserts, &model, 1).is_accept());
    }

    #[test]
    fn rejects_violated_assertion() {
        let asserts = [BvAssertion::Ult(v(0, 8), k(8, 3))];
        let model = BvModel { values: vec![5] };
        assert!(check_bv_model(&asserts, &model, 1).is_reject());
    }

    #[test]
    fn short_model_is_inconclusive_not_zero_padded() {
        // Two declared variables, model supplies only one coordinate.
        let asserts = [BvAssertion::Eq(v(0, 4), v(1, 4))];
        let model = BvModel { values: vec![3] };
        assert!(check_bv_model(&asserts, &model, 2).is_inconclusive());
    }

    #[test]
    fn unsat_cert_roundtrip_with_engine() {
        // Engine claims UNSAT for x ^ ~x == 0; kernel must accept its proof.
        use tpt_solver_core::bv::{solve_bv, BvOutcome};
        let x = v(0, 4);
        let taut = BvTerm::xor(x.clone(), BvTerm::not(x).unwrap()).unwrap();
        let asserts = [BvAssertion::Eq(taut, k(4, 0))];
        match solve_bv(1, &asserts, 1_000_000) {
            Some(BvOutcome::Unsat(cert)) => {
                assert!(check_bv_unsat(&cert).is_accept());
            }
            _ => panic!("expected Unsat from engine"),
        }
    }

    #[test]
    fn bogus_proof_is_rejected() {
        // An empty clause "proof" over a satisfiable blast must be rejected.
        let cert = BvUnsatCert {
            var_count: 2,
            clauses: vec![vec![-1]],
            proof: vec![vec![]],
        };
        assert!(check_bv_unsat(&cert).is_reject());
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
mod formula_kernel_tests {
    use super::*;
    use alloc::{boxed::Box, vec};
    use tpt_solver_core::bv::{solve_bv_formulas, BvOutcome};

    fn x() -> BvTerm {
        BvTerm::var(0, 2).unwrap()
    }

    fn c(value: u128) -> BvTerm {
        BvTerm::constant(2, value).unwrap()
    }

    fn eq(value: u128) -> BvFormula {
        BvFormula::Atom(BvAssertion::eq(x(), c(value)).unwrap())
    }

    #[test]
    fn unsat_formula_certificate_is_accepted() {
        // x is 0 or 1, not 0, not 1.
        let formulas = vec![
            BvFormula::Or(vec![eq(0), eq(1)]),
            BvFormula::Not(Box::new(eq(0))),
            BvFormula::Not(Box::new(eq(1))),
        ];
        match solve_bv_formulas(1, &formulas, 10_000_000) {
            Some(BvOutcome::Unsat(cert)) => assert_eq!(check_bv_unsat(&cert), Outcome::Accept),
            other => panic!("expected UNSAT, got {other:?}"),
        }
    }

    #[test]
    fn sat_formula_model_is_accepted_and_a_wrong_model_is_rejected() {
        let formulas = vec![BvFormula::Or(vec![eq(3), eq(0)])];
        match solve_bv_formulas(1, &formulas, 10_000_000) {
            Some(BvOutcome::Sat(model)) => {
                assert_eq!(
                    check_bv_formula_model(&formulas, &model, 1),
                    Outcome::Accept
                );
                let wrong = BvModel { values: vec![1] };
                assert_eq!(
                    check_bv_formula_model(&formulas, &wrong, 1),
                    Outcome::Reject
                );
            }
            other => panic!("expected SAT, got {other:?}"),
        }
    }
}
