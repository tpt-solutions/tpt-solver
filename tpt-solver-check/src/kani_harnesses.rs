//! Kani proof harnesses for the checker kernel. Run with `cargo kani -p tpt-solver-check`.
//!
//! Each harness states a guarantee the kernel must keep, checked over a symbolic
//! input family. The kernel is the only code whose verdicts the design trusts, so its
//! guarantees are the ones worth proving.

use crate::lra::check_farkas;
use crate::lrat::{check_proof, LratProof, LratStep};
use crate::sat::{check_model, Cnf, Model};
use tpt_solver_core::ir::{Lit, VarId};
use tpt_solver_core::lra::{FarkasCertificate, LinConstraint};
use tpt_solver_core::rational::Rational;

/// Acceptance of a SAT model implies every clause is satisfied by it. The formula is
/// the single unit clause `(x)` or `(not x)`, and the model assigns `x` either way.
#[kani::proof]
fn kani_model_accept_implies_clause_satisfied() {
    let pol: bool = kani::any();
    let model_val: bool = kani::any();
    let v = VarId::new(1).unwrap();
    let cnf = Cnf::new(vec![vec![Lit::new(v, pol)]]);
    let model = Model::from_lits(vec![Lit::new(v, model_val)]);
    if check_model(&cnf, &model, 1).is_accept() {
        assert!(pol == model_val);
    }
}

/// A satisfiable formula is never refuted: the empty clause is not derivable by unit
/// propagation from the single clause `(x)`, whatever its polarity.
#[kani::proof]
fn kani_satisfiable_formula_never_proved_unsat() {
    let pol: bool = kani::any();
    let v = VarId::new(1).unwrap();
    let cnf = [vec![Lit::new(v, pol)]];
    let proof = LratProof::new(vec![LratStep {
        clause: Vec::new(),
        hints: Vec::new(),
    }]);
    assert!(!check_proof(&cnf, &proof, 1).is_accept());
}

/// A zero multiplier combines the constraints into `0 <= 0`, which proves nothing, so
/// the infeasible constraint `0 <= -1` is never certified by it.
#[kani::proof]
fn kani_zero_farkas_multiplier_never_certifies() {
    let constraint = LinConstraint {
        coeffs: vec![Rational::zero()],
        rhs: Rational::from_i64(-1),
    };
    let cert = FarkasCertificate {
        multipliers: vec![Rational::zero()],
    };
    assert!(!check_farkas(&[constraint], &cert).is_accept());
}
