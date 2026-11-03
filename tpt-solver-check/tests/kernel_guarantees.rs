//! Kernel guarantees checked exhaustively over small input families. These mirror the
//! Kani harnesses in `src/kani_harnesses.rs` and run on every platform, including
//! those where Kani is not available.
use tpt_solver_check::lra::check_farkas;
use tpt_solver_check::lrat::{check_proof, LratProof, LratStep};
use tpt_solver_check::sat::{check_model, Cnf, Model};
use tpt_solver_core::ir::{Lit, VarId};
use tpt_solver_core::lra::{FarkasCertificate, LinConstraint};
use tpt_solver_core::rational::Rational;

#[test]
fn model_accept_implies_clause_satisfied() {
    for pol in [false, true] {
        for model_val in [false, true] {
            let v = VarId::new(1).unwrap();
            let cnf = Cnf::new(vec![vec![Lit::new(v, pol)]]);
            let model = Model::from_lits(vec![Lit::new(v, model_val)]);
            if check_model(&cnf, &model, 1).is_accept() {
                assert!(pol == model_val);
            }
        }
    }
}

#[test]
fn satisfiable_formula_never_proved_unsat() {
    for pol in [false, true] {
        let v = VarId::new(1).unwrap();
        let cnf = [vec![Lit::new(v, pol)]];
        let proof = LratProof::new(vec![LratStep {
            clause: Vec::new(),
            hints: Vec::new(),
        }]);
        assert!(!check_proof(&cnf, &proof, 1).is_accept());
    }
}

#[test]
fn zero_farkas_multiplier_never_certifies() {
    let c = LinConstraint {
        coeffs: vec![Rational::zero()],
        rhs: Rational::from_i64(-1),
    };
    let cert = FarkasCertificate {
        multipliers: vec![Rational::zero()],
    };
    assert!(!check_farkas(&[c], &cert).is_accept());
}
