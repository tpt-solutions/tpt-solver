//! LRA (linear real arithmetic) certificate checking — the trusted kernel's LRA half.
//!
//! * **UNSAT** — verify a [`FarkasCertificate`]: the weighted sum of the original
//!   constraints (with the certificate's nonnegative multipliers) must reduce to a
//!   direct contradiction (`0 <= negative`). This is pure linear arithmetic: a dot
//!   product and a sign check, exactly the bounded linear-arithmetic claim
//!   `tpt-telos` is suited to express.
//! * **SAT** — substitute a returned model into the original constraints and check
//!   satisfaction (catches wrong-SAT-answer bugs at near-zero cost).

use crate::outcome::Outcome;
use alloc::vec::Vec;
use core::cmp::Ordering;
use tpt_solver_core::lra::{FarkasCertificate, LinConstraint};
use tpt_solver_core::rational::Rational;

/// Verify a Farkas certificate against the original constraints.
///
/// Let `S = Σ mᵢ·rhsᵢ` and `R` be `<` if some strict constraint has `mᵢ > 0`, else
/// `<=`. The combination derives `0 R S`. This is a contradiction exactly when the
/// coefficients cancel and `0 R S` is false: `S < 0` for `<=`, or `S <= 0` for `<`.
///
/// Returns [`Outcome::Accept`] iff every multiplier is nonnegative, the coefficients
/// cancel, and that contradiction holds. Returns [`Outcome::Reject`] if the
/// combination fails to derive one, and [`Outcome::Inconclusive`] on malformed input
/// or exact-arithmetic overflow.
#[allow(clippy::needless_range_loop)]
pub fn check_farkas(constraints: &[LinConstraint], cert: &FarkasCertificate) -> Outcome {
    if cert.multipliers.len() != constraints.len() {
        return Outcome::Inconclusive;
    }
    let n_vars = constraints.first().map(|c| c.coeffs.len()).unwrap_or(0);
    let mut total_rhs = Rational::zero();
    let mut total_coeffs: Vec<Rational> = alloc::vec![Rational::zero(); n_vars];
    let mut strict_used = false;

    for (i, c) in constraints.iter().enumerate() {
        let m = cert.multipliers[i];
        if m.is_negative() {
            return Outcome::Reject; // Farkas multipliers must be nonnegative
        }
        if c.strict && !m.is_zero() {
            strict_used = true;
        }
        if c.coeffs.len() != n_vars {
            return Outcome::Inconclusive;
        }
        for j in 0..n_vars {
            let term = match c.coeffs[j].mul(m) {
                Some(t) => t,
                None => return Outcome::Inconclusive,
            };
            total_coeffs[j] = match total_coeffs[j].add(term) {
                Some(t) => t,
                None => return Outcome::Inconclusive,
            };
        }
        total_rhs = match total_rhs.add(match c.rhs.mul(m) {
            Some(t) => t,
            None => return Outcome::Inconclusive,
        }) {
            Some(t) => t,
            None => return Outcome::Inconclusive,
        };
    }

    for tc in &total_coeffs {
        if !tc.is_zero() {
            return Outcome::Reject;
        }
    }
    let contradiction = if strict_used {
        !total_rhs.is_positive()
    } else {
        total_rhs.is_negative()
    };
    if contradiction {
        Outcome::Accept
    } else {
        Outcome::Reject
    }
}

/// Verify that `model` satisfies every constraint (`coeffs·model <= rhs`, or
/// `< rhs` for a strict constraint).
///
/// Returns [`Outcome::Accept`] if all hold, [`Outcome::Reject`] if any is violated,
/// and [`Outcome::Inconclusive`] on a length mismatch or arithmetic overflow.
pub fn check_lra_model(constraints: &[LinConstraint], model: &[Rational]) -> Outcome {
    for c in constraints {
        // A model shorter than this constraint's variable count is malformed
        // relative to it — treat it the same as any other malformed input
        // (`Inconclusive`), rather than silently defaulting the missing
        // coordinates to zero, which could mask a real constraint violation.
        if model.len() < c.coeffs.len() {
            return Outcome::Inconclusive;
        }
        let mut lhs = Rational::zero();
        for (j, coeff) in c.coeffs.iter().enumerate() {
            let val = model[j];
            let term = match coeff.mul(val) {
                Some(t) => t,
                None => return Outcome::Inconclusive,
            };
            lhs = match lhs.add(term) {
                Some(t) => t,
                None => return Outcome::Inconclusive,
            };
        }
        let violated = match lhs.cmp(c.rhs) {
            Ordering::Greater => true,
            Ordering::Equal => c.strict,
            Ordering::Less => false,
        };
        if violated {
            return Outcome::Reject;
        }
    }
    Outcome::Accept
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use alloc::vec;
    use tpt_solver_core::lra::LinConstraint;
    use tpt_solver_core::rational::Rational;

    fn c(coeffs: &[i64], rhs: i64) -> LinConstraint {
        LinConstraint {
            strict: false,
            coeffs: coeffs.iter().map(|&x| Rational::from_i64(x)).collect(),
            rhs: Rational::from_i64(rhs),
        }
    }

    #[test]
    fn accepts_valid_farkas() {
        // x >= 1 (-x <= -1), x <= 0 ; certificate [1, 1] => 0 <= -1
        let cons = vec![c(&[-1], -1), c(&[1], 0)];
        let cert = FarkasCertificate {
            multipliers: vec![Rational::from_i64(1), Rational::from_i64(1)],
        };
        assert!(check_farkas(&cons, &cert).is_accept());
    }

    #[test]
    fn rejects_bogus_farkas() {
        let cons = vec![c(&[-1], -1), c(&[1], 0)];
        let cert = FarkasCertificate {
            multipliers: vec![Rational::from_i64(1), Rational::from_i64(0)],
        };
        // 1*(-x<=-1) + 0*(x<=0) => -x <= -1, not a contradiction => Reject.
        assert!(check_farkas(&cons, &cert).is_reject());
    }

    #[test]
    fn model_check_passes() {
        // x <= 5, x >= 0 ; model x = 3
        let cons = vec![c(&[1], 5), c(&[-1], 0)];
        let model = vec![Rational::from_i64(3)];
        assert!(check_lra_model(&cons, &model).is_accept());
    }

    #[test]
    fn model_check_inconclusive_on_short_model() {
        // Constraint over 2 variables, model only supplies 1 — malformed relative
        // to this constraint, must not silently treat the missing one as zero.
        let cons = vec![c(&[1, 1], 5)];
        let model = vec![Rational::from_i64(3)];
        assert!(check_lra_model(&cons, &model).is_inconclusive());
    }

    fn strict(coeffs: &[i64], rhs: i64) -> LinConstraint {
        LinConstraint {
            strict: true,
            ..c(coeffs, rhs)
        }
    }

    #[test]
    fn strict_bound_refuted_by_farkas_at_equal_boundary() {
        // x >= 1 and x < 1: certificate [1, 1] gives 0 < 0, a contradiction.
        let cons = vec![c(&[-1], -1), strict(&[1], 1)];
        let cert = FarkasCertificate {
            multipliers: vec![Rational::from_i64(1), Rational::from_i64(1)],
        };
        assert!(check_farkas(&cons, &cert).is_accept());
    }

    #[test]
    fn strict_certificate_without_strict_multiplier_is_not_a_contradiction() {
        // x >= 1 and x <= 1 is satisfiable (x = 1). Zero multiplier on the strict
        // constraint must not turn 0 <= 0 into a contradiction.
        let cons = vec![c(&[-1], -1), strict(&[1], 1)];
        let cert = FarkasCertificate {
            multipliers: vec![Rational::from_i64(1), Rational::from_i64(0)],
        };
        assert!(check_farkas(&cons, &cert).is_reject());
    }

    #[test]
    fn model_at_strict_boundary_is_rejected() {
        // x < 1 with x = 1 violates the strict constraint.
        let cons = vec![strict(&[1], 1)];
        assert!(check_lra_model(&cons, &[Rational::from_i64(1)]).is_reject());
        assert!(check_lra_model(&cons, &[Rational::from_i64(0)]).is_accept());
    }

    #[test]
    fn model_check_fails() {
        let cons = vec![c(&[1], 5)];
        let model = vec![Rational::from_i64(9)];
        assert!(check_lra_model(&cons, &model).is_reject());
    }
}
