//! LRA (linear real arithmetic) certificate checking — the trusted kernel's LRA half.
//!
//! * **UNSAT** — verify a [`FarkasCertificate`]: the weighted sum of the original
//!   constraints (with the certificate's nonnegative multipliers) must reduce to a
//!   direct contradiction (`0 <= negative`). This is pure linear arithmetic: a dot
//!   product and a sign check, exactly the bounded linear-arithmetic claim
//! `tpt-telos` is suited to express.
//! * **SAT** — substitute a returned model into the original constraints and check
//!   satisfaction (catches wrong-SAT-answer bugs at near-zero cost).

use crate::outcome::Outcome;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use tpt_solver_core::lra::{FarkasCertificate, LinConstraint};
use tpt_solver_core::rational::Rational;

/// Verify a Farkas certificate against the original constraints.
///
/// Returns [`Outcome::Accept`] iff every multiplier is nonnegative, the combined
/// constraint's coefficients are all zero, and the combined right-hand side is
/// strictly negative (i.e. `0 < 0`). Returns [`Outcome::Reject`] if the combination
/// fails to derive a contradiction, and [`Outcome::Inconclusive`] on malformed input
/// or exact-arithmetic overflow.
#[allow(clippy::needless_range_loop)]
pub fn check_farkas(constraints: &[LinConstraint], cert: &FarkasCertificate) -> Outcome {
    if cert.multipliers.len() != constraints.len() {
        return Outcome::Inconclusive;
    }
    let n_vars = constraints.first().map(|c| c.coeffs.len()).unwrap_or(0);
    let mut total_rhs = Rational::zero();
    let mut total_coeffs: Vec<Rational> = alloc::vec![Rational::zero(); n_vars];

    for (i, c) in constraints.iter().enumerate() {
        let m = cert.multipliers[i];
        if m.is_negative() {
            return Outcome::Reject; // Farkas multipliers must be nonnegative
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
    if total_rhs.is_negative() {
        Outcome::Accept
    } else {
        Outcome::Reject
    }
}

/// Verify that `model` satisfies every constraint (`coeffs·model <= rhs`).
///
/// Returns [`Outcome::Accept`] if all hold, [`Outcome::Reject`] if any is violated,
/// and [`Outcome::Inconclusive`] on a length mismatch or arithmetic overflow.
pub fn check_lra_model(constraints: &[LinConstraint], model: &[Rational]) -> Outcome {
    for c in constraints {
        let mut lhs = Rational::zero();
        for (j, coeff) in c.coeffs.iter().enumerate() {
            let val = match model.get(j) {
                Some(v) => *v,
                None => Rational::zero(),
            };
            let term = match coeff.mul(val) {
                Some(t) => t,
                None => return Outcome::Inconclusive,
            };
            lhs = match lhs.add(term) {
                Some(t) => t,
                None => return Outcome::Inconclusive,
            };
        }
        if lhs.cmp(c.rhs) == Ordering::Greater {
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
    fn model_check_fails() {
        let cons = vec![c(&[1], 5)];
        let model = vec![Rational::from_i64(9)];
        assert!(check_lra_model(&cons, &model).is_reject());
    }
}
