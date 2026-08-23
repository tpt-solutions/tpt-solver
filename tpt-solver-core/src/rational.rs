//! Minimal exact rational arithmetic for the LRA engine and the certificate
//! checker.
//!
//! This is intentionally tiny: the only arithmetic the Farkas/Simplex machinery
//! needs is exact rational addition, multiplication, and sign comparison — the
//! bounded linear-arithmetic surface that the verifier (and `tpt-telos`) is meant to
//! cover. It is `i128`-backed; any operation that would overflow returns `None` so
//! callers can degrade to [`Outcome::Inconclusive`](crate::outcome) rather than
//! panic, keeping the `#![deny(clippy::panic)]` guarantee.

use core::cmp::Ordering;

/// An exact rational `num / den` with `den > 0` (canonical form).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rational {
    num: i128,
    den: i128,
}

impl Rational {
    /// Build a rational, reducing by the GCD. Returns `None` for a zero denominator.
    pub fn new(num: i128, den: i128) -> Option<Rational> {
        if den == 0 {
            return None;
        }
        let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
        let g = gcd(num.unsigned_abs(), den.unsigned_abs());
        if g == 0 {
            return Some(Rational { num: 0, den: 1 });
        }
        Some(Rational {
            num: num / g as i128,
            den: den / g as i128,
        })
    }

    /// From a plain integer.
    pub fn from_i64(n: i64) -> Rational {
        Rational {
            num: n as i128,
            den: 1,
        }
    }

    /// The rational zero.
    pub fn zero() -> Rational {
        Rational { num: 0, den: 1 }
    }

    /// Whether the rational is exactly zero.
    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    /// Whether the rational is strictly negative (`num < 0`).
    pub fn is_negative(self) -> bool {
        self.num < 0
    }

    /// Whether the rational is strictly positive (`num > 0`).
    pub fn is_positive(self) -> bool {
        self.num > 0
    }

    /// The value as a `u64`, iff it is a non-negative integer that fits.
    /// Used by the array-theory front end, whose element universe is `u64`.
    pub fn to_u64(self) -> Option<u64> {
        if self.den == 1 && self.num >= 0 && self.num <= u64::MAX as i128 {
            Some(self.num as u64)
        } else {
            None
        }
    }

    /// Negation. Takes and returns `Rational` by value, not `&Self`/`Neg`, to match
    /// the rest of this by-value, no-operator-overload API on a small `Copy` type.
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> Rational {
        Rational {
            num: -self.num,
            den: self.den,
        }
    }

    /// Addition, or `None` on overflow. By-value like [`Rational::neg`], not `Add`.
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, o: Rational) -> Option<Rational> {
        let num = self
            .num
            .checked_mul(o.den)?
            .checked_add(o.num.checked_mul(self.den)?)?;
        let den = self.den.checked_mul(o.den)?;
        Rational::new(num, den)
    }

    /// Multiplication, or `None` on overflow. By-value like [`Rational::neg`], not
    /// `Mul`.
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, o: Rational) -> Option<Rational> {
        let num = self.num.checked_mul(o.num)?;
        let den = self.den.checked_mul(o.den)?;
        Rational::new(num, den)
    }

    /// Total order via cross-multiplication. By-value like [`Rational::neg`]; the
    /// reference-taking [`Ord::cmp`] impl below delegates to this one.
    #[allow(clippy::should_implement_trait)]
    pub fn cmp(self, o: Rational) -> Ordering {
        let lhs = match self.num.checked_mul(o.den) {
            Some(v) => v,
            None => return self.num.signum().cmp(&o.num.signum()),
        };
        let rhs = match o.num.checked_mul(self.den) {
            Some(v) => v,
            None => return self.num.signum().cmp(&o.num.signum()),
        };
        lhs.cmp(&rhs)
    }

    /// Division, or `None` on overflow or division by zero.
    pub fn checked_div(self, o: Rational) -> Option<Rational> {
        if o.is_zero() {
            return None;
        }
        let num = self.num.checked_mul(o.den)?;
        let den = self.den.checked_mul(o.num)?;
        Rational::new(num, den)
    }

    /// The canonical `(numerator, denominator)` pair. Test-only: production code
    /// never needs to decompose a `Rational`, but the oracle differential test
    /// below does, to compare against an independent reference implementation.
    #[cfg(test)]
    pub(crate) fn parts(self) -> (i128, i128) {
        (self.num, self.den)
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Rational {
    fn cmp(&self, o: &Self) -> Ordering {
        Rational::cmp(*self, *o)
    }
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic() {
        let a = Rational::new(1, 2).unwrap();
        let b = Rational::new(1, 3).unwrap();
        assert_eq!(a.add(b).unwrap(), Rational::new(5, 6).unwrap());
        assert_eq!(a.mul(b).unwrap(), Rational::new(1, 6).unwrap());
        assert_eq!(Rational::new(2, 4).unwrap(), Rational::new(1, 2).unwrap());
        assert!(Rational::new(-3, 1).unwrap().is_negative());
        assert!(!Rational::new(-3, 1).unwrap().is_zero());
    }

    #[test]
    fn ordering() {
        assert!(Rational::new(1, 3).unwrap() < Rational::new(1, 2).unwrap());
        assert_eq!(
            Rational::new(2, 4)
                .unwrap()
                .cmp(Rational::new(1, 2).unwrap()),
            Ordering::Equal
        );
    }
}

/// Differential fuzzing of `Rational` against an independent, arbitrary-precision
/// reference implementation (spec §4.2: a custom exact-rational is only permitted
/// if it's checked against a reference oracle from day one — `num-rational` is a
/// dev-dependency-only oracle, never a runtime dependency of this `no_std` crate).
#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod oracle {
    use super::Rational;
    use num_rational::Ratio;
    use proptest::prelude::*;

    /// Bounded so every operation below stays comfortably within `i128`; the
    /// point of this test is comparing *values*, not `Rational`'s own overflow
    /// handling (already covered directly by `invariants.rs`/unit tests).
    fn small_num() -> impl Strategy<Value = i64> {
        -1_000i64..=1_000
    }
    fn small_den() -> impl Strategy<Value = i64> {
        1i64..=1_000
    }

    fn to_oracle(n: i64, d: i64) -> Ratio<i128> {
        Ratio::new(n as i128, d as i128)
    }

    fn oracle_parts(r: Ratio<i128>) -> (i128, i128) {
        (*r.numer(), *r.denom())
    }

    proptest! {
        #[test]
        fn add_matches_oracle(n1 in small_num(), d1 in small_den(), n2 in small_num(), d2 in small_den()) {
            let ours = Rational::new(n1 as i128, d1 as i128).unwrap()
                .add(Rational::new(n2 as i128, d2 as i128).unwrap())
                .unwrap();
            let oracle = to_oracle(n1, d1) + to_oracle(n2, d2);
            prop_assert_eq!(ours.parts(), oracle_parts(oracle));
        }

        #[test]
        fn mul_matches_oracle(n1 in small_num(), d1 in small_den(), n2 in small_num(), d2 in small_den()) {
            let ours = Rational::new(n1 as i128, d1 as i128).unwrap()
                .mul(Rational::new(n2 as i128, d2 as i128).unwrap())
                .unwrap();
            let oracle = to_oracle(n1, d1) * to_oracle(n2, d2);
            prop_assert_eq!(ours.parts(), oracle_parts(oracle));
        }

        #[test]
        fn neg_matches_oracle(n in small_num(), d in small_den()) {
            let ours = Rational::new(n as i128, d as i128).unwrap().neg();
            let oracle = -to_oracle(n, d);
            prop_assert_eq!(ours.parts(), oracle_parts(oracle));
        }

        #[test]
        fn cmp_matches_oracle(n1 in small_num(), d1 in small_den(), n2 in small_num(), d2 in small_den()) {
            let ours = Rational::new(n1 as i128, d1 as i128).unwrap()
                .cmp(Rational::new(n2 as i128, d2 as i128).unwrap());
            let oracle = to_oracle(n1, d1).cmp(&to_oracle(n2, d2));
            prop_assert_eq!(ours, oracle);
        }

        #[test]
        fn is_zero_and_is_negative_match_oracle(n in small_num(), d in small_den()) {
            let ours = Rational::new(n as i128, d as i128).unwrap();
            let oracle = to_oracle(n, d);
            prop_assert_eq!(ours.is_zero(), oracle.numer() == &0);
            prop_assert_eq!(ours.is_negative(), oracle.numer() < &0);
        }

        #[test]
        fn checked_div_matches_oracle(n1 in small_num(), d1 in small_den(), n2 in small_num(), d2 in small_den()) {
            prop_assume!(n2 != 0);
            let ours = Rational::new(n1 as i128, d1 as i128).unwrap()
                .checked_div(Rational::new(n2 as i128, d2 as i128).unwrap())
                .unwrap();
            let oracle = to_oracle(n1, d1) / to_oracle(n2, d2);
            prop_assert_eq!(ours.parts(), oracle_parts(oracle));
        }
    }
}
