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

    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    pub fn is_negative(self) -> bool {
        self.num < 0
    }

    /// Whether the rational is strictly positive (`num > 0`).
    pub fn is_positive(self) -> bool {
        self.num > 0
    }

    pub fn neg(self) -> Rational {
        Rational {
            num: -self.num,
            den: self.den,
        }
    }

    /// Addition, or `None` on overflow.
    pub fn add(self, o: Rational) -> Option<Rational> {
        let num = self.num.checked_mul(o.den)?.checked_add(o.num.checked_mul(self.den)?)?;
        let den = self.den.checked_mul(o.den)?;
        Rational::new(num, den)
    }

    /// Multiplication, or `None` on overflow.
    pub fn mul(self, o: Rational) -> Option<Rational> {
        let num = self.num.checked_mul(o.num)?;
        let den = self.den.checked_mul(o.den)?;
        Rational::new(num, den)
    }

    /// Total order via cross-multiplication.
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
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(Rational::cmp(*self, *o))
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
            Rational::new(2, 4).unwrap().cmp(Rational::new(1, 2).unwrap()),
            Ordering::Equal
        );
    }
}
