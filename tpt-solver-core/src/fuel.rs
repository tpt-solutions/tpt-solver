//! Resource budget ("fuel") for bounded search.
//!
//! Every search loop in the engine consumes fuel. When fuel is exhausted the loop
//! returns [`crate::engine::SolveResult::Unknown`] instead of looping forever or
//! panicking. This is the engine's primary liveness guarantee.

use core::num::NonZeroU64;

/// A monotonically-decreasing resource budget.
///
/// Fuel is a count of "units of work" a search may perform before it must yield a
/// result. Units are deliberately unspecified at this layer (a caller may count
/// decisions, propagations, conflict analyses, or wall-clock ticks converted to a
/// count); what matters is that every loop decrements and checks it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Fuel(u64);

impl Fuel {
    /// The unlimited budget. Use with care: only meaningful where another liveness
    /// mechanism (e.g. a proven termination argument) bounds the loop.
    pub const UNLIMITED: Fuel = Fuel(u64::MAX);

    /// Create a finite fuel budget.
    #[inline]
    pub const fn new(amount: u64) -> Fuel {
        Fuel(amount)
    }

    /// Create a finite, non-zero fuel budget, or `None` if `amount` is zero.
    #[inline]
    pub const fn new_nonzero(amount: NonZeroU64) -> Fuel {
        Fuel(amount.get())
    }

    /// Remaining fuel.
    #[inline]
    pub const fn remaining(self) -> u64 {
        self.0
    }

    /// Whether any fuel remains.
    #[inline]
    pub const fn is_exhausted(self) -> bool {
        self.0 == 0
    }

    /// Consume one unit. Returns `false` (and does not decrement) if exhausted.
    #[inline]
    pub fn burn_one(&mut self) -> bool {
        if self.0 == 0 {
            return false;
        }
        self.0 -= 1;
        true
    }

    /// Consume `n` units if available, otherwise leave the budget untouched and
    /// return `false`.
    #[inline]
    pub fn burn(&mut self, n: u64) -> bool {
        match self.0.checked_sub(n) {
            Some(rem) => {
                self.0 = rem;
                true
            }
            None => false,
        }
    }

    /// Split off `n` units into a child budget, leaving the remainder here. Used to
    /// cap nested sub-problems independently.
    #[inline]
    pub fn split(&mut self, n: u64) -> Fuel {
        let taken = core::cmp::min(n, self.0);
        self.0 -= taken;
        Fuel(taken)
    }
}

impl core::ops::Add for Fuel {
    type Output = Fuel;
    #[inline]
    fn add(self, rhs: Fuel) -> Fuel {
        Fuel(self.0.saturating_add(rhs.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn burn_to_exhaustion() {
        let mut f = Fuel::new(3);
        assert!(f.burn_one());
        assert!(f.burn_one());
        assert!(f.burn_one());
        assert!(!f.burn_one());
        assert!(f.is_exhausted());
    }

    #[test]
    fn split_leaves_remainder() {
        let mut f = Fuel::new(10);
        let child = f.split(4);
        assert_eq!(child.remaining(), 4);
        assert_eq!(f.remaining(), 6);
    }
}
