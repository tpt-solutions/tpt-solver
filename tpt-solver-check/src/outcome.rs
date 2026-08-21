//! The three-way checker outcome.
//!
//! Conflating *reject* (a real bug signal from the engine) with *inconclusive* (the
//! checker could not reach a verdict within its own budget) hides which problem you
//! actually have. The checker therefore never returns a bare boolean.

/// Verdict returned by every checker in this crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The certificate was verified; the engine's answer is trustworthy.
    Accept,
    /// The certificate was structurally valid but does not establish the claimed
    /// result — a real bug signal from the engine.
    Reject,
    /// The checker could not reach a verdict (fuel exhausted, malformed/truncated
    /// certificate, unsupported theory). Not evidence of an engine bug.
    Inconclusive,
}

impl Outcome {
    /// `true` iff this outcome is [`Outcome::Accept`].
    #[inline]
    pub const fn is_accept(self) -> bool {
        matches!(self, Outcome::Accept)
    }

    /// `true` iff this outcome is [`Outcome::Reject`].
    #[inline]
    pub const fn is_reject(self) -> bool {
        matches!(self, Outcome::Reject)
    }

    /// `true` iff this outcome is [`Outcome::Inconclusive`].
    #[inline]
    pub const fn is_inconclusive(self) -> bool {
        matches!(self, Outcome::Inconclusive)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicates() {
        assert!(Outcome::Accept.is_accept());
        assert!(Outcome::Reject.is_reject());
        assert!(Outcome::Inconclusive.is_inconclusive());
    }
}
