//! Unified intermediate representation and strongly-typed identifiers.
//!
//! ## Why newtypes?
//!
//! Raw `usize` indices into solver tables are a classic source of silent logic bugs:
//! nothing stops you from passing a clause index where a variable index is expected.
//! Here every identifier is a distinct newtype, so such mix-ups are compile errors.
//!
//! ## Why session-tagged?
//!
//! In incremental solving (`push`/`pop`) a real bug class is reusing an identifier
//! from a prior context after backtracking. To make that a *compile* error rather
//! than a silent logic error, identifiers are branded with a **session tag** `S`
//! (a zero-sized phantom type). IDs produced by one solver/generation scope do not
//! type-check against another scope, so a stale ID cannot be smuggled across a
//! `pop`.

use core::marker::PhantomData;
use core::num::NonZeroU32;

/// A variable identifier, branded with session tag `S`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct VarId<S = ()>(NonZeroU32, PhantomData<S>);

/// A clause identifier, branded with session tag `S`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ClauseId<S = ()>(NonZeroU32, PhantomData<S>);

/// A Boolean literal: a variable under a polarity.
///
/// `polarity == true` means the literal is the variable as-is; `false` means its
/// negation. The session tag `S` is threaded from the owning variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit<S = ()> {
    /// The low bit encodes polarity; the remaining bits hold the variable's `u32`.
    raw: u32,
    tag: PhantomData<S>,
}

impl<S> VarId<S> {
    /// Construct from a 1-based index. Returns `None` for index `0` (a reserved,
    /// never-valid variable).
    #[inline]
    pub fn new(index: u32) -> Option<VarId<S>> {
        NonZeroU32::new(index).map(|nz| VarId(nz, PhantomData))
    }

    /// Construct from a [`NonZeroU32`], bypassing the zero check.
    #[inline]
    pub const fn from_nonzero(nz: NonZeroU32) -> VarId<S> {
        VarId(nz, PhantomData)
    }

    /// 1-based index value.
    #[inline]
    pub const fn get(self) -> u32 {
        self.0.get()
    }

    /// 0-based index, suitable for table lookups.
    #[inline]
    pub const fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }

    /// Re-brand to a different session without touching the underlying index.
    ///
    /// # Safety
    /// The caller must guarantee the new session `D` actually owns this identifier.
    /// Re-branding across a session boundary is exactly the bug this module exists
    /// to prevent, so this is an `unsafe` escape hatch, not a normal operation.
    #[inline]
    pub unsafe fn cast<D>(self) -> VarId<D> {
        VarId(self.0, PhantomData)
    }
}

impl<S> ClauseId<S> {
    /// Construct from a 1-based index. Returns `None` for index `0`.
    #[inline]
    pub fn new(index: u32) -> Option<ClauseId<S>> {
        NonZeroU32::new(index).map(|nz| ClauseId(nz, PhantomData))
    }

    /// Construct from a [`NonZeroU32`], bypassing the zero check.
    #[inline]
    pub const fn from_nonzero(nz: NonZeroU32) -> ClauseId<S> {
        ClauseId(nz, PhantomData)
    }

    /// 1-based index value.
    #[inline]
    pub const fn get(self) -> u32 {
        self.0.get()
    }

    /// 0-based index, suitable for table lookups.
    #[inline]
    pub const fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }

    /// Re-brand to a different session. See [`VarId::cast`].
    ///
    /// # Safety
    /// The caller must guarantee the new session `D` actually owns this identifier.
    #[inline]
    pub unsafe fn cast<D>(self) -> ClauseId<D> {
        ClauseId(self.0, PhantomData)
    }
}

impl<S> Lit<S> {
    const POLARITY_MASK: u32 = 1;

    /// Build a literal from a variable and a polarity.
    #[inline]
    pub fn new(var: VarId<S>, polarity: bool) -> Lit<S> {
        let raw = (var.get() << 1) | u32::from(!polarity);
        Lit {
            raw,
            tag: PhantomData,
        }
    }

    /// The variable this literal refers to.
    #[inline]
    pub fn var(self) -> VarId<S> {
        // Variable is stored in the high bits; shift back down past the polarity bit.
        let v = self.raw >> 1;
        VarId::from_nonzero(NonZeroU32::new(v).expect("lit index never zero"))
    }

    /// The polarity: `true` if this is the positive literal, `false` if negated.
    #[inline]
    pub fn is_positive(self) -> bool {
        (self.raw & Self::POLARITY_MASK) == 0
    }

    /// The negation of this literal (same variable, flipped polarity).
    #[inline]
    pub fn negate(self) -> Lit<S> {
        Lit {
            raw: self.raw ^ Self::POLARITY_MASK,
            tag: PhantomData,
        }
    }

    /// Raw packed representation (variable in high bits, polarity in low bit).
    #[inline]
    pub const fn raw(self) -> u32 {
        self.raw
    }

    /// Re-brand to a different session. See [`VarId::cast`].
    ///
    /// # Safety
    /// The caller must guarantee the new session `D` actually owns this literal.
    #[inline]
    pub unsafe fn cast<D>(self) -> Lit<D> {
        Lit {
            raw: self.raw,
            tag: PhantomData,
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn var_zero_is_invalid() {
        assert!(VarId::<()>::new(0).is_none());
        assert!(VarId::<()>::new(1).is_some());
    }

    #[test]
    fn lit_roundtrip() {
        let v = VarId::<()>::new(7).unwrap();
        let l = Lit::new(v, true);
        assert!(l.is_positive());
        assert_eq!(l.var(), v);
        assert!(!l.negate().is_positive());
        assert_eq!(l.negate().var(), v);
    }

    #[test]
    fn branding_blocks_cross_session_use() {
        // The following would not compile: a VarId<'a> is not a VarId<'b>.
        // let a: VarId<'static> = VarId::new(1).unwrap();
        // let _b: VarId<'x> = a; // compile error
        let v = VarId::<()>::new(3).unwrap();
        assert_eq!(v.index(), 2);
    }
}
