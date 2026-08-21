//! Property tests for the bounded linear-arithmetic invariants that the
//! certificate architecture relies on — the same class of properties the external
//! `tpt-telos` verifier is meant to discharge (see spec §5.2: "Fuel accounting and
//! arena/trail offset math in `tpt-solver-core`", and the checker's arithmetic).
//!
//! These run in normal CI (`cargo test`) and are the immediately-available
//! verification surface; the corresponding unbounded proofs live in
//! `kani_harnesses.rs` behind the `cfg(kani)` Kani build.
#![allow(clippy::unwrap_used)] // Generated inputs are in-range; unwraps are safe here.

use crate::fuel::Fuel;
use crate::ir::{Lit, VarId};
use crate::memory::{Arena, Trail};
use proptest::prelude::*;

proptest! {
    /// Fuel is conserved by `split`: the child's remaining plus the parent's
    /// remaining always equals the original amount.
    #[test]
    fn fuel_split_conserves(fuel in 0u64..100_000, n in 0u64..100_000) {
        let mut f = Fuel::new(fuel);
        let child = f.split(n);
        prop_assert_eq!(child.remaining() + f.remaining(), fuel);
    }

    /// `burn_one` drains exactly `fuel` units, never underflowing.
    #[test]
    fn fuel_burn_drains_exactly(fuel in 0u64..100_000) {
        let mut f = Fuel::new(fuel);
        let mut count = 0u64;
        while f.burn_one() {
            count += 1;
        }
        prop_assert_eq!(count, fuel);
        prop_assert!(f.is_exhausted());
    }

    /// Literal packing is lossless: variable, polarity, and double-negation all
    /// round-trip.
    #[test]
    fn lit_packing_roundtrip(var in 1u32..1_000_000, pol in any::<bool>()) {
        let v = VarId::<()>::new(var).unwrap();
        let l = Lit::new(v, pol);
        prop_assert_eq!(l.var(), v);
        prop_assert_eq!(l.is_positive(), pol);
        prop_assert_eq!(l.negate().negate(), l);
    }

    /// Trail rewind restores the exact prior length (O(1) backtracking invariant).
    #[test]
    fn trail_rewind_restores_length(items in proptest::collection::vec(any::<u32>(), 0..64)) {
        let mut t: Trail<u32> = Trail::default();
        for &x in &items {
            t.push(x);
        }
        let cp = t.checkpoint();
        for x in 0..16u32 {
            t.push(x);
        }
        t.truncate(cp);
        prop_assert_eq!(t.len(), items.len());
    }

    /// Arena reset discards only entries above the watermark.
    #[test]
    fn arena_reset_restores_length(items in proptest::collection::vec(any::<u32>(), 0..64)) {
        let mut a: Arena<u32> = Arena::default();
        for &x in &items {
            a.push(x);
        }
        let w = a.watermark();
        for x in 0..16u32 {
            a.push(x);
        }
        a.reset(w);
        prop_assert_eq!(a.len(), items.len());
    }
}
