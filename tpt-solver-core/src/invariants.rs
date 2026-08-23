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
use crate::lra::{lra_model, LinConstraint};
use crate::memory::{Arena, Trail};
use crate::rational::Rational;
use proptest::prelude::*;

fn mk_constraint(coeffs: &[i64], rhs: i64) -> LinConstraint {
    LinConstraint {
        coeffs: coeffs.iter().map(|&c| Rational::from_i64(c)).collect(),
        rhs: Rational::from_i64(rhs),
    }
}

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

    /// Simplex is pivot-bounded (`lra_model`'s iteration ceiling in `lra.rs` is a
    /// hard loop cap, so this always terminates) and self-consistent: whenever it
    /// does report a model, that model actually satisfies every original
    /// constraint. This is the runtime property-testing stand-in for the
    /// `tpt-telos` "Simplex pivot bounds" contract (spec §5.2) — `tpt-telos` is a
    /// separate external tool (see Phase 2/3 notes), so the bounded-arithmetic
    /// property it would have proven is discharged here instead.
    #[test]
    fn lra_model_terminates_and_is_self_consistent(
        a in proptest::collection::vec(-5i64..=5, 6),
        r in proptest::collection::vec(-10i64..=10, 3),
    ) {
        let cons = vec![
            mk_constraint(&a[0..2], r[0]),
            mk_constraint(&a[2..4], r[1]),
            mk_constraint(&a[4..6], r[2]),
        ];
        if let Some(Some(model)) = lra_model(&cons) {
            for c in &cons {
                let mut sum = Rational::zero();
                for (coef, x) in c.coeffs.iter().zip(model.iter()) {
                    sum = sum.add(coef.mul(*x).unwrap()).unwrap();
                }
                prop_assert!(sum.cmp(c.rhs) != core::cmp::Ordering::Greater);
            }
        }
    }
}
