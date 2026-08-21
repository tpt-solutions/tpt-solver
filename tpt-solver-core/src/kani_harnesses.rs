//! Kani bounded-model-checking harnesses for the core's safety-critical code.
//!
//! These are the unbounded counterparts of the `invariants` property tests: Kani
//! explores *all* inputs up to its unrolling bound rather than sampling. They target
//! exactly the code whose bug surface is hand-optimized memory/index arithmetic:
//!
//! * **fuel** — conservation across `split`, exact drain on `burn_one`.
//! * **literal packing** — lossless var/polarity/double-negation round-trip.
//! * **trail / arena** — O(1) backtracking restores the prior length.
//!
//! Run with `cargo kani` (the Kani toolchain provides the `kani` crate and sets
//! `cfg(kani)`; no Cargo dependency or feature flag is needed). This module is only
//! compiled by the Kani compiler, so it never affects the normal build or CI test
//! loop.

use crate::fuel::Fuel;
use crate::ir::{Lit, VarId};
use crate::memory::{Arena, Trail};
use core::num::NonZeroU32;
use kani;

#[kani::proof]
fn kani_fuel_split_conserves() {
    let fuel: u64 = kani::any();
    let n: u64 = kani::any();
    let mut f = Fuel::new(fuel);
    let child = f.split(n);
    assert_eq!(child.remaining() + f.remaining(), fuel);
}

#[kani::proof]
fn kani_fuel_burn_drains() {
    let fuel: u64 = kani::any();
    let mut f = Fuel::new(fuel);
    let mut count = 0u64;
    while f.burn_one() {
        count += 1;
    }
    assert_eq!(count, fuel);
    assert!(f.is_exhausted());
}

#[kani::proof]
fn kani_lit_packing_roundtrip() {
    let raw: u32 = kani::any();
    kani::assume(raw != 0);
    let v = VarId::from_nonzero(unsafe { NonZeroU32::new_unchecked(raw) });
    let pol: bool = kani::any();
    let l = Lit::new(v, pol);
    assert_eq!(l.var(), v);
    assert_eq!(l.is_positive(), pol);
    assert_eq!(l.negate().negate(), l);
}

#[kani::proof]
fn kani_trail_rewind_restores_length() {
    let n: usize = kani::any();
    kani::assume(n <= 64);
    let mut t: Trail<u32> = Trail::default();
    for _ in 0..n {
        t.push(kani::any::<u32>());
    }
    let cp = t.checkpoint();
    for _ in 0..8usize {
        t.push(kani::any::<u32>());
    }
    t.truncate(cp);
    assert_eq!(t.len(), n);
}

#[kani::proof]
fn kani_arena_reset_restores_length() {
    let n: usize = kani::any();
    kani::assume(n <= 64);
    let mut a: Arena<u32> = Arena::default();
    for _ in 0..n {
        a.push(kani::any::<u32>());
    }
    let w = a.watermark();
    for _ in 0..8usize {
        a.push(kani::any::<u32>());
    }
    a.reset(w);
    assert_eq!(a.len(), n);
}
