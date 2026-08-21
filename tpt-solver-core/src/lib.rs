//! # tpt-solver-core
//!
//! The **untrusted** solving engine of the tpt-solver suite. This crate contains the
//! aggressively-optimized search code (CDCL SAT, DPLL(T), Simplex, Fourier-Motzkin)
//! whose answers are *never* trusted blindly — every result is revalidated by
//! [`tpt-solver-check`](https://crates.io/crates/tpt-solver-check).
//!
//! Design constraints (see the suite design document):
//!
//! * `no_std` + `alloc`, **zero runtime dependencies** by default — this keeps the
//!   trusted boundary small and the build reproducible. The `std` feature (on by
//!   default) simply lifts the `no_std` restriction so that `std`-only dev tooling
//!   (e.g. `proptest`) can be used in tests.
//! * `#![deny(clippy::unwrap_used, clippy::panic)]` — the engine must never panic or
//!   unwrap on a fallible path; everything returns `Result`/`Option` or consumes
//!   *fuel* and returns [`Unknown`](crate::engine::SolveResult::Unknown).
//! * A built-in **fuel** system: every loop consumes fuel and returns
//!   [`SolveResult::Unknown`] on depletion rather than looping forever or panicking.

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(unexpected_cfgs)] // `cfg(kani)` is set by the Kani toolchain, not by rustc.
#![deny(clippy::unwrap_used)]
#![deny(clippy::panic)]
#![warn(missing_docs)]

extern crate alloc;

pub mod engine;
pub mod fuel;
pub mod ir;
#[cfg(kani)]
pub mod kani_harnesses;
pub mod lra;
pub mod memory;
pub mod rational;
pub mod sat;

#[cfg(test)]
mod invariants;
