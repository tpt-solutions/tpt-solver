//! # tpt-solver (periphery)
//!
//! The periphery of the tpt-solver suite: parsers, CLI, e-graph preprocessing, and
//! integration glue that ties the untrusted [`tpt_solver_core`] engine to the trusted
//! [`tpt_solver_check`] kernel.
//!
//! This crate is allowed MIT-compatible dependencies (e.g. `clap`,
//! `cargo-fuzz` targets) that the zero-dependency core and kernel forbid. Full
//! parsers and CLI arrive in Phase 4; what exists now is the reference solver and the
//! end-to-end integration path.

#[cfg(test)]
mod differential;
mod egraph;
pub mod parsers;
pub mod policy;
pub mod portfolio;
pub mod reference;

pub use tpt_solver_check as check;
pub use tpt_solver_core as core;
