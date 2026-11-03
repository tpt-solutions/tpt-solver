#![warn(missing_docs)]
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

pub mod api;
#[cfg(test)]
mod differential;
mod egraph;
pub mod parsers;
pub mod policy;
pub mod portfolio;
pub mod reference;

pub use tpt_solver_check as check;
pub use tpt_solver_core as core;

/// The names most callers need, in one import: `use tpt_solver::prelude::*;`.
pub mod prelude {
    pub use crate::api::{
        check_proof_text, read_input, resolve_format, solve_file, solve_str, Error, Format, Model,
        Options, Proof, Report, Stats, Theory,
    };
    pub use tpt_solver_check::outcome::Outcome;
    pub use tpt_solver_core::engine::SolveResult;
}
