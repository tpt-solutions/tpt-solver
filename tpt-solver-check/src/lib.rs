//! # tpt-solver-check
//!
//! The **trusted kernel** of the tpt-solver suite. This crate is deliberately tiny:
//! it is the *only* place whose correctness the whole system's answers rely on, so
//! it is kept as small and as self-contained as possible, and it is the target of
//! formal contracts (`tpt-telos`).
//!
//! It never trusts the engine. Every answer from [`tpt-solver-core`] is revalidated
//! here independently:
//!
//! * **UNSAT** — via a certificate checker (LRAT for SAT-propositional, Farkas for
//!   LRA), verified clause-by-clause or coefficient-by-coefficient against the
//!   original problem. (Certificate formats land in Phase 2/3; the three-way outcome
//!   type and a cheap SAT *model recheck* are in place from day one.)
//! * **SAT** — by substituting the returned assignment into the original formula and
//!   checking satisfaction. This alone catches the overwhelming majority of "wrong
//!   SAT answer" bugs at near-zero cost.
//!
//! The checker reports one of three outcomes (never a bare boolean) so that a real
//! solver bug (`Reject`) is never confused with a checker resource problem
//! (`Inconclusive`).

#![no_std]
#![deny(clippy::unwrap_used)]
#![deny(clippy::panic)]
#![warn(missing_docs)]

extern crate alloc;

pub mod lra;
pub mod lrat;
pub mod outcome;
pub mod sat;
