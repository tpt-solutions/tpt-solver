//! Parsers for problem input formats (DIMACS, SMT-LIB2, LP-MPS).
//!
//! Parsers are the fuzzing surface of the suite, so each is written to fail safely on
//! malformed/truncated input (returning a typed `Err` rather than panicking) and is
//! paired with a `cargo-fuzz` target under `fuzz/`.

pub mod dimacs;
pub mod mps;
pub mod smtlib2;
