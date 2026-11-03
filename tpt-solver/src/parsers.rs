//! Parsers for problem input formats (DIMACS, SMT-LIB2, LP-MPS).
//!
//! Parsers are the fuzzing surface of the suite, so each is written to fail safely on
//! malformed/truncated input (returning a typed `Err` rather than panicking) and is
//! paired with a `cargo-fuzz` target under `fuzz/`.

pub mod dimacs;
pub mod mps;
pub mod smtlib2;

/// A parse error tagged with the 1-based line it was found on. `line == 0` means
/// the error concerns the document as a whole rather than one line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Located<E> {
    /// 1-based line number, or `0` for document-level errors.
    pub line: usize,
    /// The underlying parse error.
    pub error: E,
}

impl<E: core::fmt::Display> core::fmt::Display for Located<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.line == 0 {
            write!(f, "{}", self.error)
        } else {
            write!(f, "line {}: {}", self.line, self.error)
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for Located<E> {}
