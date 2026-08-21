//! DIMACS CNF parser.
//!
//! Parses the standard DIMACS SAT format:
//!
//! ```text
//! c comment
//! p cnf <variables> <clauses>
//! 1 -3 0
//! 2 3 -1 0
//! ```
//!
//! Clauses are terminated by `0`; clauses may span multiple lines and comments may
//! appear anywhere. The parser is lenient about a missing `p` header (it infers the
//! variable count from the largest literal) and expands the declared count if a
//! literal exceeds it, since some generators are sloppy. It never panics on bad
//! input — it returns [`DimacsError`].

use crate::reference::Problem;
use std::error::Error;
use std::fmt;

/// Error produced while parsing a DIMACS CNF stream.
#[derive(Debug)]
pub enum DimacsError {
    /// No `p cnf` header was found and no literals were present.
    MissingHeader,
    /// The `p` line was malformed (not `p cnf <n> <m>`).
    InvalidHeader,
    /// A non-integer token appeared where an integer was expected.
    ExpectedInteger(std::num::ParseIntError),
}

impl fmt::Display for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DimacsError::MissingHeader => write!(f, "DIMACS: missing 'p cnf' header"),
            DimacsError::InvalidHeader => write!(
                f,
                "DIMACS: invalid problem line (expected 'p cnf <vars> <clauses>')"
            ),
            DimacsError::ExpectedInteger(e) => write!(f, "DIMACS: expected integer literal: {}", e),
        }
    }
}

impl Error for DimacsError {}

impl From<std::num::ParseIntError> for DimacsError {
    fn from(e: std::num::ParseIntError) -> Self {
        DimacsError::ExpectedInteger(e)
    }
}

/// Parse a DIMACS CNF document into a [`Problem`].
pub fn parse_dimacs(input: &str) -> Result<Problem, DimacsError> {
    let mut var_count: u32 = 0;
    let mut header_seen = false;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut current: Vec<i32> = Vec::new();
    let mut max_var: u32 = 0;

    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with('c') {
            continue;
        }
        if trimmed.starts_with('p') {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err(DimacsError::InvalidHeader);
            }
            var_count = parts[2].parse()?;
            // The clause count in the header is informational; we derive the true
            // count from the terminators actually present.
            header_seen = true;
            continue;
        }

        for tok in trimmed.split_whitespace() {
            let lit: i32 = tok.parse()?;
            if lit == 0 {
                // Terminator: close the current clause (an empty clause is a valid
                // UNSAT marker and is kept as an empty Vec).
                clauses.push(std::mem::take(&mut current));
                current = Vec::new();
            } else {
                let v = lit.unsigned_abs();
                if v > max_var {
                    max_var = v;
                }
                if v > var_count {
                    // Lenient: grow the declared count rather than reject.
                    var_count = v;
                }
                current.push(lit);
            }
        }
    }

    if !current.is_empty() {
        // Some files omit the final `0`; treat the trailing run as a clause.
        clauses.push(current);
    }

    if !header_seen && max_var == 0 {
        return Err(DimacsError::MissingHeader);
    }
    if !header_seen {
        var_count = max_var;
    }

    Ok(Problem { var_count, clauses })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_basic_cnf() {
        let input = "c a comment\np cnf 3 2\n1 -3 0\n2 3 -1 0\n";
        let p = parse_dimacs(input).unwrap();
        assert_eq!(p.var_count, 3);
        assert_eq!(p.clauses, vec![vec![1, -3], vec![2, 3, -1]]);
    }

    #[test]
    fn handles_comments_and_spanning_clauses() {
        let input = "p cnf 2 2\n1\n2 0\nc mid\n-1 -2 0\n";
        let p = parse_dimacs(input).unwrap();
        assert_eq!(p.clauses, vec![vec![1, 2], vec![-1, -2]]);
    }

    #[test]
    fn empty_clause_is_unsat_marker() {
        let input = "p cnf 1 1\n0\n";
        let p = parse_dimacs(input).unwrap();
        assert_eq!(p.clauses, vec![vec![]]);
    }

    #[test]
    fn missing_header_infers_count() {
        let input = "1 -2 3 0\n";
        let p = parse_dimacs(input).unwrap();
        assert_eq!(p.var_count, 3);
        assert_eq!(p.clauses, vec![vec![1, -2, 3]]);
    }

    #[test]
    fn rejects_garbage_token() {
        let input = "p cnf 1 1\nx 0\n";
        assert!(parse_dimacs(input).is_err());
    }
}
