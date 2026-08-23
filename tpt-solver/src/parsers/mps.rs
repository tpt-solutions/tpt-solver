//! Free-format LP-MPS parser.
//!
//! Parses the (free-format) MPS linear-programming interchange format into an
//! [`LraProblem`] the core's Fourier–Motzkin/Simplex engine can consume. Like the
//! other parsers in this module, it never panics on malformed input — every
//! failure mode returns a typed [`MpsError`].
//!
//! ## Supported subset
//!
//! * Sections `NAME`, `OBJSENSE`, `ROWS`, `COLUMNS`, `RHS`, `RANGES`, `BOUNDS`,
//!   `ENDATA`. Section headers are recognized by their leading keyword regardless
//!   of column position (this is the free-format convention; fixed-column MPS is
//!   not supported).
//! * Row types `N` (free/objective — contributes no constraint), `L` (`<=`), `G`
//!   (`>=`), `E` (`=`). Only the *feasibility* system is built: this is a
//!   feasibility engine, not an LP optimizer, so `N` rows (including the
//!   objective) are parsed but otherwise dropped.
//! * `RANGES`, per the standard MPS convention: a range `r` on row type `L` gives
//!   `rhs - |r| <= row <= rhs`; on `G` gives `rhs <= row <= rhs + |r|`; on `E`
//!   gives `rhs <= row <= rhs + r` (`r >= 0`) or `rhs + r <= row <= rhs` (`r < 0`).
//! * `BOUNDS` types `UP`, `LO`, `FX`, `FR`, `MI`, `PL`, `BV`. A column with no
//!   explicit bound defaults to `0 <= x < +inf`, per the MPS convention.
//! * `MARKER` lines (`'MARKER' 'INTORG'`/`'INTEND'`) delimiting integer columns
//!   are recognized and skipped; the columns themselves are treated as ordinary
//!   continuous reals (no integer/bitvector theory yet — see spec Phase 5).
//! * Numbers are parsed exactly into [`Rational`] (decimal and `[eE]` exponent
//!   forms), never through floating point, matching the exact-math discipline
//!   used everywhere else in the suite.

use crate::parsers::smtlib2::LraProblem;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use tpt_solver_core::lra::LinConstraint;
use tpt_solver_core::rational::Rational;

/// Errors produced while parsing an MPS document.
#[derive(Debug)]
pub enum MpsError {
    /// A data line appeared before any section header selected a section.
    NoActiveSection,
    /// A `ROWS` line was not `<type> <name>`.
    BadRow(String),
    /// A `COLUMNS`/`RHS`/`RANGES` line had an odd number of trailing tokens (they
    /// come in `name value` pairs).
    OddPairCount(String),
    /// A `BOUNDS` line was malformed.
    BadBound(String),
    /// A row name referenced in `COLUMNS`/`RHS`/`RANGES` was never declared in `ROWS`.
    UnknownRow(String),
    /// A numeric field could not be parsed as an exact rational.
    BadNumber(String),
    /// The document had no `ROWS` section at all.
    NoRows,
}

impl fmt::Display for MpsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MpsError::NoActiveSection => write!(f, "MPS: data line before any section header"),
            MpsError::BadRow(l) => write!(f, "MPS: malformed ROWS line: {}", l),
            MpsError::OddPairCount(l) => write!(f, "MPS: odd number of name/value fields: {}", l),
            MpsError::BadBound(l) => write!(f, "MPS: malformed BOUNDS line: {}", l),
            MpsError::UnknownRow(r) => write!(f, "MPS: reference to undeclared row '{}'", r),
            MpsError::BadNumber(s) => write!(f, "MPS: invalid number '{}'", s),
            MpsError::NoRows => write!(f, "MPS: no ROWS section"),
        }
    }
}

impl Error for MpsError {}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RowKind {
    Free,
    Le,
    Ge,
    Eq,
}

#[derive(Clone, Copy)]
struct Bound {
    lo: Option<Rational>,
    hi: Option<Rational>,
}

impl Default for Bound {
    fn default() -> Bound {
        Bound {
            lo: Some(Rational::zero()),
            hi: None,
        }
    }
}

#[derive(Default)]
enum Section {
    #[default]
    None,
    Name,
    ObjSense,
    Rows,
    Columns,
    Rhs,
    Ranges,
    Bounds,
    Done,
}

/// Parse a free-format MPS document into an [`LraProblem`].
pub fn parse_mps(input: &str) -> Result<LraProblem, MpsError> {
    let mut section = Section::None;

    let mut row_order: Vec<String> = Vec::new();
    let mut row_kind: HashMap<String, RowKind> = HashMap::new();
    // Index into `constraint_rows` for each non-`N` row.
    let mut row_idx: HashMap<String, usize> = HashMap::new();
    let mut constraint_rows: Vec<RowKind> = Vec::new();
    let mut sparse: Vec<Vec<(usize, Rational)>> = Vec::new();
    let mut rhs_val: Vec<Rational> = Vec::new();
    let mut range_val: Vec<Option<Rational>> = Vec::new();

    let mut col_index: HashMap<String, usize> = HashMap::new();
    let mut col_order: Vec<String> = Vec::new();
    let mut bounds: HashMap<usize, Bound> = HashMap::new();

    for raw_line in input.lines() {
        let line = raw_line.split('$').next().unwrap_or("").trim_end();
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('*') {
            continue;
        }
        let toks: Vec<&str> = trimmed.split_whitespace().collect();

        // Section headers start at column 0; every data line is indented. This
        // distinguishes a real header from a data line whose *field* happens to
        // spell a keyword — e.g. the RHS/RANGES vector name or a bound set name is
        // conventionally the literal word "RHS"/"RNG"/"BND".
        let is_header_line = !line.starts_with(char::is_whitespace);
        if is_header_line {
            if let Some(next) = section_header(toks[0]) {
                section = next;
                continue;
            }
        }

        match section {
            Section::None => return Err(MpsError::NoActiveSection),
            Section::Name | Section::ObjSense | Section::Done => {
                // Free-format bodies we don't need for feasibility: the problem
                // name and MAX/MIN objective sense (this engine doesn't optimize).
            }
            Section::Rows => {
                if toks.len() != 2 {
                    return Err(MpsError::BadRow(trimmed.to_string()));
                }
                let kind = match toks[0].to_ascii_uppercase().as_str() {
                    "N" => RowKind::Free,
                    "L" => RowKind::Le,
                    "G" => RowKind::Ge,
                    "E" => RowKind::Eq,
                    _ => return Err(MpsError::BadRow(trimmed.to_string())),
                };
                let name = toks[1].to_string();
                row_kind.insert(name.clone(), kind);
                if kind != RowKind::Free {
                    row_idx.insert(name.clone(), constraint_rows.len());
                    constraint_rows.push(kind);
                    sparse.push(Vec::new());
                    rhs_val.push(Rational::zero());
                    range_val.push(None);
                }
                row_order.push(name);
            }
            Section::Columns => {
                if toks.len() >= 3 && toks[1] == "'MARKER'" {
                    // INTORG/INTEND delimit an integer column range; the columns
                    // themselves are still parsed normally as continuous reals
                    // (no integer/bitvector theory yet — see spec Phase 5).
                    continue;
                }
                if toks.len() < 3 || toks.len() % 2 == 0 {
                    return Err(MpsError::OddPairCount(trimmed.to_string()));
                }
                let col = *col_index.entry(toks[0].to_string()).or_insert_with(|| {
                    col_order.push(toks[0].to_string());
                    col_order.len() - 1
                });
                let mut i = 1;
                while i + 1 < toks.len() {
                    let row = toks[i];
                    let val = parse_number(toks[i + 1])?;
                    if let Some(&idx) = row_idx.get(row) {
                        sparse[idx].push((col, val));
                    } else if !row_kind.contains_key(row) {
                        return Err(MpsError::UnknownRow(row.to_string()));
                    } // else: coefficient on a free (`N`) row — dropped, no constraint to attach to.
                    i += 2;
                }
            }
            Section::Rhs => {
                if toks.len() < 3 || toks.len() % 2 == 0 {
                    return Err(MpsError::OddPairCount(trimmed.to_string()));
                }
                let mut i = 1;
                while i + 1 < toks.len() {
                    let row = toks[i];
                    let val = parse_number(toks[i + 1])?;
                    if let Some(&idx) = row_idx.get(row) {
                        rhs_val[idx] = val;
                    } else if !row_kind.contains_key(row) {
                        return Err(MpsError::UnknownRow(row.to_string()));
                    }
                    i += 2;
                }
            }
            Section::Ranges => {
                if toks.len() < 3 || toks.len() % 2 == 0 {
                    return Err(MpsError::OddPairCount(trimmed.to_string()));
                }
                let mut i = 1;
                while i + 1 < toks.len() {
                    let row = toks[i];
                    let val = parse_number(toks[i + 1])?;
                    match row_idx.get(row) {
                        Some(&idx) => range_val[idx] = Some(val),
                        None => return Err(MpsError::UnknownRow(row.to_string())),
                    }
                    i += 2;
                }
            }
            Section::Bounds => {
                if toks.len() < 3 {
                    return Err(MpsError::BadBound(trimmed.to_string()));
                }
                let btype = toks[0].to_ascii_uppercase();
                let col = *col_index.entry(toks[2].to_string()).or_insert_with(|| {
                    col_order.push(toks[2].to_string());
                    col_order.len() - 1
                });
                let b = bounds.entry(col).or_default();
                match btype.as_str() {
                    "UP" => {
                        let v = parse_bound_value(&toks, trimmed)?;
                        b.hi = Some(v);
                    }
                    "LO" => {
                        let v = parse_bound_value(&toks, trimmed)?;
                        b.lo = Some(v);
                    }
                    "FX" => {
                        let v = parse_bound_value(&toks, trimmed)?;
                        b.lo = Some(v);
                        b.hi = Some(v);
                    }
                    "FR" => {
                        b.lo = None;
                        b.hi = None;
                    }
                    "MI" => {
                        b.lo = None;
                    }
                    "PL" => {
                        b.hi = None;
                    }
                    "BV" => {
                        b.lo = Some(Rational::zero());
                        b.hi = Some(Rational::from_i64(1));
                    }
                    _ => return Err(MpsError::BadBound(trimmed.to_string())),
                }
            }
        }
    }

    if row_order.is_empty() {
        return Err(MpsError::NoRows);
    }

    let n = col_order.len();
    let mut constraints: Vec<LinConstraint> = Vec::new();

    for (i, kind) in constraint_rows.iter().enumerate() {
        let rhs = rhs_val[i];
        let (lo, hi) = row_bounds(*kind, rhs, range_val[i])?;
        let mut coeffs = vec![Rational::zero(); n];
        for &(col, val) in &sparse[i] {
            coeffs[col] = coeffs[col].add(val).ok_or_else(|| {
                MpsError::BadNumber("coefficient accumulation overflowed".to_string())
            })?;
        }
        if let Some(u) = hi {
            constraints.push(LinConstraint {
                coeffs: coeffs.clone(),
                rhs: u,
            });
        }
        if let Some(l) = lo {
            let neg: Vec<Rational> = coeffs.iter().map(|c| c.neg()).collect();
            constraints.push(LinConstraint {
                coeffs: neg,
                rhs: l.neg(),
            });
        }
    }

    // Variable bounds (default 0 <= x < +inf per the MPS convention).
    for col in 0..n {
        let b = bounds.get(&col).copied().unwrap_or_default();
        if let Some(u) = b.hi {
            let mut coeffs = vec![Rational::zero(); n];
            coeffs[col] = Rational::from_i64(1);
            constraints.push(LinConstraint { coeffs, rhs: u });
        }
        if let Some(l) = b.lo {
            let mut coeffs = vec![Rational::zero(); n];
            coeffs[col] = Rational::from_i64(-1);
            constraints.push(LinConstraint {
                coeffs,
                rhs: l.neg(),
            });
        }
    }

    Ok(LraProblem {
        vars: col_order,
        constraints,
    })
}

fn parse_bound_value(toks: &[&str], line: &str) -> Result<Rational, MpsError> {
    let raw = toks
        .get(3)
        .ok_or_else(|| MpsError::BadBound(line.to_string()))?;
    parse_number(raw)
}

/// `(lo, hi)` for a constraint row, folding in an optional `RANGES` entry. `Err`
/// only on exact-arithmetic overflow while combining the range into the bound.
fn row_bounds(
    kind: RowKind,
    rhs: Rational,
    range: Option<Rational>,
) -> Result<(Option<Rational>, Option<Rational>), MpsError> {
    let (mut lo, mut hi) = match kind {
        RowKind::Free => (None, None),
        RowKind::Le => (None, Some(rhs)),
        RowKind::Ge => (Some(rhs), None),
        RowKind::Eq => (Some(rhs), Some(rhs)),
    };
    let overflow = || MpsError::BadNumber("RANGES combination overflowed".to_string());
    if let Some(r) = range {
        let abs_r = if r.is_negative() { r.neg() } else { r };
        match kind {
            // L row: rhs - |r| <= row <= rhs.
            RowKind::Le => lo = Some(rhs.add(abs_r.neg()).ok_or_else(overflow)?),
            // G row: rhs <= row <= rhs + |r|.
            RowKind::Ge => hi = Some(rhs.add(abs_r).ok_or_else(overflow)?),
            // E row: [rhs, rhs + r] if r >= 0, else [rhs + r, rhs].
            RowKind::Eq => {
                let other = rhs.add(r).ok_or_else(overflow)?;
                if r.is_negative() {
                    lo = Some(other);
                } else {
                    hi = Some(other);
                }
            }
            RowKind::Free => {}
        }
    }
    Ok((lo, hi))
}

fn section_header(tok: &str) -> Option<Section> {
    Some(match tok.to_ascii_uppercase().as_str() {
        "NAME" => Section::Name,
        "OBJSENSE" => Section::ObjSense,
        "ROWS" => Section::Rows,
        "COLUMNS" => Section::Columns,
        "RHS" => Section::Rhs,
        "RANGES" => Section::Ranges,
        "BOUNDS" => Section::Bounds,
        "ENDATA" => Section::Done,
        _ => return None,
    })
}

/// Parse an MPS numeric field into an exact [`Rational`]: `[+-]?d+(.d+)?([eE][+-]?d+)?`.
fn parse_number(s: &str) -> Result<Rational, MpsError> {
    let bad = || MpsError::BadNumber(s.to_string());
    let (mantissa, exp) = match s.split_once(['e', 'E']) {
        Some((m, e)) => (m, e.parse::<i32>().map_err(|_| bad())?),
        None => (s, 0),
    };
    let (sign, body) = match mantissa.strip_prefix('-') {
        Some(b) => (-1i128, b),
        None => (1i128, mantissa.strip_prefix('+').unwrap_or(mantissa)),
    };
    let (intpart, fracpart) = match body.split_once('.') {
        Some((i, f)) => (i, f),
        None => (body, ""),
    };
    if intpart.is_empty() && fracpart.is_empty() {
        return Err(bad());
    }
    let intval: i128 = if intpart.is_empty() {
        0
    } else {
        intpart.parse().map_err(|_| bad())?
    };
    let fracval: i128 = if fracpart.is_empty() {
        0
    } else {
        fracpart.parse().map_err(|_| bad())?
    };
    let frac_scale = pow10(fracpart.len() as u32).ok_or_else(bad)?;
    let num = sign
        .checked_mul(
            intval
                .checked_mul(frac_scale)
                .ok_or_else(bad)?
                .checked_add(fracval)
                .ok_or_else(bad)?,
        )
        .ok_or_else(bad)?;
    let mut r = Rational::new(num, frac_scale).ok_or_else(bad)?;
    if exp > 0 {
        let scale = pow10(exp as u32).ok_or_else(bad)?;
        r = r
            .mul(Rational::new(scale, 1).ok_or_else(bad)?)
            .ok_or_else(bad)?;
    } else if exp < 0 {
        let scale = pow10((-exp) as u32).ok_or_else(bad)?;
        r = r
            .checked_div(Rational::new(scale, 1).ok_or_else(bad)?)
            .ok_or_else(bad)?;
    }
    Ok(r)
}

fn pow10(n: u32) -> Option<i128> {
    let mut v: i128 = 1;
    for _ in 0..n {
        v = v.checked_mul(10)?;
    }
    Some(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::solve_and_check_lra;
    use tpt_solver_core::engine::SolveResult;

    const FEASIBLE: &str = "\
NAME          TEST
ROWS
 N  COST
 L  LIM1
 G  LIM2
COLUMNS
    X1        COST      1.0        LIM1      1.0
    X1        LIM2      1.0
    X2        COST      2.0        LIM1      1.0
    X2        LIM2      1.0
RHS
    RHS       LIM1      10.0       LIM2      1.0
BOUNDS
ENDATA
";

    #[test]
    fn parses_feasible_lp() {
        // 0<=x1,x2 ; x1+x2<=10 ; x1+x2>=1  -- trivially feasible, e.g. x1=x2=0 fails
        // the >=1 bound, but x1=1,x2=0 works.
        let prob = parse_mps(FEASIBLE).unwrap();
        assert_eq!(prob.vars, vec!["X1", "X2"]);
        let (claim, verdict) = solve_and_check_lra(&prob.constraints, 1_000_000);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn infeasible_when_bounds_conflict() {
        let input = "\
ROWS
 N  COST
 G  LOWER
 L  UPPER
COLUMNS
    X         COST      1.0        LOWER     1.0
    X         UPPER     1.0
RHS
    RHS       LOWER     5.0        UPPER     1.0
ENDATA
";
        // x >= 5 and x <= 1 is infeasible.
        let prob = parse_mps(input).unwrap();
        let (claim, verdict) = solve_and_check_lra(&prob.constraints, 1_000_000);
        assert_eq!(claim, SolveResult::Unsat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn fx_bound_pins_variable() {
        let input = "\
ROWS
 N  COST
 G  ATLEAST
COLUMNS
    X         COST      1.0        ATLEAST   1.0
RHS
    RHS       ATLEAST   3.0
BOUNDS
 FX BND       X         3.0
ENDATA
";
        let prob = parse_mps(input).unwrap();
        let (claim, verdict) = solve_and_check_lra(&prob.constraints, 1_000_000);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn free_variable_has_no_default_nonnegativity() {
        let input = "\
ROWS
 N  COST
 E  FIX
COLUMNS
    X         COST      1.0        FIX       1.0
RHS
    RHS       FIX       -5.0
BOUNDS
 FR BND       X
ENDATA
";
        // Without FR, the default x >= 0 would make x = -5 infeasible.
        let prob = parse_mps(input).unwrap();
        let (claim, verdict) = solve_and_check_lra(&prob.constraints, 1_000_000);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn range_narrows_le_row() {
        let input = "\
ROWS
 N  COST
 L  ROW
COLUMNS
    X         COST      1.0        ROW       1.0
RHS
    RHS       ROW       10.0
RANGES
    RNG       ROW       4.0
BOUNDS
 FR BND       X
ENDATA
";
        // L row with rhs=10, range=4 => 6 <= x <= 10.
        let prob = parse_mps(input).unwrap();
        assert_eq!(prob.constraints.len(), 2);
        let (claim, verdict) = solve_and_check_lra(&prob.constraints, 1_000_000);
        assert_eq!(claim, SolveResult::Sat);
        assert!(verdict.is_accept());

        // Exact bound check: [6, 10] is feasible, but pinning x to 5 (just below
        // the narrowed lower bound) must be infeasible, and x to 11 (just above
        // the narrowed upper bound) must be infeasible too.
        let with_extra = |extra: LinConstraint| {
            let mut cons = prob.constraints.clone();
            cons.push(extra);
            solve_and_check_lra(&cons, 1_000_000).0
        };
        let pin = |v: i64| LinConstraint {
            coeffs: vec![Rational::from_i64(1)],
            rhs: Rational::from_i64(v),
        };
        let pin_min = |v: i64| LinConstraint {
            coeffs: vec![Rational::from_i64(-1)],
            rhs: Rational::from_i64(-v),
        };
        assert_eq!(
            with_extra(pin(5)),
            SolveResult::Unsat,
            "x=5 is below [6,10]"
        );
        assert_eq!(
            with_extra(pin_min(11)),
            SolveResult::Unsat,
            "x=11 is above [6,10]"
        );
        assert_eq!(
            with_extra(pin(6)),
            SolveResult::Sat,
            "x=6 is the lower edge"
        );
        assert_eq!(
            with_extra(pin(10)),
            SolveResult::Sat,
            "x=10 is the upper edge"
        );
    }

    #[test]
    fn exponent_and_decimal_numbers_parse_exactly() {
        assert_eq!(parse_number("1.5").unwrap(), Rational::new(3, 2).unwrap());
        assert_eq!(parse_number("1.5e2").unwrap(), Rational::from_i64(150));
        assert_eq!(
            parse_number("-2E-1").unwrap(),
            Rational::new(-1, 5).unwrap()
        );
        assert_eq!(parse_number("3").unwrap(), Rational::from_i64(3));
    }

    #[test]
    fn unknown_row_is_rejected() {
        let input = "\
ROWS
 N  COST
COLUMNS
    X         COST      1.0        GHOST     1.0
ENDATA
";
        assert!(matches!(
            parse_mps(input),
            Err(MpsError::UnknownRow(r)) if r == "GHOST"
        ));
    }

    #[test]
    fn missing_rows_section_is_rejected() {
        assert!(matches!(parse_mps("ENDATA\n"), Err(MpsError::NoRows)));
    }

    #[test]
    fn garbage_before_section_header_is_rejected() {
        assert!(matches!(
            parse_mps("garbage line\nENDATA\n"),
            Err(MpsError::NoActiveSection)
        ));
    }
}
