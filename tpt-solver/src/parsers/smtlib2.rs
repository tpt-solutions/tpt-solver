//! SMT-LIB2 parser (QF_LRA / QF_LIA / QF_SAT subset).
//!
//! This implements the parser half of the Phase 4 periphery. Parsers are the fuzzing
//! surface of the suite, so the reader here is written to fail safely (a typed
//! [`SmtError`]) on malformed or out-of-subset input rather than panicking, and it is
//! paired with a `cargo-fuzz` target under `fuzz/`.
//!
//! ## Supported subset
//!
//! * Commands: `set-logic`, `set-option`, `declare-fun`/`declare-const`,
//!   `assert`, `check-sat`, `get-model`, `exit`, `push`/`pop` (accepted/no-op),
//!   `reset`.
//! * Boolean connectives `and or not => xor ite` and comparison `= < <= > >=`
//!   (strict `<`/`>` are treated as their non-strict counterparts — a documented
//!   limitation of exact rational arithmetic over the reals).
//! * Arithmetic `+ - * /` where `*`/`/` take a constant numeric operand, so the term
//!   stays *linear* (QF_LRA). Integer-sorted variables are handled as reals.
//!
//! ## Two compilation targets
//!
//! * [`Script::to_lra`] flattens a conjunction of linear comparisons into
//!   [`LinConstraint`]s and solves via Fourier–Motzkin (UNSAT, Farkas-certified) and
//!   Simplex (SAT model, re-checked by the kernel). Disjunctions/non-linear terms
//!   yield [`SmtError::Unsupported`].
//! * [`Script::to_cnf`] Tseitin-encodes a *propositional* formula into a DIMACS-style
//!   [`Problem`] for the CDCL engine (non-arithmetic QF_SAT).

use crate::reference::Problem;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use tpt_solver_core::array::{ArrAssertion, ArrayExpr, ElemExpr};
use tpt_solver_core::bv::BvAssertion;
use tpt_solver_core::bv::BvTerm;
use tpt_solver_core::lra::LinConstraint;
use tpt_solver_core::rational::Rational;

/// Errors produced while parsing or lowering an SMT-LIB2 script.
#[derive(Debug)]
pub enum SmtError {
    /// A lexical or structural parse failure (unbalanced parentheses, etc.).
    Parse(String),
    /// The input uses a feature outside the supported subset.
    Unsupported(String),
    /// A term had the wrong arity for its operator.
    BadArity(String),
    /// A numeric literal could not be read as an exact rational.
    BadNumber(String),
    /// The script contained no `assert` commands.
    NoAsserts,
}

impl fmt::Display for SmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtError::Parse(s) => write!(f, "SMT-LIB2 parse error: {}", s),
            SmtError::Unsupported(s) => write!(f, "SMT-LIB2 unsupported feature: {}", s),
            SmtError::BadArity(s) => write!(f, "SMT-LIB2 bad arity: {}", s),
            SmtError::BadNumber(s) => write!(f, "SMT-LIB2 bad number: {}", s),
            SmtError::NoAsserts => write!(f, "SMT-LIB2: no asserted formulas"),
        }
    }
}

impl Error for SmtError {}

// ---------------------------------------------------------------------------
// Tokenizer
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    LParen,
    RParen,
    Atom(String),
}

fn tokenize(input: &str) -> Result<Vec<Tok>, SmtError> {
    let bytes: Vec<char> = input.chars().collect();
    let mut toks = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c == ';' {
            // Line comment: skip to end of line.
            while i < bytes.len() && bytes[i] != '\n' {
                i += 1;
            }
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '(' {
            toks.push(Tok::LParen);
            i += 1;
            continue;
        }
        if c == ')' {
            toks.push(Tok::RParen);
            i += 1;
            continue;
        }
        // An atom: read until whitespace, '(', ')' or ';'.
        let start = i;
        while i < bytes.len() {
            let d = bytes[i];
            if d.is_whitespace() || d == '(' || d == ')' || d == ';' {
                break;
            }
            i += 1;
        }
        if i == start {
            return Err(SmtError::Parse(format!("unexpected character '{}'", c)));
        }
        toks.push(Tok::Atom(bytes[start..i].iter().collect()));
    }
    Ok(toks)
}

// ---------------------------------------------------------------------------
// S-expression AST
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn parse_sexps(toks: &[Tok], pos: &mut usize) -> Result<Vec<Sexp>, SmtError> {
    let mut out = Vec::new();
    while *pos < toks.len() {
        match &toks[*pos] {
            Tok::RParen => break,
            Tok::LParen => {
                *pos += 1;
                let list = parse_sexps(toks, pos)?;
                // Consume the matching ')'.
                if *pos >= toks.len() || !matches!(toks[*pos], Tok::RParen) {
                    return Err(SmtError::Parse("unbalanced '('".into()));
                }
                *pos += 1;
                out.push(Sexp::List(list));
            }
            Tok::Atom(a) => {
                out.push(Sexp::Atom(a.clone()));
                *pos += 1;
            }
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Term AST
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Op {
    And,
    Or,
    Not,
    Imp,
    Xor,
    Ite,
    Eq,
    Distinct,
    Le,
    Lt,
    Ge,
    Gt,
    Add,
    Sub,
    Mul,
    Div,
    // Bit-vector operators (QF_BV subset; see `Script::to_bv`).
    BvNot,
    BvNeg,
    BvAnd,
    BvOr,
    BvXor,
    BvAdd,
    BvSub,
    /// Logical left shift; the amount must be a constant literal.
    BvShl,
    /// Logical right shift; the amount must be a constant literal.
    BvLShr,
    /// Unsigned less-than.
    BvUlt,
    Concat,
    Select,
    Store,
    Other,
}

/// An extraction with its inclusive bit range `hi..=lo`, from the indexed
/// operator form `((_ extract i j) t)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ExtractRange {
    pub hi: u32,
    pub lo: u32,
}

#[derive(Debug, Clone)]
pub(crate) enum Term {
    Bool(bool),
    Num(Rational),
    /// A bit-vector constant with its width (from `#x..` / `#b..` literals).
    BvLit(u64, u8),
    Sym(String),
    App(Op, Vec<Term>),
    /// `((_ extract hi lo) t)` — carries the bit range Op cannot.
    Extract(ExtractRange, Box<Term>),
    /// `((as const (Array S T)) v)` — the all-`v` constant array.
    ConstArray(Box<Term>),
}

fn op_from_str(s: &str) -> Option<Op> {
    Some(match s {
        "and" => Op::And,
        "or" => Op::Or,
        "not" => Op::Not,
        "=>" => Op::Imp,
        "xor" => Op::Xor,
        "ite" => Op::Ite,
        "=" => Op::Eq,
        "distinct" => Op::Distinct,
        "<=" => Op::Le,
        "<" => Op::Lt,
        ">=" => Op::Ge,
        ">" => Op::Gt,
        "+" => Op::Add,
        "-" => Op::Sub,
        "*" => Op::Mul,
        "/" => Op::Div,
        "bvnot" => Op::BvNot,
        "bvneg" => Op::BvNeg,
        "bvand" => Op::BvAnd,
        "bvor" => Op::BvOr,
        "bvxor" => Op::BvXor,
        "bvadd" => Op::BvAdd,
        "bvsub" => Op::BvSub,
        "bvshl" => Op::BvShl,
        "bvlshr" => Op::BvLShr,
        "bvult" => Op::BvUlt,
        "concat" => Op::Concat,
        "select" => Op::Select,
        "store" => Op::Store,
        _ => return None,
    })
}

fn sexp_to_term(s: &Sexp) -> Result<Term, SmtError> {
    match s {
        Sexp::Atom(a) => Ok(atom_to_term(a)),
        Sexp::List(items) => {
            if items.is_empty() {
                return Err(SmtError::Parse("empty application ()".into()));
            }
            // Indexed / qualified operator forms, whose head is itself a list:
            //   ((_ extract hi lo) t)      — bit-range extraction
            //   ((as const (Array S T)) v) — a constant array
            if let Sexp::List(head) = &items[0] {
                if let Some(Sexp::Atom(tag)) = head.first() {
                    match tag.as_str() {
                        "_" => {
                            if let Some(Sexp::Atom(kind)) = head.get(1) {
                                if kind == "extract" {
                                    let hi = parse_index(head.get(2), 2)?;
                                    let lo = parse_index(head.get(3), 3)?;
                                    if items.len() != 2 {
                                        return Err(SmtError::BadArity(
                                            "extract expects exactly 1 argument".into(),
                                        ));
                                    }
                                    let arg = sexp_to_term(&items[1])?;
                                    return Ok(Term::Extract(
                                        ExtractRange { hi, lo },
                                        Box::new(arg),
                                    ));
                                }
                            }
                            return Err(SmtError::Unsupported(format!(
                                "unknown indexed operator {:?}",
                                head
                            )));
                        }
                        "as" => {
                            // ((as const (Array S T)) v): a constant array.
                            let is_const_array = matches!(head.get(1), Some(Sexp::Atom(a)) if a == "const");
                            if is_const_array {
                                if items.len() != 2 {
                                    return Err(SmtError::BadArity(
                                        "const array expects exactly 1 value".into(),
                                    ));
                                }
                                let v = sexp_to_term(&items[1])?;
                                return Ok(Term::ConstArray(Box::new(v)));
                            }
                            return Err(SmtError::Unsupported(format!(
                                "unknown qualified symbol {:?}",
                                head
                            )));
                        }
                        _ => {
                            return Err(SmtError::Unsupported(format!(
                                "unknown application head {:?}",
                                head
                            )))
                        }
                    }
                }
                return Err(SmtError::Parse("application head is not a symbol".into()));
            }
            if let Sexp::Atom(head) = &items[0] {
                if let Some(op) = op_from_str(head) {
                    let mut args = Vec::with_capacity(items.len() - 1);
                    for a in &items[1..] {
                        args.push(sexp_to_term(a)?);
                    }
                    return Ok(Term::App(op, args));
                }
                // Application of a user-defined symbol to arguments.
                let mut args = Vec::with_capacity(items.len() - 1);
                for a in &items[1..] {
                    args.push(sexp_to_term(a)?);
                }
                return Ok(Term::App(Op::Other, args));
            }
            Err(SmtError::Parse("application head is not a symbol".into()))
        }
    }
}

fn atom_to_term(a: &str) -> Term {
    match a {
        "true" => Term::Bool(true),
        "false" => Term::Bool(false),
        _ => {
            if let Some(lit) = parse_bv_literal(a) {
                return lit;
            }
            if is_numeral(a) {
                match parse_rational(a) {
                    Some(r) => Term::Num(r),
                    None => Term::Sym(a.to_string()),
                }
            } else {
                Term::Sym(a.to_string())
            }
        }
    }
}

/// Parse `#b0101` / `#xAB` bit-vector literals into `(value, width)`.
/// Widths above 64 bits are out of subset (`None`, surfacing as an unknown
/// symbol and later [`SmtError::Unsupported`]).
fn parse_bv_literal(a: &str) -> Option<Term> {
    let (val, width) = if let Some(hex) = a.strip_prefix("#x") {
        if hex.is_empty() || hex.len() > 16 {
            return None;
        }
        (u64::from_str_radix(hex, 16).ok()?, (hex.len() * 4) as u8)
    } else if let Some(bin) = a.strip_prefix("#b") {
        if bin.is_empty() || bin.len() > 64 {
            return None;
        }
        (u64::from_str_radix(bin, 2).ok()?, bin.len() as u8)
    } else {
        return None;
    };
    Some(Term::BvLit(val, width))
}

/// Parse a non-negative decimal index used by indexed operators.
fn parse_index(s: Option<&Sexp>, pos: usize) -> Result<u32, SmtError> {
    match s {
        Some(Sexp::Atom(a)) => a
            .parse::<u32>()
            .map_err(|_| SmtError::Parse(format!("bad index at position {}: {:?}", pos, a))),
        _ => Err(SmtError::Parse(format!("missing index at position {}", pos))),
    }
}

fn is_numeral(a: &str) -> bool {
    let trimmed = a.strip_prefix('-').unwrap_or(a);
    let trimmed = trimmed.strip_prefix('+').unwrap_or(trimmed);
    if trimmed.is_empty() {
        return false;
    }
    let mut saw_dot = false;
    for ch in trimmed.chars() {
        if ch == '.' {
            if saw_dot {
                return false;
            }
            saw_dot = true;
        } else if !ch.is_ascii_digit() {
            return false;
        }
    }
    true
}

fn parse_rational(a: &str) -> Option<Rational> {
    let (sign, body) = match a.strip_prefix('-') {
        Some(b) => (-1i128, b),
        None => (1, a.strip_prefix('+').unwrap_or(a)),
    };
    let (intpart, fracpart) = match body.split_once('.') {
        Some((i, f)) => (i, Some(f)),
        None => (body, None),
    };
    let intval: i128 = intpart.parse().ok()?;
    let (fracval, scale) = match fracpart {
        Some(f) if !f.is_empty() => {
            let fv: i128 = f.parse().ok()?;
            let flen = f.len() as u32;
            let scl = pow10(flen)?;
            (fv, scl)
        }
        _ => (0, 1),
    };
    let num = sign.checked_mul(intval.checked_mul(scale)?.checked_add(fracval)?)?;
    Rational::new(num, scale)
}

fn pow10(n: u32) -> Option<i128> {
    let mut v = 1i128;
    for _ in 0..n {
        v = v.checked_mul(10)?;
    }
    Some(v)
}

// ---------------------------------------------------------------------------
// Script
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Sort {
    Bool,
    Real,
    Int,
    /// `(_ BitVec n)` with `n <= 64`.
    BitVec(u32),
    /// `(Array S T)` — element universe is the suite's `u64` regardless of S/T
    /// (a documented limitation of the QF_AX subset).
    Array,
}

fn parse_sort(s: &Sexp) -> Option<Sort> {
    match s {
        Sexp::Atom(a) => match a.as_str() {
            "Bool" => Some(Sort::Bool),
            "Real" => Some(Sort::Real),
            "Int" => Some(Sort::Int),
            _ => None,
        },
        Sexp::List(items) => {
            // (_ BitVec n)
            if matches!(items.first(), Some(Sexp::Atom(a)) if a == "_") {
                if let (Some(Sexp::Atom(k)), Some(Sexp::Atom(w))) = (items.get(1), items.get(2)) {
                    if k == "BitVec" {
                        return w.parse::<u32>().ok().map(Sort::BitVec);
                    }
                }
                return None;
            }
            // (Array S T)
            if matches!(items.first(), Some(Sexp::Atom(a)) if a == "Array") && items.len() == 3 {
                return Some(Sort::Array);
            }
            None
        }
    }
}

#[derive(Debug, Clone)]
struct Decl {
    name: String,
    sort: Sort,
}

/// A parsed SMT-LIB2 script: the logic, declared symbols, and asserted formulas.
#[derive(Debug, Clone, Default)]
pub struct Script {
    pub logic: Option<String>,
    decls: Vec<Decl>,
    asserts: Vec<Term>,
}

impl Script {
    /// The number of declared symbols.
    pub fn decl_count(&self) -> usize {
        self.decls.len()
    }

    /// The number of asserted formulas.
    pub fn assert_count(&self) -> usize {
        self.asserts.len()
    }

    /// Lower to a QF_LRA problem: a conjunction of linear `<=` constraints.
    ///
    /// Returns [`SmtError::Unsupported`] if any asserted sub-formula is not a
    /// conjunction of linear comparisons (e.g. it contains a disjunction or a
    /// non-linear term).
    pub fn to_lra(&self) -> Result<LraProblem, SmtError> {
        let mut ctx = LraCtx::default();
        for d in &self.decls {
            if matches!(d.sort, Sort::Real | Sort::Int) {
                ctx.intern(&d.name);
            }
        }
        let combined = self.combined_asserts()?;
        let mut constraints = Vec::new();
        collect_constraints(&combined, &mut ctx, &mut constraints)?;
        // Pad every constraint to a uniform variable count.
        let n = constraints
            .iter()
            .map(|c| c.coeffs.len())
            .max()
            .unwrap_or(0);
        for c in &mut constraints {
            c.coeffs.resize(n, Rational::zero());
        }
        Ok(LraProblem {
            vars: ctx.vars,
            constraints,
        })
    }

    /// Lower to a propositional CNF problem via Tseitin encoding.
    ///
    /// Returns [`SmtError::Unsupported`] if any asserted formula contains an
    /// arithmetic comparison (use [`Script::to_lra`] for those).
    pub fn to_cnf(&self) -> Result<Problem, SmtError> {
        let combined = self.combined_asserts()?;
        // E-graph preprocessing (spec §4.3, §7): simplify the Boolean formula via
        // equality saturation before Tseitin encoding it. This is untrusted
        // preprocessing like the rest of the pipeline; see `egraph` module docs for
        // why that's safe and how it's checked.
        let simplified = crate::egraph::simplify_boolean(&combined)?;
        let mut enc = Encoder::default();
        for d in &self.decls {
            if matches!(d.sort, Sort::Bool) {
                enc.intern_bool(&d.name);
            }
        }
        let root = enc.encode(&simplified, true)?;
        enc.add_clause(vec![root]);
        Ok(Problem {
            var_count: enc.next_var,
            clauses: enc.clauses,
        })
    }

    /// Lower to a QF_BV problem: a conjunction of bit-vector equalities and
    /// unsigned `<` over the fixed-width fragment the core's bit-blaster
    /// supports.
    ///
    /// Returns [`SmtError::Unsupported`] for disjunctions, shifts by
    /// non-constant amounts, widths above 64, or any term outside the
    /// fragment.
    pub fn to_bv(&self) -> Result<BvProblem, SmtError> {
        let mut ctx = BvCtx::default();
        for d in &self.decls {
            if let Sort::BitVec(w) = d.sort {
                if w == 0 || w > 64 {
                    return Err(SmtError::Unsupported(format!(
                        "bit-vector width {} out of the supported 1..=64",
                        w
                    )));
                }
                ctx.intern(&d.name, w as u8);
            }
        }
        let combined = self.combined_asserts()?;
        let mut assertions = Vec::new();
        collect_bv_assertions(&combined, &mut ctx, &mut assertions)?;
        Ok(BvProblem {
            var_count: ctx.vars.len() as u32,
            names: ctx.names(),
            assertions,
        })
    }

    /// Lower to a QF_AX problem: a conjunction of ground equalities between
    /// element terms (`var`/const/`select`) and array terms
    /// (`avar`/`store`/constant arrays).
    ///
    /// The element universe is non-negative 64-bit integers regardless of the
    /// declared index/value sorts — a documented limitation of this subset.
    pub fn to_array(&self) -> Result<ArrayProblem, SmtError> {
        let mut ctx = AxParserCtx::default();
        // Element variables first (dense ids in declaration order), then
        // array variables.
        for d in &self.decls {
            if matches!(d.sort, Sort::Int | Sort::Real) {
                ctx.intern_elem(&d.name);
            }
        }
        for d in &self.decls {
            if matches!(d.sort, Sort::Array) {
                ctx.intern_arr(&d.name);
            }
        }
        let combined = self.combined_asserts()?;
        let mut assertions = Vec::new();
        collect_ax_assertions(&combined, &mut ctx, &mut assertions)?;
        Ok(ArrayProblem {
            avar_count: ctx.avars.len() as u32,
            evar_count: ctx.evars.len() as u32,
            avars: ctx.avars,
            evars: ctx.evars,
            assertions,
        })
    }

    /// Combine all asserted formulas into a single `and`.
    fn combined_asserts(&self) -> Result<Term, SmtError> {
        if self.asserts.is_empty() {
            return Err(SmtError::NoAsserts);
        }
        Ok(Term::App(Op::And, self.asserts.to_vec()))
    }
}

/// A linear-arithmetic problem in `<=` form, ready for the core's FM/Simplex engine.
#[derive(Debug, Clone)]
pub struct LraProblem {
    /// Variable names, in column order.
    pub vars: Vec<String>,
    /// Constraints `Σ coeffs[i]·x_i <= rhs`.
    pub constraints: Vec<LinConstraint>,
}

impl LraProblem {
    /// The number of variables.
    pub fn var_count(&self) -> usize {
        self.vars.len()
    }
}

// ---------------------------------------------------------------------------
// LRA lowering
// ---------------------------------------------------------------------------

#[derive(Default)]
struct LraCtx {
    vars: Vec<String>,
    idx: HashMap<String, usize>,
}

impl LraCtx {
    fn intern(&mut self, name: &str) -> usize {
        if let Some(&i) = self.idx.get(name) {
            return i;
        }
        let i = self.vars.len();
        self.vars.push(name.to_string());
        self.idx.insert(name.to_string(), i);
        i
    }
}

/// A linear expression: coefficients per variable plus a constant term.
struct Linear {
    coeffs: Vec<Rational>,
    constant: Rational,
}

fn collect_constraints(
    term: &Term,
    ctx: &mut LraCtx,
    out: &mut Vec<LinConstraint>,
) -> Result<(), SmtError> {
    match term {
        Term::App(Op::And, args) => {
            for a in args {
                collect_constraints(a, ctx, out)?;
            }
            Ok(())
        }
        Term::App(Op::Not, args) => {
            if args.len() != 1 {
                return Err(SmtError::BadArity("not expects 1 argument".into()));
            }
            negate_comparison(&args[0], ctx, out)
        }
        Term::App(Op::Le, args) => mk_cmp(args, ctx, out, CmpDir::Le),
        Term::App(Op::Lt, args) => {
            // Strict inequality is approximated by its non-strict form.
            mk_cmp(args, ctx, out, CmpDir::Le)
        }
        Term::App(Op::Ge, args) => mk_cmp(args, ctx, out, CmpDir::Ge),
        Term::App(Op::Gt, args) => mk_cmp(args, ctx, out, CmpDir::Ge),
        Term::App(Op::Eq, args) => {
            // a = b  =>  a <= b  and  b <= a
            mk_cmp(args, ctx, out, CmpDir::Le)?;
            mk_cmp(args, ctx, out, CmpDir::Ge)
        }
        _ => Err(SmtError::Unsupported(
            "LRA lowering supports only conjunctions of linear comparisons".into(),
        )),
    }
}

enum CmpDir {
    Le,
    Ge,
}

fn mk_cmp(
    args: &[Term],
    ctx: &mut LraCtx,
    out: &mut Vec<LinConstraint>,
    dir: CmpDir,
) -> Result<(), SmtError> {
    if args.len() != 2 {
        return Err(SmtError::BadArity("comparison expects 2 arguments".into()));
    }
    let p = linear(&args[0], ctx)?;
    let q = linear(&args[1], ctx)?;
    let n = p.coeffs.len().max(q.coeffs.len());
    let mut pc = p.coeffs;
    let mut qc = q.coeffs;
    pc.resize(n, Rational::zero());
    qc.resize(n, Rational::zero());
    let coeffs = match dir {
        CmpDir::Le => sub_vec(&pc, &qc),
        CmpDir::Ge => sub_vec(&qc, &pc),
    };
    let rhs = match dir {
        CmpDir::Le => q
            .constant
            .add(p.constant.neg())
            .ok_or_else(|| SmtError::BadNumber("arithmetic overflow".into()))?,
        CmpDir::Ge => p
            .constant
            .add(q.constant.neg())
            .ok_or_else(|| SmtError::BadNumber("arithmetic overflow".into()))?,
    };
    out.push(LinConstraint { coeffs, rhs });
    Ok(())
}

fn negate_comparison(
    term: &Term,
    ctx: &mut LraCtx,
    out: &mut Vec<LinConstraint>,
) -> Result<(), SmtError> {
    // not(a R b) where R in {<=,<,>=,>}. With the strict->non-strict approximation:
    //   not(a <= b) = a > b  =>  b <= a
    //   not(a >= b) = a < b  =>  a <= b
    match term {
        Term::App(Op::Le, a) | Term::App(Op::Lt, a) => mk_cmp(a, ctx, out, CmpDir::Ge),
        Term::App(Op::Ge, a) | Term::App(Op::Gt, a) => mk_cmp(a, ctx, out, CmpDir::Le),
        Term::App(Op::Eq, a) => {
            // not(a = b): a < b or a > b  =>  a disjunction, unsupported in pure LRA.
            let _ = a;
            Err(SmtError::Unsupported(
                "negated equality is a disjunction; not supported by the LRA subset".into(),
            ))
        }
        _ => Err(SmtError::Unsupported(
            "negation of a non-comparison is not supported by the LRA subset".into(),
        )),
    }
}

fn linear(term: &Term, ctx: &mut LraCtx) -> Result<Linear, SmtError> {
    match term {
        Term::Num(r) => Ok(Linear {
            coeffs: Vec::new(),
            constant: *r,
        }),
        Term::Sym(name) => {
            let i = ctx.intern(name);
            let mut coeffs = vec![Rational::zero(); i + 1];
            coeffs[i] = Rational::from_i64(1);
            Ok(Linear {
                coeffs,
                constant: Rational::zero(),
            })
        }
        Term::App(Op::Add, args) => {
            let mut coeffs = Vec::new();
            let mut constant = Rational::zero();
            for a in args {
                let l = linear(a, ctx)?;
                let n = coeffs.len().max(l.coeffs.len());
                coeffs.resize(n, Rational::zero());
                for (i, c) in l.coeffs.iter().enumerate() {
                    coeffs[i] = coeffs[i]
                        .add(*c)
                        .ok_or_else(|| SmtError::BadNumber("arithmetic overflow".into()))?;
                }
                constant = constant
                    .add(l.constant)
                    .ok_or_else(|| SmtError::BadNumber("arithmetic overflow".into()))?;
            }
            Ok(Linear { coeffs, constant })
        }
        Term::App(Op::Sub, args) => {
            if args.is_empty() {
                return Err(SmtError::BadArity("'-' needs >=1 argument".into()));
            }
            let mut acc = linear(&args[0], ctx)?;
            if args.len() == 1 {
                // unary minus
                for c in acc.coeffs.iter_mut() {
                    *c = c.neg();
                }
                acc.constant = acc.constant.neg();
                return Ok(acc);
            }
            for a in &args[1..] {
                let l = linear(a, ctx)?;
                let n = acc.coeffs.len().max(l.coeffs.len());
                acc.coeffs.resize(n, Rational::zero());
                for (i, c) in l.coeffs.iter().enumerate() {
                    acc.coeffs[i] = acc.coeffs[i]
                        .add(c.neg())
                        .ok_or_else(|| SmtError::BadNumber("arithmetic overflow".into()))?;
                }
                acc.constant = acc
                    .constant
                    .add(l.constant.neg())
                    .ok_or_else(|| SmtError::BadNumber("arithmetic overflow".into()))?;
            }
            Ok(acc)
        }
        Term::App(Op::Mul, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("'*' expects 2 arguments".into()));
            }
            match (&args[0], &args[1]) {
                (Term::Num(r), other) | (other, Term::Num(r)) => {
                    let l = linear(other, ctx)?;
                    let coeffs = l
                        .coeffs
                        .iter()
                        .map(|c| c.mul(*r))
                        .collect::<Option<Vec<_>>>()
                        .ok_or_else(|| SmtError::BadNumber("multiplication overflow".into()))?;
                    let constant = l
                        .constant
                        .mul(*r)
                        .ok_or_else(|| SmtError::BadNumber("multiplication overflow".into()))?;
                    Ok(Linear { coeffs, constant })
                }
                _ => Err(SmtError::Unsupported(
                    "non-linear multiplication is not supported".into(),
                )),
            }
        }
        Term::App(Op::Div, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("'/' expects 2 arguments".into()));
            }
            let denom = match &args[1] {
                Term::Num(r) if !r.is_zero() => *r,
                Term::Num(_) => return Err(SmtError::BadNumber("division by zero".into())),
                _ => {
                    return Err(SmtError::Unsupported(
                        "division by a non-constant is not supported".into(),
                    ))
                }
            };
            let inv = Rational::from_i64(1)
                .checked_div(denom)
                .ok_or_else(|| SmtError::BadNumber("division overflow".into()))?;
            let l = linear(&args[0], ctx)?;
            let coeffs = l
                .coeffs
                .iter()
                .map(|c| c.mul(inv))
                .collect::<Option<Vec<_>>>()
                .ok_or_else(|| SmtError::BadNumber("division overflow".into()))?;
            let constant = l
                .constant
                .mul(inv)
                .ok_or_else(|| SmtError::BadNumber("division overflow".into()))?;
            Ok(Linear { coeffs, constant })
        }
        _ => Err(SmtError::Unsupported(
            "term is not a linear arithmetic expression".into(),
        )),
    }
}

fn sub_vec(a: &[Rational], b: &[Rational]) -> Vec<Rational> {
    let n = a.len().max(b.len());
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let x = a.get(i).copied().unwrap_or_else(Rational::zero);
        let y = b.get(i).copied().unwrap_or_else(Rational::zero);
        out.push(x.add(y.neg()).expect("sub_vec: overflow"));
    }
    out
}

// ---------------------------------------------------------------------------
// SAT (Tseitin) lowering
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Encoder {
    clauses: Vec<Vec<i32>>,
    next_var: u32,
    bool_vars: HashMap<String, i32>,
}

impl Encoder {
    fn intern_bool(&mut self, name: &str) -> i32 {
        if let Some(&v) = self.bool_vars.get(name) {
            return v;
        }
        self.next_var += 1;
        let v = self.next_var as i32;
        self.bool_vars.insert(name.to_string(), v);
        v
    }

    fn fresh(&mut self) -> i32 {
        self.next_var += 1;
        self.next_var as i32
    }

    fn add_clause(&mut self, c: Vec<i32>) {
        self.clauses.push(c);
    }

    /// Encode `term` and return a literal `l` that is true iff `term` is true under
    /// the given `polarity` (the caller asserts the root as true).
    fn encode(&mut self, term: &Term, polarity: bool) -> Result<i32, SmtError> {
        // Convention: the returned literal `l` is *true* iff `term` has the truth value
        // `polarity` (so `l` true <=> term is true, when `polarity` is true).
        let l = match term {
            Term::Bool(b) => {
                let v = self.fresh();
                self.add_clause(vec![if *b { v } else { -v }]);
                if polarity {
                    v
                } else {
                    -v
                }
            }
            Term::Sym(name) => {
                let v = self.intern_bool(name);
                if polarity {
                    v
                } else {
                    -v
                }
            }
            Term::Num(_) => {
                return Err(SmtError::Unsupported(
                    "numeric constant in boolean position".into(),
                ))
            }
            Term::App(Op::Not, args) => {
                if args.len() != 1 {
                    return Err(SmtError::BadArity("not expects 1 argument".into()));
                }
                self.encode(&args[0], !polarity)?
            }
            Term::App(Op::And, args) => {
                let mut lits = Vec::with_capacity(args.len());
                for a in args {
                    lits.push(self.encode(a, true)?);
                }
                let v = self.fresh();
                for &li in &lits {
                    self.add_clause(vec![-v, li]);
                }
                let mut big = vec![v];
                for &li in &lits {
                    big.push(-li);
                }
                self.add_clause(big);
                if polarity {
                    v
                } else {
                    -v
                }
            }
            Term::App(Op::Or, args) => {
                let mut lits = Vec::with_capacity(args.len());
                for a in args {
                    lits.push(self.encode(a, true)?);
                }
                let v = self.fresh();
                for &li in &lits {
                    self.add_clause(vec![v, -li]);
                }
                let mut big = vec![-v];
                for &li in &lits {
                    big.push(li);
                }
                self.add_clause(big);
                if polarity {
                    v
                } else {
                    -v
                }
            }
            Term::App(Op::Imp, args) => {
                if args.len() != 2 {
                    return Err(SmtError::BadArity("=> expects 2 arguments".into()));
                }
                // a => b  ==  (not a) or b
                let not_a = Term::App(Op::Not, vec![args[0].clone()]);
                let or_term = Term::App(Op::Or, vec![not_a, args[1].clone()]);
                self.encode(&or_term, polarity)?
            }
            Term::App(Op::Xor, args) => {
                if args.len() != 2 {
                    return Err(SmtError::BadArity("xor expects 2 arguments".into()));
                }
                let a = self.encode(&args[0], true)?;
                let b = self.encode(&args[1], true)?;
                let v = self.fresh();
                self.add_clause(vec![-v, a, b]);
                self.add_clause(vec![-v, -a, -b]);
                self.add_clause(vec![v, -a, b]);
                self.add_clause(vec![v, a, -b]);
                if polarity {
                    v
                } else {
                    -v
                }
            }
            Term::App(Op::Ite, args) => {
                if args.len() != 3 {
                    return Err(SmtError::BadArity("ite expects 3 arguments".into()));
                }
                // ite(c, a, b) == (c and a) or (not c and b)
                let branch1 = Term::App(Op::And, vec![args[0].clone(), args[1].clone()]);
                let not_c = Term::App(Op::Not, vec![args[0].clone()]);
                let branch2 = Term::App(Op::And, vec![not_c, args[2].clone()]);
                let or_term = Term::App(Op::Or, vec![branch1, branch2]);
                self.encode(&or_term, polarity)?
            }
            Term::App(Op::Eq, args) => {
                if args.len() != 2 {
                    return Err(SmtError::BadArity("= expects 2 arguments".into()));
                }
                let a = self.encode(&args[0], true)?;
                let b = self.encode(&args[1], true)?;
                let v = self.fresh();
                self.add_clause(vec![-v, a, -b]);
                self.add_clause(vec![-v, -a, b]);
                self.add_clause(vec![v, a, b]);
                self.add_clause(vec![v, -a, -b]);
                if polarity {
                    v
                } else {
                    -v
                }
            }
            Term::App(Op::Distinct, args) => {
                // Boolean distinct of two terms is exactly XOR.
                if args.len() != 2 {
                    return Err(SmtError::Unsupported(
                        "distinct is only supported on 2 boolean terms".into(),
                    ));
                }
                let a = self.encode(&args[0], true)?;
                let b = self.encode(&args[1], true)?;
                let v = self.fresh();
                self.add_clause(vec![-v, a, b]);
                self.add_clause(vec![-v, -a, -b]);
                self.add_clause(vec![v, -a, b]);
                self.add_clause(vec![v, a, -b]);
                if polarity {
                    v
                } else {
                    -v
                }
            }
            Term::App(Op::Le, _)
            | Term::App(Op::Lt, _)
            | Term::App(Op::Ge, _)
            | Term::App(Op::Gt, _) => {
                return Err(SmtError::Unsupported(
                    "arithmetic comparison in a boolean formula; use the LRA path".into(),
                ))
            }
            Term::App(Op::Other, _)
            | Term::App(Op::Add, _)
            | Term::App(Op::Sub, _)
            | Term::App(Op::Mul, _)
            | Term::App(Op::Div, _) => {
                return Err(SmtError::Unsupported(
                    "non-boolean term in a boolean formula".into(),
                ))
            }
        };
        Ok(l)
    }
}

// ---------------------------------------------------------------------------
// Top-level parse
// ---------------------------------------------------------------------------

/// Parse an SMT-LIB2 script string into a [`Script`].
pub fn parse_script(input: &str) -> Result<Script, SmtError> {
    let toks = tokenize(input)?;
    let mut pos = 0;
    let sexps = parse_sexps(&toks, &mut pos)?;
    if pos != toks.len() {
        return Err(SmtError::Parse("unexpected ')'".into()));
    }

    let mut script = Script::default();
    for sexp in &sexps {
        match sexp {
            Sexp::List(items) => {
                if items.is_empty() {
                    continue;
                }
                if let Sexp::Atom(head) = &items[0] {
                    match head.as_str() {
                        "set-logic" => {
                            if let Some(Sexp::Atom(l)) = items.get(1) {
                                script.logic = Some(l.clone());
                            }
                        }
                        "set-option" => {}
                        "declare-fun" | "declare-const" => {
                            if let Some(decl) = parse_decl(head, items) {
                                script.decls.push(decl);
                            }
                        }
                        "assert" => {
                            if let Some(body) = items.get(1) {
                                script.asserts.push(sexp_to_term(body)?);
                            }
                        }
                        "check-sat" | "get-model" | "exit" | "push" | "pop" | "reset" => {}
                        _ => {}
                    }
                }
            }
            Sexp::Atom(_) => {}
        }
    }
    Ok(script)
}

fn parse_decl(head: &str, items: &[Sexp]) -> Option<Decl> {
    let name = match items.get(1) {
        Some(Sexp::Atom(n)) => n.clone(),
        _ => return None,
    };
    // declare-const: (declare-const x Real)
    // declare-fun:    (declare-fun x () Real)
    let sort_sexp = if head == "declare-const" {
        items.get(2)
    } else {
        items.get(3)
    }?;
    let sort = parse_sort(sort_sexp)?;
    Some(Decl { name, sort })
}

// ---------------------------------------------------------------------------
// Bit-vector lowering (QF_BV subset)
// ---------------------------------------------------------------------------

/// A lowered QF_BV problem, ready for the core's bit-blasting engine.
#[derive(Debug, Clone)]
pub struct BvProblem {
    /// Number of bit-vector variables; ids are dense in `0..var_count`.
    pub var_count: u32,
    /// Variable names by id (for model display).
    pub names: Vec<String>,
    /// The conjunction of asserted comparisons.
    pub assertions: Vec<BvAssertion>,
}

#[derive(Default)]
struct BvCtx {
    names: Vec<String>,
    idx: HashMap<String, (u32, u8)>,
}

impl BvCtx {
    fn intern(&mut self, name: &str, width: u8) {
        if !self.idx.contains_key(name) {
            let id = self.names.len() as u32;
            self.names.push(name.to_string());
            self.idx.insert(name.to_string(), (id, width));
        }
    }

    fn lookup(&self, name: &str) -> Option<(u32, u8)> {
        self.idx.get(name).copied()
    }
}

fn collect_bv_assertions(
    term: &Term,
    ctx: &mut BvCtx,
    out: &mut Vec<BvAssertion>,
) -> Result<(), SmtError> {
    match term {
        Term::App(Op::And, args) => {
            for a in args {
                collect_bv_assertions(a, ctx, out)?;
            }
            Ok(())
        }
        Term::Bool(true) => Ok(()),
        Term::App(Op::Eq, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("equality expects 2 arguments".into()));
            }
            let l = bv_term(&args[0], ctx)?;
            let r = bv_term(&args[1], ctx)?;
            BvAssertion::eq(l, r).ok_or_else(|| {
                SmtError::Unsupported("bit-vector equality width mismatch".into())
            })
        }
        Term::App(Op::BvUlt, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("bvult expects 2 arguments".into()));
            }
            let l = bv_term(&args[0], ctx)?;
            let r = bv_term(&args[1], ctx)?;
            BvAssertion::ult(l, r).ok_or_else(|| {
                SmtError::Unsupported("bit-vector comparison width mismatch".into())
            })
        }
        _ => Err(SmtError::Unsupported(
            "QF_BV lowering supports only conjunctions of = and bvult".into(),
        )),
    }
}

/// Lower a bit-vector term. Shifts must be by constant `#x`/`#b` literals.
fn bv_term(term: &Term, ctx: &BvCtx) -> Result<BvTerm, SmtError> {
    let width_mismatch = || SmtError::Unsupported("bit-vector width mismatch".into());
    match term {
        Term::BvLit(v, w) => BvTerm::constant(*w, *v)
            .ok_or_else(|| SmtError::Unsupported("bit-vector width out of range".into())),
        Term::Sym(name) => {
            let (id, w) = ctx.lookup(name).ok_or_else(|| {
                SmtError::Unsupported(format!("unknown bit-vector symbol {:?}", name))
            })?;
            BvTerm::var(id, w)
                .ok_or_else(|| SmtError::Unsupported("bit-vector width out of range".into()))
        }
        Term::Extract(range, arg) => {
            let a = bv_term(arg, ctx)?;
            let hi = u8::try_from(range.hi)
                .ok()
                .filter(|&h| h < 64)
                .ok_or_else(|| SmtError::Unsupported("extract index out of range".into()))?;
            let lo = u8::try_from(range.lo)
                .ok()
                .filter(|&l| l <= hi)
                .ok_or_else(|| SmtError::Unsupported("extract index out of range".into()))?;
            BvTerm::extract(a, hi, lo)
                .ok_or_else(|| SmtError::Unsupported("extract range outside operand".into()))
        }
        Term::App(op, args) => {
            let need = |n: usize| -> Result<(), SmtError> {
                if args.len() != n {
                    Err(SmtError::BadArity(format!(
                        "operator expects {} arguments",
                        n
                    )))
                } else {
                    Ok(())
                }
            };
            let a0 = || bv_term(&args[0], ctx);
            let a1 = || bv_term(&args[1], ctx);
            match op {
                Op::BvNot => {
                    need(1)?;
                    BvTerm::not(a0()?).ok_or_else(width_mismatch)
                }
                Op::BvNeg => {
                    need(1)?;
                    BvTerm::neg(a0()?).ok_or_else(width_mismatch)
                }
                Op::BvAdd => {
                    need(2)?;
                    BvTerm::add(a0()?, a1()?).ok_or_else(width_mismatch)
                }
                Op::BvSub => {
                    need(2)?;
                    BvTerm::sub(a0()?, a1()?).ok_or_else(width_mismatch)
                }
                Op::BvAnd => {
                    need(2)?;
                    BvTerm::and(a0()?, a1()?).ok_or_else(width_mismatch)
                }
                Op::BvOr => {
                    need(2)?;
                    BvTerm::or(a0()?, a1()?).ok_or_else(width_mismatch)
                }
                Op::BvXor => {
                    need(2)?;
                    BvTerm::xor(a0()?, a1()?).ok_or_else(width_mismatch)
                }
                Op::Concat => {
                    need(2)?;
                    BvTerm::concat(a0()?, a1()?)
                        .ok_or_else(|| SmtError::Unsupported("concatenation exceeds 64 bits".into()))
                }
                Op::BvShl | Op::BvLShr => {
                    need(2)?;
                    let amt = match &args[1] {
                        // Amounts >= any width collapse to "yield 0", so 64 is
                        // a faithful saturation point for widths <= 64.
                        Term::BvLit(v, _) => Some(v.min(64) as u8),
                        _ => None,
                    }
                    .ok_or_else(|| {
                        SmtError::Unsupported(
                            "shifts must be by a constant #x/#b literal".into(),
                        )
                    })?;
                    let arg = a0()?;
                    if *op == Op::BvShl {
                        BvTerm::shl(arg, amt)
                    } else {
                        BvTerm::lshr(arg, amt)
                    }
                    .ok_or_else(width_mismatch)
                }
                _ => Err(SmtError::Unsupported(format!(
                    "operator not supported in the QF_BV subset: {:?}",
                    op
                ))),
            }
        }
        _ => Err(SmtError::Unsupported(
            "term is not a bit-vector expression".into(),
        )),
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn parses_lra_unsat() {
        let src = "
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (>= x 1))
(assert (<= x 0))
(check-sat)
";
        let script = parse_script(src).unwrap();
        let prob = script.to_lra().unwrap();
        // x >= 1 => -x <= -1 ; x <= 0 => x <= 0
        assert_eq!(prob.constraints.len(), 2);
        assert_eq!(prob.vars, vec!["x".to_string()]);
    }

    #[test]
    fn lra_sat_roundtrip_via_engine() {
        let src = "
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (<= x 5))
(assert (>= x 0))
(assert (<= y 5))
(assert (>= y 0))
(assert (<= (+ x y) 8))
(check-sat)
";
        let script = parse_script(src).unwrap();
        let prob = script.to_lra().unwrap();
        let (claim, verdict) = crate::reference::solve_and_check_lra(&prob.constraints, 1_000_000);
        assert_eq!(claim, tpt_solver_core::engine::SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn parses_propositional_sat() {
        let src = "
(set-logic QF_SAT)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
(assert (not a))
(check-sat)
";
        let script = parse_script(src).unwrap();
        let prob = script.to_cnf().unwrap();
        assert!(prob.var_count >= 2);
        // Should be satisfiable (b true).
        let (claim, verdict) = crate::reference::solve_and_check_cdcl(&prob, 1_000_000);
        assert_eq!(claim, tpt_solver_core::engine::SolveResult::Sat);
        assert!(verdict.is_accept());
    }

    #[test]
    fn rejects_nonlinear() {
        let src = "
(declare-fun x () Real)
(declare-fun y () Real)
(assert (<= (* x y) 3))
(check-sat)
";
        let script = parse_script(src).unwrap();
        assert!(script.to_lra().is_err());
    }

    #[test]
    fn disjunction_is_unsupported_in_lra() {
        let src = "
(declare-fun x () Real)
(assert (or (<= x 1) (>= x 2)))
(check-sat)
";
        let script = parse_script(src).unwrap();
        assert!(matches!(script.to_lra(), Err(SmtError::Unsupported(_))));
    }
}
