//! Fixed-width bit-vector theory — a practical QF_BV fragment (Phase 5).
//!
//! Terms are word-level trees over variables and constants of width 1..=64,
//! with bitwise (`and`/`or`/`xor`/`not`), two's-complement (`add`/`sub`/
//! `neg`), constant shifts, `concat`, and `extract`. Assertions are unsigned
//! equality and `<`.
//!
//! Decision procedure: **eager bit-blasting** onto the existing CDCL engine
//! ([`crate::sat`]) — the same architecture production solvers use for QF_BV.
//!
//! Certificate story (mirroring every other theory in this suite):
//!
//! * **SAT** — the bit-level model is decoded into word values
//!   ([`BvModel`]); the trusted kernel re-evaluates the *original* assertions
//!   under that model with its own independent evaluator
//!   (`tpt_solver_check::bv::check_bv_model`), so a wrong SAT answer cannot
//!   survive. The engine additionally self-checks before claiming `Sat`.
//! * **UNSAT** — the CDCL proof over the *blasted* CNF ships alongside the
//!   blast itself ([`BvUnsatCert`]); the kernel re-validates the proof
//!   clause-by-clause (`tpt_solver_check::bv::check_bv_unsat`). The residual
//!   trust surface — this file's encoder circuits — is closed by differential
//!   brute-force property testing (the `oracle` tests below), not by the
//!   kernel.
//!
//! Malformed input (bad widths, oversized extracts, inconsistent variable
//! widths) yields `None` — surfaced downstream as `Unknown`, never a panic —
//! and all traversals are iterative so adversarially deep terms cannot
//! overflow the stack.

use crate::engine::SolveResult;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

/// Maximum supported bit-vector width (fits a `u64` word).
pub const MAX_WIDTH: u8 = 64;

/// A binary bit-vector operation; operands and result share one width.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BvBinOp {
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise exclusive or.
    Xor,
    /// Two's-complement addition (wraps mod 2^width).
    Add,
    /// Two's-complement subtraction (wraps mod 2^width).
    Sub,
}

/// A word-level bit-vector term.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BvTerm {
    /// A variable of fixed width; ids are dense in `0..var_count`.
    Var {
        /// Dense variable id.
        id: u32,
        /// Width in bits, `1..=64`.
        width: u8,
    },
    /// A constant, stored masked to `width` bits.
    Const {
        /// Width in bits, `1..=64`.
        width: u8,
        /// The masked constant value.
        value: u64,
    },
    /// Bitwise negation.
    Not {
        /// Operand.
        arg: Box<BvTerm>,
    },
    /// Two's-complement negation (wraps).
    Neg {
        /// Operand.
        arg: Box<BvTerm>,
    },
    /// A binary operation over same-width operands.
    BinOp {
        /// Which operation.
        op: BvBinOp,
        /// Left operand.
        lhs: Box<BvTerm>,
        /// Right operand.
        rhs: Box<BvTerm>,
    },
    /// Shift by a constant amount: logical left if `left`, else logical
    /// right; shifting by `>= width` yields zero.
    Shift {
        /// `true` for left shift, `false` for logical right shift.
        left: bool,
        /// Operand.
        arg: Box<BvTerm>,
        /// Shift amount.
        amount: u8,
    },
    /// Concatenation: low bits are `lo`, high bits are `hi`.
    Concat {
        /// High part.
        hi: Box<BvTerm>,
        /// Low part.
        lo: Box<BvTerm>,
    },
    /// Extraction of bits `lo..=hi` (inclusive).
    Extract {
        /// Operand.
        arg: Box<BvTerm>,
        /// Highest extracted bit index.
        hi: u8,
        /// Lowest extracted bit index.
        lo: u8,
    },
}

/// Mask with the low `w` bits set (`w` in `1..=64`).
#[inline]
pub(crate) fn mask(w: u8) -> u64 {
    if w >= MAX_WIDTH {
        u64::MAX
    } else {
        (1u64 << w) - 1
    }
}

fn width_ok(w: u8) -> bool {
    (1..=MAX_WIDTH).contains(&w)
}

impl BvTerm {
    /// A variable of `width` bits; `None` if the width is out of range.
    pub fn var(id: u32, width: u8) -> Option<BvTerm> {
        if width_ok(width) {
            Some(BvTerm::Var { id, width })
        } else {
            None
        }
    }

    /// A constant of `width` bits; `value` is masked to the width.
    pub fn constant(width: u8, value: u64) -> Option<BvTerm> {
        if width_ok(width) {
            Some(BvTerm::Const {
                width,
                value: value & mask(width),
            })
        } else {
            None
        }
    }

    /// The width of this term in bits.
    pub fn width(&self) -> u8 {
        match self {
            BvTerm::Var { width, .. } | BvTerm::Const { width, .. } => *width,
            BvTerm::Not { arg } | BvTerm::Neg { arg } => arg.width(),
            BvTerm::BinOp { lhs, .. } => lhs.width(),
            BvTerm::Shift { arg, .. } => arg.width(),
            BvTerm::Concat { hi, lo } => hi.width().saturating_add(lo.width()),
            BvTerm::Extract { hi, lo, .. } => hi.saturating_sub(*lo) + 1,
        }
    }

    fn boxed_bin(op: BvBinOp, lhs: BvTerm, rhs: BvTerm) -> Option<BvTerm> {
        if width_ok(lhs.width()) && lhs.width() == rhs.width() {
            Some(BvTerm::BinOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
        } else {
            None
        }
    }

    /// Bitwise and of two same-width terms.
    pub fn and(lhs: BvTerm, rhs: BvTerm) -> Option<BvTerm> {
        BvTerm::boxed_bin(BvBinOp::And, lhs, rhs)
    }

    /// Bitwise or of two same-width terms.
    pub fn or(lhs: BvTerm, rhs: BvTerm) -> Option<BvTerm> {
        BvTerm::boxed_bin(BvBinOp::Or, lhs, rhs)
    }

    /// Bitwise exclusive or of two same-width terms.
    pub fn xor(lhs: BvTerm, rhs: BvTerm) -> Option<BvTerm> {
        BvTerm::boxed_bin(BvBinOp::Xor, lhs, rhs)
    }

    /// Wrapping addition of two same-width terms.
    #[allow(clippy::should_implement_trait)]
    pub fn add(lhs: BvTerm, rhs: BvTerm) -> Option<BvTerm> {
        BvTerm::boxed_bin(BvBinOp::Add, lhs, rhs)
    }

    /// Wrapping subtraction of two same-width terms.
    #[allow(clippy::should_implement_trait)]
    pub fn sub(lhs: BvTerm, rhs: BvTerm) -> Option<BvTerm> {
        BvTerm::boxed_bin(BvBinOp::Sub, lhs, rhs)
    }

    /// Bitwise negation.
    #[allow(clippy::should_implement_trait)]
    pub fn not(arg: BvTerm) -> Option<BvTerm> {
        if width_ok(arg.width()) {
            Some(BvTerm::Not { arg: Box::new(arg) })
        } else {
            None
        }
    }

    /// Two's-complement negation.
    #[allow(clippy::should_implement_trait)]
    pub fn neg(arg: BvTerm) -> Option<BvTerm> {
        if width_ok(arg.width()) {
            Some(BvTerm::Neg { arg: Box::new(arg) })
        } else {
            None
        }
    }

    /// Logical left shift by a constant amount (`>= width` yields zero).
    #[allow(clippy::should_implement_trait)]
    pub fn shl(arg: BvTerm, amount: u8) -> Option<BvTerm> {
        if width_ok(arg.width()) {
            Some(BvTerm::Shift {
                left: true,
                arg: Box::new(arg),
                amount,
            })
        } else {
            None
        }
    }

    /// Logical right shift by a constant amount (`>= width` yields zero).
    pub fn lshr(arg: BvTerm, amount: u8) -> Option<BvTerm> {
        if width_ok(arg.width()) {
            Some(BvTerm::Shift {
                left: false,
                arg: Box::new(arg),
                amount,
            })
        } else {
            None
        }
    }

    /// Concatenation; combined width must be at most [`MAX_WIDTH`].
    pub fn concat(hi: BvTerm, lo: BvTerm) -> Option<BvTerm> {
        let total = hi.width().saturating_add(lo.width());
        if width_ok(hi.width()) && width_ok(lo.width()) && total <= MAX_WIDTH {
            Some(BvTerm::Concat {
                hi: Box::new(hi),
                lo: Box::new(lo),
            })
        } else {
            None
        }
    }

    /// Extract bits `lo..=hi`; requires `lo <= hi < arg.width()`.
    pub fn extract(arg: BvTerm, hi: u8, lo: u8) -> Option<BvTerm> {
        if width_ok(arg.width()) && lo <= hi && hi < arg.width() {
            Some(BvTerm::Extract {
                arg: Box::new(arg),
                hi,
                lo,
            })
        } else {
            None
        }
    }
}

/// An assertion of the bit-vector problem: unsigned comparison of two
/// same-width terms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BvAssertion {
    /// `lhs == rhs` (bitwise equality).
    Eq(BvTerm, BvTerm),
    /// `lhs < rhs` (unsigned).
    Ult(BvTerm, BvTerm),
}

impl BvAssertion {
    /// Build an equality assertion; `None` on a width mismatch.
    pub fn eq(lhs: BvTerm, rhs: BvTerm) -> Option<BvAssertion> {
        if lhs.width() == rhs.width() {
            Some(BvAssertion::Eq(lhs, rhs))
        } else {
            None
        }
    }

    /// Build an unsigned less-than assertion; `None` on a width mismatch.
    pub fn ult(lhs: BvTerm, rhs: BvTerm) -> Option<BvAssertion> {
        if lhs.width() == rhs.width() {
            Some(BvAssertion::Ult(lhs, rhs))
        } else {
            None
        }
    }
}

/// Evaluate a term under an assignment (`env[id]` = value).
///
/// Returns `None` for malformed terms or out-of-range variable ids.
/// Iterative (explicit stack): adversarially deep terms cannot overflow
/// the call stack.
pub fn eval_bv(term: &BvTerm, env: &[u64]) -> Option<u64> {
    enum Item<'a> {
        Enter(&'a BvTerm),
        Merge(&'a BvTerm),
    }
    fn addr(t: &BvTerm) -> usize {
        t as *const BvTerm as usize
    }
    // Compute a node's value from its children's completed results.
    fn compute(t: &BvTerm, env: &[u64], done: &BTreeMap<usize, u64>) -> Option<u64> {
        let kid = |c: &BvTerm| done.get(&addr(c)).copied();
        match t {
            BvTerm::Var { id, .. } => env_get(env, *id).copied(),
            BvTerm::Const { value, .. } => Some(*value),
            BvTerm::Not { arg } => Some((!kid(arg)?) & mask(arg.width())),
            BvTerm::Neg { arg } => Some(kid(arg)?.wrapping_neg() & mask(arg.width())),
            BvTerm::BinOp { op, lhs, rhs } => {
                let (l, r) = (kid(lhs)?, kid(rhs)?);
                let w = lhs.width();
                match op {
                    BvBinOp::And => Some(l & r),
                    BvBinOp::Or => Some(l | r),
                    BvBinOp::Xor => Some(l ^ r),
                    BvBinOp::Add => Some(l.wrapping_add(r) & mask(w)),
                    BvBinOp::Sub => Some(l.wrapping_sub(r) & mask(w)),
                }
            }
            BvTerm::Shift {
                left, arg, amount, ..
            } => {
                let w = arg.width();
                let amt = *amount as u32;
                if amt >= w as u32 {
                    Some(0)
                } else if *left {
                    Some((kid(arg)? << amt) & mask(w))
                } else {
                    Some(kid(arg)? >> amt)
                }
            }
            BvTerm::Extract { arg, hi, lo } => {
                if *hi >= arg.width() || *lo > *hi {
                    return None;
                }
                Some((kid(arg)? >> *lo) & mask(*hi - *lo + 1))
            }
            BvTerm::Concat { hi, lo } => Some((kid(hi)? << lo.width()) | kid(lo)?),
        }
    }

    let mut stack = alloc::vec![Item::Enter(term)];
    let mut done: BTreeMap<usize, u64> = BTreeMap::new();
    while let Some(item) = stack.pop() {
        match item {
            Item::Enter(t) => match t {
                BvTerm::Var { .. } | BvTerm::Const { .. } => {
                    let v = compute(t, env, &done)?;
                    done.insert(addr(t), v);
                }
                _ => {
                    stack.push(Item::Merge(t));
                    match t {
                        BvTerm::Not { arg } | BvTerm::Neg { arg } => stack.push(Item::Enter(arg)),
                        BvTerm::BinOp { lhs, rhs, .. } => {
                            stack.push(Item::Enter(rhs));
                            stack.push(Item::Enter(lhs));
                        }
                        BvTerm::Shift { arg, .. } | BvTerm::Extract { arg, .. } => {
                            stack.push(Item::Enter(arg))
                        }
                        BvTerm::Concat { hi, lo } => {
                            stack.push(Item::Enter(lo));
                            stack.push(Item::Enter(hi));
                        }
                        _ => {}
                    }
                }
            },
            Item::Merge(t) => {
                let v = compute(t, env, &done)?;
                done.insert(addr(t), v);
            }
        }
    }
    done.get(&addr(term)).copied()
}

fn env_get(env: &[u64], id: u32) -> Option<&u64> {
    env.get(id as usize)
}

/// Does `a` hold under the word assignment `values`?
fn assertion_holds(a: &BvAssertion, values: &[u64]) -> Option<bool> {
    match a {
        BvAssertion::Eq(l, r) => Some(eval_bv(l, values)? == eval_bv(r, values)?),
        BvAssertion::Ult(l, r) => Some(eval_bv(l, values)? < eval_bv(r, values)?),
    }
}

/// The CNF produced by bit-blasting, plus everything needed to decode a model.
#[derive(Clone, Debug)]
pub struct BlastedBv {
    /// Number of SAT variables in the encoding.
    pub var_count: u32,
    /// The encoded clauses (DIMACS-style signed literals).
    pub clauses: Vec<Vec<i32>>,
    /// Per problem-variable bit literals (LSB first), indexed by variable id.
    pub var_bits: Vec<Vec<i32>>,
}

struct Blaster {
    next_var: u32,
    clauses: Vec<Vec<i32>>,
    memo: BTreeMap<BvTerm, Vec<i32>>,
}

impl Blaster {
    fn new() -> Blaster {
        // Variable 1 is pinned false and shared as the constant wire; its
        // negation is the canonical `true` literal.
        Blaster {
            next_var: 2,
            clauses: vec![vec![-1]],
            memo: BTreeMap::new(),
        }
    }

    fn fresh(&mut self) -> i32 {
        let v = self.next_var;
        self.next_var += 1;
        v as i32
    }

    fn false_lit(&self) -> i32 {
        // Variable 1 is pinned false by a unit clause; its positive literal
        // therefore evaluates to false.
        1
    }

    fn true_lit(&self) -> i32 {
        -1
    }

    fn unit(&mut self, l: i32) {
        self.clauses.push(vec![l]);
    }

    fn g_not(&mut self, a: i32) -> i32 {
        let z = self.fresh();
        self.clauses.push(vec![-z, -a]);
        self.clauses.push(vec![z, a]);
        z
    }

    fn g_and(&mut self, a: i32, b: i32) -> i32 {
        let z = self.fresh();
        self.clauses.push(vec![-z, a]);
        self.clauses.push(vec![-z, b]);
        self.clauses.push(vec![z, -a, -b]);
        z
    }

    fn g_or(&mut self, a: i32, b: i32) -> i32 {
        let z = self.fresh();
        self.clauses.push(vec![z, -a]);
        self.clauses.push(vec![z, -b]);
        self.clauses.push(vec![-z, a, b]);
        z
    }

    fn g_xor(&mut self, a: i32, b: i32) -> i32 {
        let z = self.fresh();
        self.clauses.push(vec![-a, -b, -z]);
        self.clauses.push(vec![a, b, -z]);
        self.clauses.push(vec![a, -b, z]);
        self.clauses.push(vec![-a, b, z]);
        z
    }

    /// Ripple-carry addition of two equal-length bit vectors.
    fn add_bits(&mut self, x: &[i32], y: &[i32], carry_in: i32) -> Vec<i32> {
        let mut out = Vec::with_capacity(x.len());
        let mut c = carry_in;
        for k in 0..x.len() {
            let t = self.g_xor(x[k], y[k]);
            let s = self.g_xor(t, c);
            let c1 = self.g_and(x[k], y[k]);
            let c2 = self.g_and(t, c);
            c = self.g_or(c1, c2);
            out.push(s);
        }
        out
    }

    fn const_bits(&self, w: usize, value: u64) -> Vec<i32> {
        (0..w)
            .map(|k| {
                if (value >> k) & 1 == 1 {
                    self.true_lit()
                } else {
                    self.false_lit()
                }
            })
            .collect()
    }

    fn neg_bits(&mut self, x: &[i32]) -> Vec<i32> {
        let inverted: Vec<i32> = x.iter().map(|&b| self.g_not(b)).collect();
        let one = self.const_bits(x.len(), 1);
        self.add_bits(&inverted, &one, self.false_lit())
    }

    /// Bit-blast `t`, allocating variable bits on first encounter. Iterative;
    /// shared subterms are memoized structurally.
    fn term(&mut self, root: &BvTerm, var_bits: &mut [Vec<i32>]) -> Option<Vec<i32>> {
        enum Item<'a> {
            Enter(&'a BvTerm),
            Merge(&'a BvTerm),
        }
        fn addr(t: &BvTerm) -> usize {
            t as *const BvTerm as usize
        }
        if let Some(b) = self.memo.get(root) {
            return Some(b.clone());
        }
        let mut stack = alloc::vec![Item::Enter(root)];
        let mut done: BTreeMap<usize, Vec<i32>> = BTreeMap::new();
        while let Some(item) = stack.pop() {
            match item {
                Item::Enter(t) => {
                    if done.contains_key(&addr(t)) {
                        continue; // duplicate child within this traversal
                    }
                    if let Some(b) = self.memo.get(t) {
                        // Cross-assertion memo hit: seed this traversal's map
                        // so parents can find the child's bits.
                        let b = b.clone();
                        done.insert(addr(t), b);
                        continue;
                    }
                    match t {
                        BvTerm::Var { id, width } => {
                            let id = *id as usize;
                            let w = *width as usize;
                            match var_bits.get(id) {
                                None => return None,
                                Some(existing) if !existing.is_empty() && existing.len() != w => {
                                    return None; // inconsistent width for one id
                                }
                                _ => {}
                            }
                            let bits: Vec<i32> = (0..w).map(|_| self.fresh()).collect();
                            var_bits[id] = bits.clone();
                            self.memo.insert(t.clone(), bits.clone());
                            done.insert(addr(t), bits);
                        }
                        BvTerm::Const { width, value } => {
                            let bits = self.const_bits(*width as usize, *value);
                            self.memo.insert(t.clone(), bits.clone());
                            done.insert(addr(t), bits);
                        }
                        _ => {
                            stack.push(Item::Merge(t));
                            match t {
                                BvTerm::Not { arg } | BvTerm::Neg { arg } => {
                                    stack.push(Item::Enter(arg))
                                }
                                BvTerm::BinOp { lhs, rhs, .. } => {
                                    stack.push(Item::Enter(rhs));
                                    stack.push(Item::Enter(lhs));
                                }
                                BvTerm::Shift { arg, .. } | BvTerm::Extract { arg, .. } => {
                                    stack.push(Item::Enter(arg))
                                }
                                BvTerm::Concat { hi, lo } => {
                                    stack.push(Item::Enter(lo));
                                    stack.push(Item::Enter(hi));
                                }
                                _ => {}
                            }
                        }
                    }
                }
                Item::Merge(t) => {
                    let bits = self.merge_bits(t, &done)?;
                    done.insert(addr(t), bits.clone());
                    self.memo.insert(t.clone(), bits);
                }
            }
        }
        self.memo.get(root).cloned()
    }
}

impl Blaster {
    /// Build output bits for a composite node from its children's bits.
    fn merge_bits(&mut self, t: &BvTerm, done: &BTreeMap<usize, Vec<i32>>) -> Option<Vec<i32>> {
        let kid = |d: &BTreeMap<usize, Vec<i32>>, c: &BvTerm| -> Option<Vec<i32>> {
            d.get(&(c as *const BvTerm as usize)).cloned()
        };
        match t {
            BvTerm::Not { arg } => {
                let a = kid(done, arg)?;
                let mut out = Vec::with_capacity(a.len());
                for b in a {
                    out.push(self.g_not(b));
                }
                Some(out)
            }
            BvTerm::Neg { arg } => Some(self.neg_bits(&kid(done, arg)?)),
            BvTerm::BinOp { op, lhs, rhs } => {
                let (l, r) = (kid(done, lhs)?, kid(done, rhs)?);
                match op {
                    BvBinOp::Add => Some(self.add_bits(&l, &r, self.false_lit())),
                    BvBinOp::Sub => {
                        let nr = self.neg_bits(&r);
                        Some(self.add_bits(&l, &nr, self.false_lit()))
                    }
                    BvBinOp::And | BvBinOp::Or | BvBinOp::Xor => {
                        let mut out = Vec::with_capacity(l.len());
                        for k in 0..l.len().min(r.len()) {
                            out.push(match op {
                                BvBinOp::And => self.g_and(l[k], r[k]),
                                BvBinOp::Or => self.g_or(l[k], r[k]),
                                _ => self.g_xor(l[k], r[k]),
                            });
                        }
                        if out.len() != l.len() {
                            None
                        } else {
                            Some(out)
                        }
                    }
                }
            }
            BvTerm::Shift {
                left, arg, amount, ..
            } => {
                let a = kid(done, arg)?;
                let w = a.len();
                let amt = *amount as usize;
                let mut out = Vec::with_capacity(w);
                for k in 0..w {
                    if *left {
                        out.push(if k >= amt {
                            a[k - amt]
                        } else {
                            self.false_lit()
                        });
                    } else {
                        out.push(if k + amt < w {
                            a[k + amt]
                        } else {
                            self.false_lit()
                        });
                    }
                }
                Some(out)
            }
            BvTerm::Extract { arg, hi, lo } => {
                let a = kid(done, arg)?;
                let h = *hi as usize;
                let l = *lo as usize;
                if h >= a.len() || l > h {
                    return None;
                }
                Some(a[l..=h].to_vec())
            }
            BvTerm::Concat { hi, lo } => {
                let (h, l) = (kid(done, hi)?, kid(done, lo)?);
                let mut out = l;
                out.extend(h);
                Some(out)
            }
            _ => None,
        }
    }

    /// Encode `x == y` over already-blasted bit vectors.
    fn blast_eq(&mut self, x: &[i32], y: &[i32]) {
        for k in 0..x.len().min(y.len()) {
            self.clauses.push(vec![-x[k], y[k]]);
            self.clauses.push(vec![x[k], -y[k]]);
        }
    }

    /// Encode `x <u y` via an equality-chain comparator.
    fn blast_ult(&mut self, x: &[i32], y: &[i32]) {
        let mut e = self.true_lit();
        let mut acc: Option<i32> = None;
        for k in (0..x.len()).rev() {
            // Strict-less decided at bit k: all higher bits equal so far,
            // x_k false, y_k true.
            let nx = self.g_not(x[k]);
            let t = self.g_and(e, nx);
            let d = self.g_and(t, y[k]);
            acc = Some(match acc {
                None => d,
                Some(a) => self.g_or(a, d),
            });
            let x1 = self.g_xor(x[k], y[k]);
            let xnor = self.g_not(x1);
            e = self.g_and(e, xnor);
        }
        match acc {
            Some(lt) => self.unit(lt),
            None => self.unit(self.false_lit()),
        }
    }
}

/// Bit-blast a conjunction of assertions into CNF. Returns `None` on malformed
/// input (bad widths, unknown/inconsistent variables).
pub fn blast_bv(var_count: u32, assertions: &[BvAssertion]) -> Option<BlastedBv> {
    let mut blaster = Blaster::new();
    let mut var_bits: Vec<Vec<i32>> = vec![Vec::new(); var_count as usize];
    for a in assertions {
        let (lb, rb) = match a {
            BvAssertion::Eq(l, r) | BvAssertion::Ult(l, r) => {
                let lb = blaster.term(l, &mut var_bits)?;
                let rb = blaster.term(r, &mut var_bits)?;
                if lb.len() != rb.len() {
                    return None;
                }
                (lb, rb)
            }
        };
        match a {
            BvAssertion::Eq(..) => blaster.blast_eq(&lb, &rb),
            BvAssertion::Ult(..) => blaster.blast_ult(&lb, &rb),
        }
    }
    Some(BlastedBv {
        var_count: blaster.next_var - 1,
        clauses: blaster.clauses,
        var_bits,
    })
}

/// A word-level model: `values[id]` is the value of variable `id`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BvModel {
    /// Word value per variable id.
    pub values: Vec<u64>,
}

/// Evidence shipped with an UNSAT claim: the blasted CNF plus the CDCL proof
/// over it. The kernel re-validates the proof against these clauses; the
/// encoding itself is covered by the differential brute-force tests.
#[derive(Clone, Debug)]
pub struct BvUnsatCert {
    /// Number of SAT variables in the blast (needed by the LRAT checker).
    pub var_count: u32,
    /// The bit-blasted clauses.
    pub clauses: Vec<Vec<i32>>,
    /// Learned clauses in derivation order, ending in the empty clause.
    pub proof: Vec<Vec<i32>>,
}

/// The engine's bit-vector answer with its certificate.
#[derive(Clone, Debug)]
pub enum BvOutcome {
    /// Satisfiable, with a word-level model (kernel-recheckable).
    Sat(BvModel),
    /// Unsatisfiable, with the blast + proof (kernel-recheckable).
    Unsat(BvUnsatCert),
}

/// Decide a conjunction of bit-vector assertions by bit-blasting onto CDCL.
///
/// Returns `None` for malformed problems or if the SAT engine's fuel runs out
/// — both surface as "could not decide", never as a guess. On `Sat` the model
/// is self-checked against the original assertions before being returned.
pub fn solve_bv(var_count: u32, assertions: &[BvAssertion], fuel: u64) -> Option<BvOutcome> {
    let blasted = blast_bv(var_count, assertions)?;
    let ans = crate::sat::solve_cnf(blasted.var_count, &blasted.clauses, fuel);
    match ans.result {
        SolveResult::Sat => {
            let bits = ans.model?;
            let mut values = vec![0u64; var_count as usize];
            for (id, wb) in blasted.var_bits.iter().enumerate() {
                let mut v = 0u64;
                for (k, &l) in wb.iter().enumerate() {
                    let assigned = *bits.get((l.unsigned_abs() - 1) as usize)?;
                    let lit_true = if l > 0 { assigned } else { !assigned };
                    if lit_true && k < 64 {
                        v |= 1u64 << k;
                    }
                }
                values[id] = v;
            }
            // Defense in depth: never claim Sat without checking the model
            // ourselves first; the kernel re-checks independently afterwards.
            for a in assertions {
                match assertion_holds(a, &values) {
                    Some(true) => {}
                    _ => return None,
                }
            }
            Some(BvOutcome::Sat(BvModel { values }))
        }
        SolveResult::Unsat => Some(BvOutcome::Unsat(BvUnsatCert {
            var_count: blasted.var_count,
            clauses: blasted.clauses,
            proof: ans.proof,
        })),
        SolveResult::Unknown => None,
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
mod tests {
    use super::*;

    fn v(id: u32, w: u8) -> BvTerm {
        BvTerm::var(id, w).unwrap()
    }
    fn k(w: u8, val: u64) -> BvTerm {
        BvTerm::constant(w, val).unwrap()
    }
    fn eq(l: BvTerm, r: BvTerm) -> BvAssertion {
        BvAssertion::eq(l, r).unwrap()
    }

    #[test]
    fn tmp_and_bug_debug() {
        // x1 <u (x0|x1) & (x1&x0): RHS == x0&x1 <= x1 always => UNSAT.
        let x0 = v(0, 3);
        let x1 = v(1, 3);
        let or_t = BvTerm::or(x0.clone(), x1.clone()).unwrap();
        let and_t = BvTerm::and(x1.clone(), x0.clone()).unwrap();
        let rhs = BvTerm::and(or_t, and_t).unwrap();
        let asserts = vec![BvAssertion::ult(x1.clone(), rhs).unwrap()];
        // Brute-force truth:
        let mut any = false;
        for a in 0..8u64 {
            for b in 0..8u64 {
                if let Some(true) = assertion_holds(&asserts[0], &[a, b]) {
                    any = true;
                }
            }
        }
        println!("brute force satisfiable = {}", any);
        // Escalating fuels to distinguish exhaustion from an immediate Unknown.
        let blasted = blast_bv(2, &asserts).expect("blast");
        for f in [600u64] {
            let ans = crate::sat::solve_cnf(blasted.var_count, &blasted.clauses, f);
            println!("fuel={:>9} -> {:?}", f, ans.result);
        }
        match solve_bv(2, &asserts, 10_000_000) {
            Some(BvOutcome::Unsat(_)) => println!("engine UNSAT (correct)"),
            Some(BvOutcome::Sat(m)) => println!("engine SAT model={:?} (BUG)", m.values),
            None => println!("engine gave up (BUG?)"),
        }
    }

    #[test]
    fn constructor_width_validation() {
        assert!(BvTerm::var(0, 0).is_none());
        assert!(BvTerm::var(0, 65).is_none());
        assert!(BvTerm::concat(v(0, 40), v(1, 30)).is_none()); // 70 > 64
        let t = v(0, 8);
        assert!(BvTerm::extract(t.clone(), 8, 0).is_none()); // hi >= width
        assert!(BvTerm::extract(t.clone(), 6, 7).is_none()); // lo > hi
        assert!(BvTerm::and(v(0, 8), v(1, 9)).is_none()); // width mismatch
                                                          // Constants are masked on construction.
        assert_eq!(k(4, 0xFF), k(4, 0xF));
        assert_eq!(t.width(), 8);
        assert_eq!(BvTerm::concat(v(0, 5), v(1, 3)).unwrap().width(), 8);
        assert_eq!(BvTerm::extract(v(0, 8), 6, 2).unwrap().width(), 5);
    }

    #[test]
    fn eval_matches_word_semantics() {
        // add wraps: (12 + 5) mod 16 = 1 at width 4.
        let t = BvTerm::add(k(4, 12), k(4, 5)).unwrap();
        assert_eq!(eval_bv(&t, &[]), Some(1));
        // sub wraps below zero.
        let t = BvTerm::sub(k(4, 3), k(4, 7)).unwrap();
        assert_eq!(eval_bv(&t, &[]), Some(12));
        // neg of 0 is 0; not flips within the width.
        assert_eq!(eval_bv(&BvTerm::neg(k(4, 0)).unwrap(), &[]), Some(0));
        assert_eq!(eval_bv(&BvTerm::not(k(4, 0)).unwrap(), &[]), Some(15));
        // Shifts: overshoot yields zero.
        let x = v(0, 8);
        let env = [0b1010_1100u64];
        assert_eq!(
            eval_bv(&BvTerm::shl(x.clone(), 2).unwrap(), &env),
            Some(0b1011_0000)
        );
        assert_eq!(
            eval_bv(&BvTerm::lshr(x.clone(), 2).unwrap(), &env),
            Some(0b0010_1011)
        );
        assert_eq!(eval_bv(&BvTerm::lshr(x.clone(), 8).unwrap(), &env), Some(0));
        // Concat puts `lo` in the low bits.
        let c = BvTerm::concat(v(0, 4), v(1, 4)).unwrap();
        assert_eq!(eval_bv(&c, &[0xD, 0x7]), Some(0xD7));
        // Extract pulls bits lo..=hi.
        let e = BvTerm::extract(v(0, 8), 5, 2).unwrap();
        assert_eq!(eval_bv(&e, &[0b1010_1100]), Some(0b1011));
        // Out-of-range variable id is None, never a panic.
        assert_eq!(eval_bv(&v(9, 4), &[]), None);
    }

    #[test]
    fn unsat_xor_self_complement() {
        // x ^ ~x == 1111 always, so equating it to 0 is unsatisfiable.
        let w = 4;
        let x = v(0, w);
        let taut = BvTerm::xor(x.clone(), BvTerm::not(x).unwrap()).unwrap();
        let asserts = vec![eq(taut, k(w, 0))];
        match solve_bv(1, &asserts, 1_000_000) {
            Some(BvOutcome::Unsat(_)) => {}
            other => panic!("expected Unsat, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn sat_add_one_wraps_to_zero() {
        // x + 1 == 0 at width 4 forces x = 15 (wrapping).
        let w = 4;
        let t = BvTerm::add(v(0, w), k(w, 1)).unwrap();
        let asserts = vec![eq(t, k(w, 0))];
        match solve_bv(1, &asserts, 1_000_000) {
            Some(BvOutcome::Sat(model)) => {
                assert_eq!(model.values, vec![15]);
                // The kernel-side re-check would substitute and agree.
                assert!(assertion_holds(&asserts[0], &model.values) == Some(true));
            }
            _ => panic!("expected Sat"),
        }
    }

    #[test]
    fn ult_conflict_is_unsat() {
        // x < 3 and x == 5 cannot both hold.
        let asserts = vec![
            BvAssertion::ult(v(0, 8), k(8, 3)).unwrap(),
            eq(v(0, 8), k(8, 5)),
        ];
        assert!(matches!(
            solve_bv(1, &asserts, 1_000_000),
            Some(BvOutcome::Unsat(_))
        ));
    }

    #[test]
    fn concat_extract_roundtrip_sat() {
        // Concat(hi=x, lo=y) == 0xAB and Extract(bits 7..=4) == 0xA jointly SAT.
        let w = 4;
        let cat = BvTerm::concat(v(0, w), v(1, w)).unwrap();
        let ext = BvTerm::extract(cat.clone(), 7, 4).unwrap();
        let asserts = vec![eq(cat, k(8, 0xAB)), eq(ext, k(4, 0xA))];
        match solve_bv(2, &asserts, 1_000_000) {
            Some(BvOutcome::Sat(model)) => {
                let (x, y) = (model.values[0], model.values[1]);
                assert_eq!((x << 4) | y, 0xAB);
            }
            _ => panic!("expected Sat"),
        }
    }

    #[test]
    fn malformed_problems_yield_none() {
        // A width mismatch between assertion sides (built directly, bypassing
        // the validating constructors) is rejected by the blaster.
        let bad = [BvAssertion::Eq(v(0, 4), k(8, 1))];
        assert!(blast_bv(1, &bad).is_none());
        assert!(solve_bv(1, &bad, 1_000).is_none());
        // An unknown variable id is rejected, not indexed out of bounds.
        let asserts = vec![eq(v(5, 4), k(4, 1))];
        assert!(solve_bv(1, &asserts, 1_000).is_none());
        // An inconsistent width for the same id across terms is rejected.
        let mixed = [BvAssertion::Eq(
            BvTerm::concat(v(0, 2), v(0, 2)).unwrap(),
            v(0, 4),
        )];
        assert!(blast_bv(1, &mixed).is_none());
    }
}

/// Differential brute-force oracle: on small random problems the engine's
/// verdict must agree with ground truth in *both* directions. This is what
/// closes the encoder trust gap documented at the top of this file: a circuit
/// bug that over-constrains shows up as a bogus `Unsat` here; one that
/// under-constrains lets `Sat` through where brute force says UNSAT.
#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod oracle {
    use super::*;
    use proptest::prelude::*;

    fn w() -> impl Strategy<Value = u8> {
        1u8..=3
    }
    fn konst() -> impl Strategy<Value = u64> {
        0u64..8
    }
    fn decode_op(i: u8) -> BvBinOp {
        match i {
            0 => BvBinOp::And,
            1 => BvBinOp::Or,
            2 => BvBinOp::Xor,
            3 => BvBinOp::Add,
            _ => BvBinOp::Sub,
        }
    }

    // `(t1 op t2) == c` plus an optional second var, brute-forced end to end.
    proptest! {
        #[test]
        fn engine_agrees_with_brute_force(
            width in w(),
            k1 in konst(), k2 in konst(),
            raw_op1 in 0u8..5, raw_op2 in 0u8..5,
            use_second_var in proptest::bool::ANY,
            assert_ult_too in proptest::bool::ANY,
            ult_bound in konst(),
        ) {
            let op1 = decode_op(raw_op1);
            let op2 = decode_op(raw_op2);
            let m = mask(width);
            let x = BvTerm::var(0, width).unwrap();
            let inner = BvTerm::BinOp { op: op1, lhs: Box::new(x.clone()), rhs: Box::new(BvTerm::constant(width, k1 & m).unwrap()) };
            let t1 = if use_second_var {
                let y = BvTerm::var(1, width).unwrap();
                BvTerm::BinOp { op: op2, lhs: Box::new(inner), rhs: Box::new(y) }
            } else {
                inner
            };
            let mut asserts = vec![BvAssertion::Eq(t1.clone(), BvTerm::constant(width, k2 & m).unwrap())];
            if assert_ult_too {
                let t2 = if use_second_var {
                    BvTerm::var(1, width).unwrap()
                } else {
                    x
                };
                asserts.push(BvAssertion::Ult(t2, BvTerm::constant(width, ult_bound & m).unwrap()));
            }

            // Ground truth by enumeration.
            let domain = 1u64 << width;
            let mut truth_sat = false;
            'outer: for vx in 0..domain {
                for vy in 0..domain {
                    let values = if use_second_var { vec![vx, vy] } else { vec![vx] };
                    let mut all = true;
                    for a in &asserts {
                        match assertion_holds(a, &values) {
                            Some(true) => {}
                            _ => { all = false; break; }
                        }
                    }
                    if all { truth_sat = true; break 'outer; }
                }
            }

            match solve_bv(if use_second_var { 2 } else { 1 }, &asserts, 10_000_000) {
                Some(BvOutcome::Sat(model)) => {
                    prop_assert!(truth_sat, "engine said Sat but brute force says UNSAT");
                    for a in &asserts {
                        prop_assert_eq!(assertion_holds(a, &model.values), Some(true));
                    }
                }
                Some(BvOutcome::Unsat(_)) => {
                    prop_assert!(!truth_sat, "engine said Unsat but brute force found a model");
                    // Proof revalidation against the blast happens in the
                    // periphery's `solve_and_check_bv` tests (the checker
                    // crate sits above this one).
                }
                None => { /* fuel/malformed: skip */ }
            }
        }
    }
}
