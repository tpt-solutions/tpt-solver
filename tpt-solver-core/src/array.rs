//! QF_AX array theory — ground arrays with positive equalities (Phase 5).
//!
//! Fragment: conjunctions of *equalities* between element terms
//! ([`ElemExpr`]: variables, constants, `select`) and array terms
//! ([`ArrayExpr`]: array variables, constant arrays, `store`). There are no
//! disequalities yet — see the todo notes; with positive equalities alone,
//! unsatisfiability always manifests as two **distinct constants** being
//! proven equal, which is exactly the shape the certificate captures.
//!
//! Decision procedure: congruence closure modulo the select-over-store axioms,
//! fuel-bounded:
//!
//! * `select(store(a, i, v), i) ≡ v` (same index),
//! * `select(store(a, i, v), j) ≡ select(a, j)` when `i, j` are distinct
//!   representatives (a *walk* through the store),
//! * `select(constarray(v), j) ≡ v`,
//! * congruence: equal arrays read at equal indices give equal elements.
//!
//! Certificate story:
//!
//! * **UNSAT** — [`AxCertificate`] lists the axiom instances used, each a term
//!   with purely *local*, syntactically checkable shape (`select` over a
//!   literal `store`, etc.) plus a precondition decidable by the checker's own
//!   union-find at application time. The kernel never sees engine internals.
//!   Constants can only enter a class through the input assertions or through
//!   a store/constant-array operand (both part of the anchored term shape), so
//!   fabricated facts cannot manufacture a clash. The engine additionally
//!   replays every certificate with a naive mirror of the kernel's rules and
//!   refuses to claim `Unsat` unless the replay reproduces the clash.
//! * **SAT** — a concrete [`ArrayModel`] (per-array default + sorted finite
//!   entries). The engine self-evaluates all assertions before claiming
//!   success; the kernel re-evaluates independently
//!   (`tpt_solver_check::array::check_array_model`).
//!
//! All traversals are iterative and everything is fuel-bounded; malformed
//! input yields `None` ("could not decide"), never a panic.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

/// An element-sorted term: variables/constants, or a selection out of an
/// array.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ElemExpr {
    /// An element variable (dense id `0..evar_count`).
    Var(u32),
    /// A concrete element.
    Const(u64),
    /// `Select(arr, idx)` — read the array at an index.
    Select(Box<ArrayExpr>, Box<ElemExpr>),
}

/// An array-sorted term.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayExpr {
    /// An array variable (dense id `0..avar_count`).
    AVar(u32),
    /// The array constantly equal to `v` at every index.
    ConstArray(Box<ElemExpr>),
    /// `Store(arr, idx, val)` — functional update.
    Store(Box<ArrayExpr>, Box<ElemExpr>, Box<ElemExpr>),
}

/// An assertion of the array problem (positive equalities only).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrAssertion {
    /// Two element terms are equal.
    ElemsEqual(ElemExpr, ElemExpr),
    /// Two array terms are equal.
    ArraysEqual(ArrayExpr, ArrayExpr),
}

impl ElemExpr {
    /// Element variable.
    pub fn var(id: u32) -> ElemExpr {
        ElemExpr::Var(id)
    }
    /// Element constant.
    pub fn konst(v: u64) -> ElemExpr {
        ElemExpr::Const(v)
    }
    /// Selection term.
    pub fn select(arr: ArrayExpr, idx: ElemExpr) -> ElemExpr {
        ElemExpr::Select(Box::new(arr), Box::new(idx))
    }
}

impl ArrayExpr {
    /// Array variable.
    pub fn avar(id: u32) -> ArrayExpr {
        ArrayExpr::AVar(id)
    }
    /// Constant array.
    pub fn const_array(v: ElemExpr) -> ArrayExpr {
        ArrayExpr::ConstArray(Box::new(v))
    }
    /// Functional update term.
    pub fn store(arr: ArrayExpr, idx: ElemExpr, val: ElemExpr) -> ArrayExpr {
        ArrayExpr::Store(Box::new(arr), Box::new(idx), Box::new(val))
    }
}

/// A concrete array: a default value plus finitely many overriding entries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteArray {
    /// Value at indices without an entry.
    pub default: u64,
    /// Overriding `(index, value)` pairs, sorted strictly ascending by index.
    pub entries: Vec<(u64, u64)>,
}

impl ConcreteArray {
    /// The constant array `v`.
    pub fn constant(v: u64) -> ConcreteArray {
        ConcreteArray {
            default: v,
            entries: Vec::new(),
        }
    }

    /// Read at an index (binary search over the entries).
    pub fn read(&self, idx: u64) -> u64 {
        match self.entries.binary_search_by_key(&idx, |&(i, _)| i) {
            Ok(pos) => self.entries[pos].1,
            Err(_) => self.default,
        }
    }

    /// Functional update: this array written at `idx`.
    pub fn written(&self, idx: u64, val: u64) -> ConcreteArray {
        let mut out = self.clone();
        match out.entries.binary_search_by_key(&idx, |&(i, _)| i) {
            Ok(pos) => out.entries[pos].1 = val,
            Err(pos) => out.entries.insert(pos, (idx, val)),
        }
        out
    }
}

/// A claimed model: one concrete array per array variable, one value per
/// element variable (both indexed by dense id).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ArrayModel {
    /// Content per array variable id.
    pub arrays: Vec<ConcreteArray>,
    /// Value per element variable id.
    pub elems: Vec<u64>,
}

/// Maximum expression depth accepted by evaluation/interning; deeper
/// adversarial inputs degrade to `None` instead of overflowing the stack.
const MAX_DEPTH: u32 = 2048;

/// Evaluate an element term under a model. `None` if a variable id falls
/// outside the model or the term is pathologically deep.
pub fn eval_elem(e: &ElemExpr, m: &ArrayModel) -> Option<u64> {
    fn go(e: &ElemExpr, m: &ArrayModel, d: u32) -> Option<u64> {
        if d > MAX_DEPTH {
            return None;
        }
        match e {
            ElemExpr::Var(id) => m.elems.get(*id as usize).copied(),
            ElemExpr::Const(v) => Some(*v),
            ElemExpr::Select(arr, idx) => {
                let a = eval_array_go(arr, m, d + 1)?;
                let i = go(idx, m, d + 1)?;
                Some(a.read(i))
            }
        }
    }
    go(e, m, 0)
}

/// Evaluate an array term under a model into its concrete content.
pub fn eval_array(a: &ArrayExpr, m: &ArrayModel) -> Option<ConcreteArray> {
    eval_array_go(a, m, 0)
}

fn eval_array_go(a: &ArrayExpr, m: &ArrayModel, d: u32) -> Option<ConcreteArray> {
    if d > MAX_DEPTH {
        return None;
    }
    match a {
        ArrayExpr::AVar(id) => m.arrays.get(*id as usize).cloned(),
        ArrayExpr::ConstArray(v) => Some(ConcreteArray::constant(eval_elem(v, m)?)),
        ArrayExpr::Store(base, idx, val) => {
            let b = eval_array_go(base, m, d + 1)?;
            let i = eval_elem(idx, m)?;
            let v = eval_elem(val, m)?;
            Some(b.written(i, v))
        }
    }
}

/// Do all assertions hold under `model`? `None` on malformed/short models.
pub fn assertions_hold(assertions: &[ArrAssertion], model: &ArrayModel) -> Option<bool> {
    for a in assertions {
        let ok = match a {
            ArrAssertion::ElemsEqual(l, r) => eval_elem(l, model)? == eval_elem(r, model)?,
            ArrAssertion::ArraysEqual(l, r) => eval_array(l, model)? == eval_array(r, model)?,
        };
        if !ok {
            return Some(false);
        }
    }
    Some(true)
}

// ---------------------------------------------------------------------------
// Certificate types
// ---------------------------------------------------------------------------

/// One axiom instance used in an UNSAT derivation. Every variant carries only
/// terms with *local* syntactic shape, so a checker can validate each instance
/// without any engine internals: constants can enter a class only through the
/// input assertions or through a `store`/`constarray` operand that is part of
/// the checked shape itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AxFact {
    /// `select(store(a, i, v), j)` with `i ≡ j` at application time yields `v`.
    SelectOfStoreIsIndex {
        /// The whole `select` term (its array argument must be a literal
        /// `store`).
        select: ElemExpr,
    },
    /// `select(store(a, i, v), j)` with `i ≢ j` at application time equals
    /// `inner`, which must be literally `select(a, j)` (the store walked
    /// through).
    SelectOfStoreWalk {
        /// The whole `select` term.
        select: ElemExpr,
        /// The walked-through `select(a, j)` term.
        inner: ElemExpr,
    },
    /// `select(constarray(v), j)` equals `v`, unconditionally.
    SelectOfConstArray {
        /// The whole `select` term (array argument must be a literal
        /// `constarray`).
        select: ElemExpr,
    },
    /// Two `select`s whose array arguments are united and whose indices are
    /// united are themselves equal.
    CongruentSelects {
        /// Left `select` term.
        left: ElemExpr,
        /// Right `select` term.
        right: ElemExpr,
    },
}

/// UNSAT evidence: the axiom instances used by the closure. The engine replays
/// this list with its own naive mirror of the checker's rules before claiming
/// `Unsat`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AxCertificate {
    /// Axiom instances, in derivation order.
    pub facts: Vec<AxFact>,
}

/// The engine's array-theory answer with its certificate.
#[derive(Clone, Debug)]
pub enum AxOutcome {
    /// Satisfiable, with a concrete model (kernel-recheckable).
    Sat(ArrayModel),
    /// Unsatisfiable, with the axiom-instance certificate (kernel-recheckable).
    Unsat(AxCertificate),
}

// ---------------------------------------------------------------------------
// Closure machinery
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    EVar(u32),
    EConst(u64),
    Select(usize, usize),
    AVar(u32),
    ConstArr(usize),
    Store(usize, usize, usize),
}

/// Structural interner + union-find with constant-value propagation.
struct Closure {
    ek: BTreeMap<ElemExpr, usize>,
    ak: BTreeMap<ArrayExpr, usize>,
    kinds: Vec<Kind>,
    /// Canonical term per element cell, keyed by cell id.
    eterm: BTreeMap<usize, ElemExpr>,
    /// Canonical term per array cell, keyed by cell id.
    aterm: BTreeMap<usize, ArrayExpr>,
    evar_cell: Vec<Option<usize>>,
    avar_cell: Vec<Option<usize>>,
    parent: Vec<usize>,
    rank: Vec<u8>,
    val: Vec<Option<u64>>,
}

impl Closure {
    fn new() -> Closure {
        Closure {
            ek: BTreeMap::new(),
            ak: BTreeMap::new(),
            kinds: Vec::new(),
            eterm: BTreeMap::new(),
            aterm: BTreeMap::new(),
            evar_cell: Vec::new(),
            avar_cell: Vec::new(),
            parent: Vec::new(),
            rank: Vec::new(),
            val: Vec::new(),
        }
    }

    fn push_cell(&mut self, k: Kind) -> usize {
        let id = self.kinds.len();
        self.kinds.push(k);
        self.parent.push(id);
        self.rank.push(0);
        self.val.push(None);
        id
    }

    fn intern_elem(&mut self, e: &ElemExpr, d: u32) -> Option<usize> {
        if d > MAX_DEPTH {
            return None;
        }
        if let Some(&c) = self.ek.get(e) {
            return Some(c);
        }
        let cell = match e {
            ElemExpr::Var(id) => {
                let id = *id as usize;
                while self.evar_cell.len() <= id {
                    self.evar_cell.push(None);
                }
                let c = self.push_cell(Kind::EVar(id as u32));
                self.evar_cell[id] = Some(c);
                c
            }
            ElemExpr::Const(v) => {
                let c = self.push_cell(Kind::EConst(*v));
                self.val[c] = Some(*v);
                c
            }
            ElemExpr::Select(arr, idx) => {
                let ac = self.intern_array(arr, d + 1)?;
                let ic = self.intern_elem(idx, d + 1)?;
                self.push_cell(Kind::Select(ac, ic))
            }
        };
        self.eterm.insert(cell, e.clone());
        self.ek.insert(e.clone(), cell);
        Some(cell)
    }

    fn intern_array(&mut self, a: &ArrayExpr, d: u32) -> Option<usize> {
        if d > MAX_DEPTH {
            return None;
        }
        if let Some(&c) = self.ak.get(a) {
            return Some(c);
        }
        let cell = match a {
            ArrayExpr::AVar(id) => {
                let id = *id as usize;
                while self.avar_cell.len() <= id {
                    self.avar_cell.push(None);
                }
                let c = self.push_cell(Kind::AVar(id as u32));
                self.avar_cell[id] = Some(c);
                c
            }
            ArrayExpr::ConstArray(v) => {
                let vc = self.intern_elem(v, d + 1)?;
                self.push_cell(Kind::ConstArr(vc))
            }
            ArrayExpr::Store(arr, idx, val) => {
                let bc = self.intern_array(arr, d + 1)?;
                let ic = self.intern_elem(idx, d + 1)?;
                let vc = self.intern_elem(val, d + 1)?;
                self.push_cell(Kind::Store(bc, ic, vc))
            }
        };
        self.aterm.insert(cell, a.clone());
        self.ak.insert(a.clone(), cell);
        Some(cell)
    }

    fn find(&mut self, x: usize) -> usize {
        let mut r = x;
        while self.parent[r] != r {
            r = self.parent[r];
        }
        let mut c = x;
        while self.parent[c] != r {
            let next = self.parent[c];
            self.parent[c] = r;
            c = next;
        }
        r
    }

    /// Unite two cells; returns `true` on a clash (two distinct constants
    /// forced together). Values propagate to the class root.
    fn unite(&mut self, a: usize, b: usize) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        let clash = matches!((self.val[ra], self.val[rb]), (Some(x), Some(y)) if x != y);
        let vopt = match (self.val[ra], self.val[rb]) {
            (Some(x), _) => Some(x),
            (None, y) => y,
        };
        if self.rank[ra] < self.rank[rb] {
            self.parent[ra] = rb;
        } else if self.rank[ra] > self.rank[rb] {
            self.parent[rb] = ra;
        } else {
            self.parent[rb] = ra;
            self.rank[ra] += 1;
        }
        let root = self.find(ra);
        self.val[root] = vopt;
        clash
    }

    /// Reset only the union-find state, keeping the interning tables.
    fn reset_uf(&mut self) {
        for i in 0..self.parent.len() {
            self.parent[i] = i;
            self.rank[i] = 0;
        }
        for i in 0..self.kinds.len() {
            self.val[i] = match self.kinds[i] {
                Kind::EConst(v) => Some(v),
                _ => None,
            };
        }
    }

    /// Class value at a cell's root (constants propagate here).
    fn root_val(&mut self, c: usize) -> Option<u64> {
        let r = self.find(c);
        self.val[r]
    }
}

/// Destructure a `select` term into `(array term, index term)`.
fn sel_parts(s: &ElemExpr) -> Option<(&ArrayExpr, &ElemExpr)> {
    match s {
        ElemExpr::Select(a, j) => Some((a, j)),
        _ => None,
    }
}

/// Apply one fact under the current partition using ONLY its local term shape,
/// exactly as the trusted kernel does. Returns `false` when a precondition
/// does not hold yet (the stratified replay retries later).
fn apply_fact(cl: &mut Closure, f: &AxFact) -> bool {
    match f {
        AxFact::SelectOfConstArray { select } => apply_sel_const_array(cl, select),
        AxFact::SelectOfStoreIsIndex { select } => apply_sel_store_is_index(cl, select),
        AxFact::SelectOfStoreWalk { select, inner } => apply_sel_store_walk(cl, select, inner),
        AxFact::CongruentSelects { left, right } => apply_congruent_selects(cl, left, right),
    }
}

fn apply_sel_const_array(cl: &mut Closure, select: &ElemExpr) -> bool {
    let Some((arr, _j)) = sel_parts(select) else {
        return false;
    };
    let ArrayExpr::ConstArray(v) = arr else {
        return false;
    };
    let sc = match cl.intern_elem(select, 0) {
        Some(c) => c,
        None => return false,
    };
    let vc = match cl.intern_elem(v, 0) {
        Some(c) => c,
        None => return false,
    };
    if cl.find(sc) != cl.find(vc) {
        cl.unite(sc, vc);
    }
    true
}

fn apply_sel_store_is_index(cl: &mut Closure, select: &ElemExpr) -> bool {
    let Some((arr, j)) = sel_parts(select) else {
        return false;
    };
    let ArrayExpr::Store(_a, i, v) = arr else {
        return false;
    };
    let sc = match cl.intern_elem(select, 0) {
        Some(c) => c,
        None => return false,
    };
    let ic = match cl.ek.get(i.as_ref()).copied() {
        Some(c) => c,
        None => return false,
    };
    let jc = match cl.ek.get(j).copied() {
        Some(c) => c,
        None => return false,
    };
    let vc = match cl.ek.get(v.as_ref()).copied() {
        Some(c) => c,
        None => return false,
    };
    if cl.find(ic) != cl.find(jc) {
        return false; // precondition not yet established
    }
    if cl.find(sc) != cl.find(vc) {
        cl.unite(sc, vc);
    }
    true
}

fn apply_sel_store_walk(cl: &mut Closure, select: &ElemExpr, inner: &ElemExpr) -> bool {
    let Some((arr, j)) = sel_parts(select) else {
        return false;
    };
    let ArrayExpr::Store(a, i, _v) = arr else {
        return false;
    };
    // The walked-through term must be literally `select(a, j)`.
    let expected = ElemExpr::Select(Box::new((**a).clone()), Box::new((*j).clone()));
    if inner != &expected {
        return false;
    }
    let sc = match cl.intern_elem(select, 0) {
        Some(c) => c,
        None => return false,
    };
    let ic = match cl.ek.get(i.as_ref()).copied() {
        Some(c) => c,
        None => return false,
    };
    let jc = match cl.ek.get(j).copied() {
        Some(c) => c,
        None => return false,
    };
    if cl.find(ic) == cl.find(jc) {
        return false; // indices became equal; this walk no longer applies
    }
    let ic2 = match cl.intern_elem(inner, 0) {
        Some(c) => c,
        None => return false,
    };
    if cl.find(sc) != cl.find(ic2) {
        cl.unite(sc, ic2);
    }
    true
}

fn apply_congruent_selects(cl: &mut Closure, left: &ElemExpr, right: &ElemExpr) -> bool {
    let (Some((al, jl)), Some((ar, jr))) = (sel_parts(left), sel_parts(right)) else {
        return false;
    };
    let lc = match cl.intern_elem(left, 0) {
        Some(c) => c,
        None => return false,
    };
    let rc = match cl.intern_elem(right, 0) {
        Some(c) => c,
        None => return false,
    };
    let alc = cl.ak.get(al).copied();
    let jlc = cl.ek.get(jl).copied();
    let arc = cl.ak.get(ar).copied();
    let jrc = cl.ek.get(jr).copied();
    let (Some(alc), Some(jlc), Some(arc), Some(jrc)) = (alc, jlc, arc, jrc) else {
        return false;
    };
    if cl.find(alc) != cl.find(arc) || cl.find(jlc) != cl.find(jrc) {
        return false; // preconditions not yet established
    }
    if cl.find(lc) != cl.find(rc) {
        cl.unite(lc, rc);
    }
    true
}

/// Naive replay of `facts` over a fresh partition seeded with the forced
/// unions; returns `true` iff some class ends holding two distinct constants.
/// The engine runs this mirror of the kernel's algorithm before it may claim
/// `Unsat`, so only certificates that genuinely replay to a clash ship.
fn replay_finds_clash(cl: &mut Closure, forced: &[(usize, usize)], facts: &[AxFact]) -> bool {
    cl.reset_uf();
    let mut clash = false;
    for &(x, y) in forced {
        if cl.find(x) != cl.find(y) && cl.unite(x, y) {
            clash = true;
        }
    }
    let mut consumed = alloc::vec![false; facts.len()];
    loop {
        let mut progress = false;
        for (fi, f) in facts.iter().enumerate() {
            if consumed[fi] {
                continue;
            }
            if apply_fact(cl, f) {
                consumed[fi] = true;
                progress = true;
            }
        }
        if !progress || clash {
            break;
        }
    }
    if !clash {
        // Clash scan: two distinct constant kinds in one class.
        'scan: for c in 0..cl.kinds.len() {
            if !matches!(cl.kinds[c], Kind::EConst(_)) {
                continue;
            }
            for d in (c + 1)..cl.kinds.len() {
                if matches!(cl.kinds[d], Kind::EConst(_))
                    && cl.find(c) == cl.find(d)
                    && cl.kinds[c] != cl.kinds[d]
                {
                    clash = true;
                    break 'scan;
                }
            }
        }
    }
    clash
}

/// Decide a conjunction of ground array equalities.
///
/// Returns `None` when malformed, too deep, or out of fuel — surfaced
/// downstream as "could not decide", never as a guess.
pub fn solve_arrays(
    avar_count: u32,
    evar_count: u32,
    assertions: &[ArrAssertion],
    fuel_budget: u64,
) -> Option<AxOutcome> {
    let mut fuel = crate::fuel::Fuel::new(fuel_budget);
    let mut cl = Closure::new();
    for _ in 0..evar_count {
        cl.evar_cell.push(None);
    }
    for _ in 0..avar_count {
        cl.avar_cell.push(None);
    }

    let mut forced: Vec<(usize, usize)> = Vec::new();
    for a in assertions {
        match a {
            ArrAssertion::ElemsEqual(l, r) => {
                let x = cl.intern_elem(l, 0)?;
                let y = cl.intern_elem(r, 0)?;
                forced.push((x, y));
            }
            ArrAssertion::ArraysEqual(l, r) => {
                let x = cl.intern_array(l, 0)?;
                let y = cl.intern_array(r, 0)?;
                forced.push((x, y));
            }
        }
    }

    // Index pairs whose distinctness was assumed by a walkthrough fact and
    // later invalidated; forcing them equal and re-running restores soundness.
    let mut extra_pairs: Vec<(usize, usize)> = Vec::new();

    loop {
        if !fuel.burn_one() {
            return None;
        }
        cl.reset_uf();
        let combined: Vec<(usize, usize)> =
            forced.iter().chain(extra_pairs.iter()).copied().collect();
        let mut clash = false;
        for &(x, y) in &combined {
            if cl.find(x) != cl.find(y) && cl.unite(x, y) {
                clash = true;
            }
        }

        let mut facts: Vec<AxFact> = Vec::new();
        let mut queue: Vec<usize> = (0..cl.kinds.len())
            .filter(|&c| matches!(cl.kinds[c], Kind::Select(..)))
            .collect();
        let mut qi = 0usize;
        let mut sel_reg: BTreeMap<(usize, usize), usize> = BTreeMap::new();
        for &s in &queue {
            if let Kind::Select(a, j) = cl.kinds[s] {
                sel_reg.insert((a, j), s);
            }
        }
        let mut cmap: BTreeMap<(usize, usize), usize> = BTreeMap::new();

        let mut changed = true;
        while changed && !clash {
            if !fuel.burn_one() {
                return None;
            }
            changed = false;
            while qi < queue.len() && !clash {
                if !fuel.burn_one() {
                    return None;
                }
                let s = queue[qi];
                qi += 1;
                let Kind::Select(ac, jc) = cl.kinds[s] else {
                    continue;
                };
                let prep = cl.find(ac);
                match cl.kinds[prep] {
                    Kind::ConstArr(vc) => {
                        if cl.find(s) != cl.find(vc) {
                            let st = cl.eterm.get(&s).cloned()?;
                            facts.push(AxFact::SelectOfConstArray { select: st });
                            clash = cl.unite(s, vc);
                            changed = true;
                        }
                    }
                    Kind::Store(b, ic, vc) => {
                        let fi = cl.find(ic);
                        let fj = cl.find(jc);
                        if fi == fj {
                            if cl.find(s) != cl.find(vc) {
                                let st = cl.eterm.get(&s).cloned()?;
                                facts.push(AxFact::SelectOfStoreIsIndex { select: st });
                                clash = cl.unite(s, vc);
                                changed = true;
                            }
                        } else {
                            let (Some(st), Some(bt), Some(jt)) = (
                                cl.eterm.get(&s).cloned(),
                                cl.aterm.get(&b).cloned(),
                                cl.eterm.get(&jc).cloned(),
                            ) else {
                                return None;
                            };
                            let inner = ElemExpr::Select(Box::new(bt), Box::new(jt));
                            let s2 = match sel_reg.get(&(b, jc)) {
                                Some(&x) => x,
                                None => {
                                    let c2 = cl.intern_elem(&inner, 0)?;
                                    sel_reg.insert((b, jc), c2);
                                    queue.push(c2);
                                    c2
                                }
                            };
                            if cl.find(s) != cl.find(s2) {
                                facts.push(AxFact::SelectOfStoreWalk { select: st, inner });
                                clash = cl.unite(s, s2);
                                changed = true;
                            }
                        }
                    }
                    _ => {}
                }
                match congrue(&mut cl, &mut cmap, s, &mut facts) {
                    None => return None,
                    Some(true) => clash = true,
                    Some(false) => {}
                }
            }
            // Full congruence sweep: representatives may have shifted.
            let snapshot: Vec<usize> = queue.clone();
            for s in snapshot {
                match congrue(&mut cl, &mut cmap, s, &mut facts) {
                    None => return None,
                    Some(true) => {
                        clash = true;
                        changed = true;
                    }
                    Some(false) => {}
                }
            }
        }

        if clash {
            if replay_finds_clash(&mut cl, &combined, &facts) {
                return Some(AxOutcome::Unsat(AxCertificate { facts }));
            }
            // Ban invalidated walkthrough assumptions and retry.
            let mut added = false;
            let suspected: Vec<(usize, usize)> = facts
                .iter()
                .filter_map(|f| walk_index_pair(&cl, f))
                .collect();
            for (ic, jc) in suspected {
                if cl.find(ic) == cl.find(jc) && !extra_pairs.contains(&(ic, jc)) {
                    extra_pairs.push((ic, jc));
                    added = true;
                }
            }
            if !added {
                return None; // cannot repair honestly; refuse to guess
            }
            continue;
        }
        break;
    }

    // No clash: extract a model and self-check it before claiming Sat.
    let selects: Vec<usize> = (0..cl.kinds.len())
        .filter(|&c| matches!(cl.kinds[c], Kind::Select(..)))
        .collect();
    let mut reg: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    for c in 0..cl.kinds.len() {
        if let Kind::Select(a, j) = cl.kinds[c] {
            reg.insert((a, j), c);
        }
    }
    build_model(&mut cl, avar_count, evar_count, &selects, &reg, assertions).map(AxOutcome::Sat)
}

/// Index pair `(i, j)` whose distinctness a walkthrough fact assumed, used by
/// the ban-and-retry loop. `None` for other fact shapes or malformed terms.
fn walk_index_pair(cl: &Closure, f: &AxFact) -> Option<(usize, usize)> {
    match f {
        AxFact::SelectOfStoreWalk { select, .. } => {
            let (arr, j) = sel_parts(select)?;
            let ArrayExpr::Store(_, i, _) = arr else {
                return None;
            };
            let ic = cl.ek.get(i.as_ref()).copied()?;
            let jc = cl.ek.get(j).copied()?;
            Some((ic, jc))
        }
        _ => None,
    }
}

/// Congruence: register this select under its current representative key and
/// unite it with any earlier select sharing that key.
///
/// * `Some(true)` — united, clash detected.
/// * `Some(false)` — registered or already equal.
/// * `None` — internal invariant break (missing term); caller degrades to
///   "could not decide".
fn congrue(
    cl: &mut Closure,
    cmap: &mut BTreeMap<(usize, usize), usize>,
    s: usize,
    facts: &mut Vec<AxFact>,
) -> Option<bool> {
    let Kind::Select(ac, jc) = cl.kinds[s] else {
        return Some(false);
    };
    let key = (cl.find(ac), cl.find(jc));
    if let Some(&t) = cmap.get(&key) {
        if t != s && cl.find(t) != cl.find(s) {
            let lt = cl.eterm.get(&t).cloned()?;
            let rt = cl.eterm.get(&s).cloned()?;
            facts.push(AxFact::CongruentSelects {
                left: lt,
                right: rt,
            });
            return Some(cl.unite(t, s));
        }
        return Some(false);
    }
    cmap.insert(key, s);
    Some(false)
}

/// Extract a concrete model from the clash-free closure and self-check it.
/// Returns `None` when any residual inconsistency remains — degraded to
/// "could not decide", never a wrong `Sat`.
fn build_model(
    cl: &mut Closure,
    avar_count: u32,
    evar_count: u32,
    selects: &[usize],
    sel_reg: &BTreeMap<(usize, usize), usize>,
    assertions: &[ArrAssertion],
) -> Option<ArrayModel> {
    // Element variable values: their class constant if any, else 0.
    let mut elems: Vec<u64> = Vec::with_capacity(evar_count as usize);
    for id in 0..evar_count as usize {
        let v = match cl.evar_cell.get(id).copied().flatten() {
            Some(c) => cl.root_val(c).unwrap_or(0),
            None => 0,
        };
        elems.push(v);
    }

    // Required readings per root array cell: index-class-root -> value.
    let mut req: BTreeMap<usize, BTreeMap<usize, u64>> = BTreeMap::new();
    let mut resolved: BTreeMap<usize, ()> = BTreeMap::new();
    let mut stack: Vec<usize> = selects.to_vec();
    while let Some(s) = stack.pop() {
        if resolved.contains_key(&s) {
            continue;
        }
        let Kind::Select(ac, jc) = cl.kinds[s] else {
            continue;
        };
        let arr_term = cl.aterm.get(&ac).cloned()?;
        match &arr_term {
            ArrayExpr::AVar(_) => {
                let ar = cl.find(ac);
                let ir = cl.find(jc);
                let v = cl.root_val(s).unwrap_or(0);
                req.entry(ar).or_default().insert(ir, v);
                resolved.insert(s, ());
            }
            ArrayExpr::ConstArray(_) => {
                resolved.insert(s, ());
            }
            ArrayExpr::Store(bt, it, _vt) => {
                let bc = *cl.ak.get(bt.as_ref())?;
                let ic = cl.ek.get(it.as_ref()).copied()?;
                if cl.find(ic) == cl.find(jc) {
                    resolved.insert(s, ());
                } else {
                    let s2 = *sel_reg.get(&(bc, jc))?;
                    if resolved.contains_key(&s2) {
                        resolved.insert(s, ());
                    } else {
                        stack.push(s);
                        stack.push(s2);
                    }
                }
            }
        }
    }

    // Concrete members per element-class root (constants + chosen var values).
    let mut members_of: BTreeMap<usize, Vec<u64>> = BTreeMap::new();
    for c in 0..cl.kinds.len() {
        match cl.kinds[c] {
            Kind::EConst(v) => members_of.entry(cl.find(c)).or_default().push(v),
            Kind::EVar(id) => {
                if let Some(&val) = elems.get(id as usize) {
                    members_of.entry(cl.find(c)).or_default().push(val);
                }
            }
            _ => {}
        }
    }

    // Materialize arrays; array-equal variables share a class root, hence
    // identical content.
    let mut arrays: Vec<ConcreteArray> = Vec::with_capacity(avar_count as usize);
    for id in 0..avar_count as usize {
        let mut entries_map: BTreeMap<u64, u64> = BTreeMap::new();
        if let Some(Some(cell)) = cl.avar_cell.get(id).copied() {
            let r = cl.find(cell);
            if let Some(m) = req.get(&r) {
                for (ir, v) in m {
                    if let Some(members) = members_of.get(ir) {
                        for mem in members {
                            entries_map.insert(*mem, *v);
                        }
                    }
                }
            }
        }
        arrays.push(ConcreteArray {
            default: 0,
            entries: entries_map.into_iter().collect(),
        });
    }

    let model = ArrayModel { arrays, elems };
    if assertions_hold(assertions, &model) == Some(true) {
        Some(model)
    } else {
        None
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
mod tests {
    use super::*;

    fn av(id: u32) -> ArrayExpr {
        ArrayExpr::avar(id)
    }
    fn ev(id: u32) -> ElemExpr {
        ElemExpr::var(id)
    }
    fn k(v: u64) -> ElemExpr {
        ElemExpr::konst(v)
    }

    #[test]
    fn sat_same_index_read() {
        // select(store(a, 3, 9), 3) == 9 holds by the axiom itself.
        let sel = ElemExpr::select(ArrayExpr::store(av(0), k(3), k(9)), k(3));
        let asserts = vec![ArrAssertion::ElemsEqual(sel, k(9))];
        match solve_arrays(1, 0, &asserts, 10_000) {
            Some(AxOutcome::Sat(m)) => {
                assert!(assertions_hold(&asserts, &m) == Some(true));
            }
            other => panic!("expected Sat, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn unsat_store_read_conflict() {
        // select(store(a, i, 5), i) == 7 forces 5 == 7: clash.
        let sel = ElemExpr::select(ArrayExpr::store(av(0), ev(0), k(5)), ev(0));
        let asserts = vec![ArrAssertion::ElemsEqual(sel, k(7))];
        match solve_arrays(1, 1, &asserts, 10_000) {
            Some(AxOutcome::Unsat(cert)) => {
                // The certificate must replay to the clash on its own, over
                // exactly the input unions plus the shipped facts.
                let mut cl = Closure::new();
                let mut forced = Vec::new();
                for a in &asserts {
                    if let ArrAssertion::ElemsEqual(l, r) = a {
                        let x = cl.intern_elem(l, 0).unwrap();
                        let y = cl.intern_elem(r, 0).unwrap();
                        forced.push((x, y));
                    }
                }
                assert!(replay_finds_clash(&mut cl, &forced, &cert.facts));
            }
            other => panic!("expected Unsat, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn unsat_via_congruent_indices() {
        // i == j asserted; select(store(a, i, 5), j) == 6 => clash 5 vs 6,
        // requiring SameIdx over congruence-derived index equality.
        let sel = ElemExpr::select(ArrayExpr::store(av(0), ev(0), k(5)), ev(1));
        let asserts = vec![
            ArrAssertion::ElemsEqual(ev(0), ev(1)),
            ArrAssertion::ElemsEqual(sel, k(6)),
        ];
        assert!(matches!(
            solve_arrays(1, 2, &asserts, 10_000),
            Some(AxOutcome::Unsat(_))
        ));
    }

    #[test]
    fn sat_walkthrough_case() {
        // x = select(store(b, 1, 5), 2); x == 7; select(b, 2) == 7.
        // Satisfiable: b[2] = 7 (the store is elsewhere). Exercises the walk
        // fact and model building through it.
        let sel = ElemExpr::select(ArrayExpr::store(av(0), k(1), k(5)), k(2));
        let selb = ElemExpr::select(av(0), k(2));
        let x = ev(1);
        let asserts = vec![
            ArrAssertion::ElemsEqual(x.clone(), sel),
            ArrAssertion::ElemsEqual(x, k(7)),
            ArrAssertion::ElemsEqual(selb, k(7)),
        ];
        match solve_arrays(1, 2, &asserts, 10_000) {
            Some(AxOutcome::Sat(m)) => {
                assert_eq!(m.elems[1], 7);
                assert!(assertions_hold(&asserts, &m) == Some(true));
            }
            other => panic!("expected Sat, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn sat_array_equality_shares_content() {
        // x == y; select(store(x, 0, 5), 0) == 5. Both x and y must end up
        // with identical content for the asserted equality to hold.
        let sel = ElemExpr::select(ArrayExpr::store(av(0), k(0), k(5)), k(0));
        let asserts = vec![
            ArrAssertion::ArraysEqual(av(0), av(1)),
            ArrAssertion::ElemsEqual(sel, k(5)),
        ];
        match solve_arrays(2, 0, &asserts, 10_000) {
            Some(AxOutcome::Sat(m)) => {
                assert_eq!(m.arrays[0], m.arrays[1]);
                assert!(assertions_hold(&asserts, &m) == Some(true));
            }
            other => panic!("expected Sat, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn const_array_cases() {
        // select(constarray(7), j) == 7 is SAT for any j.
        let sel = ElemExpr::select(ArrayExpr::const_array(k(7)), ev(0));
        let asserts = vec![ArrAssertion::ElemsEqual(sel.clone(), k(7))];
        assert!(matches!(
            solve_arrays(0, 1, &asserts, 10_000),
            Some(AxOutcome::Sat(_))
        ));
        // ...but == 8 is UNSAT.
        let asserts = vec![ArrAssertion::ElemsEqual(sel, k(8))];
        assert!(matches!(
            solve_arrays(0, 1, &asserts, 10_000),
            Some(AxOutcome::Unsat(_))
        ));
    }

    #[test]
    fn fuel_exhaustion_yields_none() {
        let sel = ElemExpr::select(ArrayExpr::store(av(0), ev(0), k(5)), ev(0));
        let asserts = vec![ArrAssertion::ElemsEqual(sel, k(7))];
        assert!(solve_arrays(1, 1, &asserts, 0).is_none());
    }
}
