//! QF_AX answer checking — the trusted kernel's array half.
//!
//! * **SAT** — substitute the claimed [`ArrayModel`] into the original
//!   assertions and re-evaluate them here, with this file's own evaluator.
//!   Models shorter than the declared variable counts are `Inconclusive`,
//!   never silently zero-padded.
//! * **UNSAT** — replay the certificate ([`AxCertificate`]): each fact is an
//!   axiom instance whose *local* term shape is checked syntactically and
//!   whose precondition is decided by this file's own union-find at
//!   application time. Facts are applied in stratified passes until none can
//!   fire further; UNSAT is confirmed iff some class ends holding two
//!   distinct constants. Nothing about the engine's search is trusted.

use crate::outcome::Outcome;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use tpt_solver_core::array::{ArrAssertion, ArrayExpr, ArrayModel, AxFact, ElemExpr};

/// Maximum accepted term depth; deeper inputs are [`Outcome::Inconclusive`].
const MAX_DEPTH: u32 = 2048;

fn eval_elem(e: &ElemExpr, m: &ArrayModel, d: u32) -> Option<u64> {
    if d > MAX_DEPTH {
        return None;
    }
    match e {
        ElemExpr::Var(id) => m.elems.get(*id as usize).copied(),
        ElemExpr::Const(v) => Some(*v),
        ElemExpr::Select(arr, idx) => {
            let a = eval_array(arr, m, d + 1)?;
            Some(a.read(eval_elem(idx, m, d + 1)?))
        }
    }
}

fn eval_array(
    a: &ArrayExpr,
    m: &ArrayModel,
    d: u32,
) -> Option<tpt_solver_core::array::ConcreteArray> {
    use tpt_solver_core::array::ConcreteArray;
    if d > MAX_DEPTH {
        return None;
    }
    match a {
        ArrayExpr::AVar(id) => m.arrays.get(*id as usize).cloned(),
        ArrayExpr::ConstArray(v) => Some(ConcreteArray::constant(eval_elem(v, m, d + 1)?)),
        ArrayExpr::Store(base, idx, val) => {
            let b = eval_array(base, m, d + 1)?;
            let i = eval_elem(idx, m, d + 1)?;
            let v = eval_elem(val, m, d + 1)?;
            Some(b.written(i, v))
        }
    }
}

/// Verify a claimed SAT model by substituting it into every assertion.
pub fn check_array_model(
    assertions: &[ArrAssertion],
    model: &ArrayModel,
    avar_count: u32,
    evar_count: u32,
) -> Outcome {
    if model.arrays.len() < avar_count as usize || model.elems.len() < evar_count as usize {
        return Outcome::Inconclusive;
    }
    for a in assertions {
        let ok = match a {
            ArrAssertion::ElemsEqual(l, r) => {
                let (Some(x), Some(y)) = (eval_elem(l, model, 0), eval_elem(r, model, 0)) else {
                    return Outcome::Inconclusive;
                };
                x == y
            }
            ArrAssertion::ArraysEqual(l, r) => {
                let (Some(x), Some(y)) = (eval_array(l, model, 0), eval_array(r, model, 0)) else {
                    return Outcome::Inconclusive;
                };
                x == y
            }
        };
        if !ok {
            return Outcome::Reject;
        }
    }
    Outcome::Accept
}

// ---------------------------------------------------------------------------
// UNSAT certificate replay
// ---------------------------------------------------------------------------

/// The kernel's own interner + union-find over the assertion terms.
struct KernelAx {
    ek: BTreeMap<ElemExpr, usize>,
    ak: BTreeMap<ArrayExpr, usize>,
    parent: Vec<usize>,
    rank: Vec<u8>,
    /// The cell's own constant, if it is a `Const` term. Immutable after
    /// interning so a merge can never mask which constants a class holds.
    konst: Vec<Option<u64>>,
}

impl KernelAx {
    fn new() -> KernelAx {
        KernelAx {
            ek: BTreeMap::new(),
            ak: BTreeMap::new(),
            parent: Vec::new(),
            rank: Vec::new(),
            konst: Vec::new(),
        }
    }

    fn push(&mut self, k: Option<u64>) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        self.rank.push(0);
        self.konst.push(k);
        id
    }

    fn ie(&mut self, e: &ElemExpr, d: u32) -> Option<usize> {
        if d > MAX_DEPTH {
            return None;
        }
        if let Some(&c) = self.ek.get(e) {
            return Some(c);
        }
        let c = match e {
            ElemExpr::Var(_) | ElemExpr::Const(_) => {
                let v = match e {
                    ElemExpr::Const(v) => Some(*v),
                    _ => None,
                };
                self.push(v)
            }
            ElemExpr::Select(arr, idx) => {
                self.ia(arr, d + 1)?;
                self.ie(idx, d + 1)?;
                self.push(None)
            }
        };
        self.ek.insert(e.clone(), c);
        Some(c)
    }

    fn ia(&mut self, a: &ArrayExpr, d: u32) -> Option<usize> {
        if d > MAX_DEPTH {
            return None;
        }
        if let Some(&c) = self.ak.get(a) {
            return Some(c);
        }
        let c = match a {
            ArrayExpr::AVar(_) => self.push(None),
            ArrayExpr::ConstArray(v) => {
                self.ie(v, d + 1)?;
                self.push(None)
            }
            ArrayExpr::Store(b, i, v) => {
                self.ia(b, d + 1)?;
                self.ie(i, d + 1)?;
                self.ie(v, d + 1)?;
                self.push(None)
            }
        };
        self.ak.insert(a.clone(), c);
        Some(c)
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

    fn unite(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        if self.rank[ra] < self.rank[rb] {
            self.parent[ra] = rb;
        } else if self.rank[ra] > self.rank[rb] {
            self.parent[rb] = ra;
        } else {
            self.parent[rb] = ra;
            self.rank[ra] += 1;
        }
    }
}

/// Destructure a select term.
fn sel_parts(s: &ElemExpr) -> Option<(&ArrayExpr, &ElemExpr)> {
    match s {
        ElemExpr::Select(a, j) => Some((a, j)),
        _ => None,
    }
}

/// Apply one fact under the kernel's own rules.
///
/// * `Some(true)` — preconditions held and the union is in place.
/// * `Some(false)` — a shape-valid fact whose preconditions do not hold yet
///   (retry in a later stratum).
/// * `None` — malformed term/shape (caller reports `Inconclusive`).
fn apply(k: &mut KernelAx, f: &AxFact) -> Option<bool> {
    match f {
        AxFact::SelectOfConstArray { select } => {
            let (arr, _) = sel_parts(select)?;
            let ArrayExpr::ConstArray(v) = arr else {
                return None;
            };
            let sc = k.ie(select, 0)?;
            let vc = k.ie(v, 0)?;
            if k.find(sc) != k.find(vc) {
                k.unite(sc, vc);
            }
            Some(true)
        }
        AxFact::SelectOfStoreIsIndex { select } => {
            let (arr, j) = sel_parts(select)?;
            let ArrayExpr::Store(_, i, v) = arr else {
                return None;
            };
            let sc = k.ie(select, 0)?;
            let ic = k.ie(i, 0)?;
            let jc = k.ie(j, 0)?;
            let vc = k.ie(v, 0)?;
            if k.find(ic) != k.find(jc) {
                return Some(false); // indices must already be equal
            }
            if k.find(sc) != k.find(vc) {
                k.unite(sc, vc);
            }
            Some(true)
        }
        AxFact::SelectOfStoreWalk { select, inner } => {
            let (arr, j) = sel_parts(select)?;
            let ArrayExpr::Store(a, i, _) = arr else {
                return None;
            };
            // The conclusion term must be literally `select(a, j)`.
            let expected = ElemExpr::Select(Box::new((**a).clone()), Box::new((*j).clone()));
            if inner != &expected {
                return None;
            }
            let sc = k.ie(select, 0)?;
            let ic = k.ie(i, 0)?;
            let jc = k.ie(j, 0)?;
            let ic2 = k.ie(inner, 0)?;
            if k.find(ic) == k.find(jc) {
                return Some(false); // indices must still be distinct
            }
            if k.find(sc) != k.find(ic2) {
                k.unite(sc, ic2);
            }
            Some(true)
        }
        AxFact::CongruentSelects { left, right } => {
            let ((al, jl), (ar, jr)) = (sel_parts(left)?, sel_parts(right)?);
            let lc = k.ie(left, 0)?;
            let rc = k.ie(right, 0)?;
            let alc = k.ia(al, 0)?;
            let jlc = k.ie(jl, 0)?;
            let arc = k.ia(ar, 0)?;
            let jrc = k.ie(jr, 0)?;
            if k.find(alc) != k.find(arc) || k.find(jlc) != k.find(jrc) {
                return Some(false); // preconditions not yet established
            }
            if k.find(lc) != k.find(rc) {
                k.unite(lc, rc);
            }
            Some(true)
        }
    }
}

/// Replay an UNSAT certificate against the original assertions.
///
/// [`Outcome::Accept`] iff the facts all validate locally and some element
/// class ends holding two distinct constants; [`Outcome::Reject`] when every
/// fact applies cleanly but no contradiction is reached (an engine bug
/// signal); [`Outcome::Inconclusive`] on malformed terms or shapes.
pub fn check_ax_unsat(
    assertions: &[ArrAssertion],
    cert: &tpt_solver_core::array::AxCertificate,
) -> Outcome {
    let mut k = KernelAx::new();
    for a in assertions {
        let ok = match a {
            ArrAssertion::ElemsEqual(l, r) => {
                let (Some(x), Some(y)) = (k.ie(l, 0), k.ie(r, 0)) else {
                    return Outcome::Inconclusive;
                };
                k.unite(x, y);
                true
            }
            ArrAssertion::ArraysEqual(l, r) => {
                let (Some(x), Some(y)) = (k.ia(l, 0), k.ia(r, 0)) else {
                    return Outcome::Inconclusive;
                };
                k.unite(x, y);
                true
            }
        };
        if !ok {
            return Outcome::Inconclusive;
        }
    }

    // Stratified application: retry facts whose preconditions were not yet
    // established until no further progress is possible.
    let mut consumed = vec![false; cert.facts.len()];
    loop {
        let mut progress = false;
        for (i, f) in cert.facts.iter().enumerate() {
            if consumed[i] {
                continue;
            }
            match apply(&mut k, f) {
                None => return Outcome::Inconclusive,
                Some(true) => {
                    consumed[i] = true;
                    progress = true;
                }
                Some(false) => {}
            }
        }
        if !progress {
            break;
        }
    }
    if consumed.iter().any(|&c| !c) {
        // A fact that never became applicable means the engine's derivation
        // does not replay — reject rather than accept.
        return Outcome::Reject;
    }

    // Clash: one class holding two distinct constants (constants are tracked
    // immutably per cell, so merges can never mask them).
    for c in 0..k.konst.len() {
        let Some(vc) = k.konst[c] else {
            continue;
        };
        for d in (c + 1)..k.konst.len() {
            let Some(vd) = k.konst[d] else {
                continue;
            };
            if vc != vd && k.find(c) == k.find(d) {
                return Outcome::Accept;
            }
        }
    }
    Outcome::Reject
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::panic)]
mod tests {
    use super::*;
    use tpt_solver_core::array::{solve_arrays, AxOutcome};

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
    fn model_check_roundtrip_sat() {
        let sel = ElemExpr::select(ArrayExpr::store(av(0), k(3), k(9)), k(3));
        let asserts = vec![ArrAssertion::ElemsEqual(sel, k(9))];
        match solve_arrays(1, 0, &asserts, 10_000) {
            Some(AxOutcome::Sat(m)) => {
                assert!(check_array_model(&asserts, &m, 1, 0).is_accept());
            }
            _ => panic!("expected Sat"),
        }
    }

    #[test]
    fn unsat_replay_roundtrip() {
        // select(store(a, i, 5), i) == 7 is UNSAT; kernel must accept the
        // engine's axiom-instance certificate.
        let sel = ElemExpr::select(ArrayExpr::store(av(0), ev(0), k(5)), ev(0));
        let asserts = vec![ArrAssertion::ElemsEqual(sel, k(7))];
        match solve_arrays(1, 1, &asserts, 10_000) {
            Some(AxOutcome::Unsat(cert)) => {
                assert!(check_ax_unsat(&asserts, &cert).is_accept());
            }
            _ => panic!("expected Unsat"),
        }
    }

    #[test]
    fn fabricated_fact_is_inconclusive() {
        // Assertions are trivially satisfiable, so no certificate can be
        // valid; a fabricated fact whose select does not even have a store as
        // its array argument has an invalid shape: Inconclusive (malformed),
        // never Accept.
        let asserts = vec![ArrAssertion::ElemsEqual(ev(0), k(1))];
        let bogus = ElemExpr::select(av(0), ev(0));
        let cert = tpt_solver_core::array::AxCertificate {
            facts: vec![AxFact::SelectOfStoreIsIndex { select: bogus }],
        };
        assert!(check_ax_unsat(&asserts, &cert).is_inconclusive());
    }

    #[test]
    fn well_shaped_but_false_certificate_is_rejected() {
        // A shape-valid SameIdx fact whose indices are NOT asserted equal can
        // never become applicable: Reject, not Accept.
        let sel = ElemExpr::select(ArrayExpr::store(av(0), ev(0), k(5)), ev(1));
        let asserts = vec![];
        let cert = tpt_solver_core::array::AxCertificate {
            facts: vec![
                AxFact::SelectOfStoreIsIndex { select: sel },
                AxFact::CongruentSelects {
                    left: ElemExpr::select(av(0), k(1)),
                    right: ElemExpr::select(av(0), k(2)),
                },
            ],
        };
        assert!(check_ax_unsat(&asserts, &cert).is_reject());
    }

    #[test]
    fn short_model_is_inconclusive() {
        let asserts = vec![ArrAssertion::ArraysEqual(av(0), av(1))];
        let model = ArrayModel {
            arrays: vec![tpt_solver_core::array::ConcreteArray::constant(0)],
            elems: Vec::new(),
        };
        assert!(check_array_model(&asserts, &model, 2, 0).is_inconclusive());
    }
}
