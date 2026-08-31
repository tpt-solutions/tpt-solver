//! E-graph equality-saturation preprocessing for the propositional (QF_SAT) formula
//! that [`Script::to_cnf`](crate::parsers::smtlib2::Script::to_cnf) Tseitin-encodes.
//!
//! This is untrusted preprocessing, exactly like the CDCL engine or Simplex: a bug
//! here can at worst make the pipeline solve a *different* (wrongly "simplified")
//! formula, which the trusted checker still validates against the checker's own
//! inputs — but to keep that risk as small as possible in the first place, every
//! rewrite is a semantics-preserving Boolean-algebra identity, and
//! [`simplify_boolean_preserves_truth_table`] property-tests that directly: for
//! random small formulas, the original and simplified terms are compared over
//! *every* assignment of their variables, not just re-solved and compared.
//!
//! Only the purely Boolean fragment is represented (the same fragment
//! [`to_cnf`](crate::parsers::smtlib2::Script::to_cnf) already restricts itself to):
//! `and`/`or`/`not`/`xor`/`iff`/`ite` over Boolean constants and variables.
//! Arithmetic terms are rejected with the same [`SmtError::Unsupported`] `to_cnf`
//! itself would raise on them — this pass runs *before* Tseitin encoding, not
//! instead of its checks.
//!
//! This module is a self-contained, dependency-free e-graph engine (a small union-
//! find e-graph with congruence closure and minimal-size extraction). It replaces
//! the external `egg` crate, which pulled in ~40 transitive crates and is no longer
//! maintained (its authors moved to `egglog`); for a fixed set of Boolean identities
//! a hand-rolled engine is smaller, auditable, and sufficient.

use crate::parsers::smtlib2::{Op, SmtError, Term};
use std::collections::{HashMap, HashSet};

type Id = usize;

/// A node in the e-graph. Children are e-class ids (`Id`), not nested nodes, so the
/// graph is a dag of equivalence classes rather than a tree.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum BoolLang {
    True,
    False,
    Not(Id),
    And(Id, Id),
    Or(Id, Id),
    Xor(Id, Id),
    Iff(Id, Id),
    Ite(Id, Id, Id),
    Sym(String),
}

impl BoolLang {
    fn children(&self) -> Vec<Id> {
        match self {
            BoolLang::True | BoolLang::False | BoolLang::Sym(_) => vec![],
            BoolLang::Not(a) => vec![*a],
            BoolLang::And(a, b)
            | BoolLang::Or(a, b)
            | BoolLang::Xor(a, b)
            | BoolLang::Iff(a, b) => vec![*a, *b],
            BoolLang::Ite(a, b, c) => vec![*a, *b, *c],
        }
    }

    fn with_children(&self, cs: &[Id]) -> BoolLang {
        match self {
            BoolLang::True => BoolLang::True,
            BoolLang::False => BoolLang::False,
            BoolLang::Sym(s) => BoolLang::Sym(s.clone()),
            BoolLang::Not(_) => BoolLang::Not(cs[0]),
            BoolLang::And(_, _) => BoolLang::And(cs[0], cs[1]),
            BoolLang::Or(_, _) => BoolLang::Or(cs[0], cs[1]),
            BoolLang::Xor(_, _) => BoolLang::Xor(cs[0], cs[1]),
            BoolLang::Iff(_, _) => BoolLang::Iff(cs[0], cs[1]),
            BoolLang::Ite(_, _, _) => BoolLang::Ite(cs[0], cs[1], cs[2]),
        }
    }
}

/// Bounds saturation the same way `Fuel` bounds every loop in the core: this is
/// preprocessing, not the trusted kernel, but it still must never run unbounded.
const NODE_LIMIT: usize = 10_000;
const ITER_LIMIT: usize = 20;

// ----------------------------------------------------------------------------
// Minimal union-find
// ----------------------------------------------------------------------------

struct UnionFind {
    parent: Vec<Id>,
}

impl UnionFind {
    fn new() -> Self {
        UnionFind { parent: Vec::new() }
    }

    fn make_set(&mut self) -> Id {
        let id = self.parent.len();
        self.parent.push(id);
        id
    }

    fn find(&self, mut id: Id) -> Id {
        while self.parent[id] != id {
            id = self.parent[id];
        }
        id
    }

    /// Union `a` and `b`, returning the new representative (the old `a`).
    fn union(&mut self, a: Id, b: Id) -> Id {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return a;
        }
        self.parent[b] = a;
        a
    }
}

// ----------------------------------------------------------------------------
// E-graph core
// ----------------------------------------------------------------------------

struct EGraph {
    uf: UnionFind,
    /// For each representative class id, the enodes it currently holds.
    nodes: HashMap<Id, Vec<BoolLang>>,
    /// Hash-consing: a canonical enode maps to the class id that owns it.
    memo: HashMap<BoolLang, Id>,
}

impl EGraph {
    fn new() -> Self {
        EGraph {
            uf: UnionFind::new(),
            nodes: HashMap::new(),
            memo: HashMap::new(),
        }
    }

    fn size(&self) -> usize {
        self.memo.len()
    }

    /// The currently-active representative class ids.
    fn reps(&self) -> Vec<Id> {
        self.nodes
            .keys()
            .cloned()
            .filter(|&k| self.uf.find(k) == k)
            .collect()
    }

    fn canon(&self, node: &BoolLang) -> Vec<Id> {
        node.children().iter().map(|c| self.uf.find(*c)).collect()
    }

    /// Insert an enode (children are canonicalized first), returning its class id.
    /// Hash-consing means structurally-equal enodes share a class immediately.
    fn add(&mut self, node: BoolLang) -> Id {
        let node = node.with_children(&self.canon(&node));
        if let Some(&id) = self.memo.get(&node) {
            return self.uf.find(id);
        }
        let id = self.uf.make_set();
        self.nodes.entry(id).or_default().push(node.clone());
        self.memo.insert(node, id);
        id
    }

    fn union(&mut self, a: Id, b: Id) -> Id {
        self.uf.union(a, b)
    }

    /// Congruence closure: repeatedly canonicalize every enode's children and merge
    /// any two classes that contain a structurally-equal (modulo equality) enode,
    /// until the graph stops changing. O(iterations · n²) but `n` is tiny here.
    fn rebuild(&mut self) {
        loop {
            let mut changed = false;

            // Gather every enode under its current representative, with children
            // re-canonicalized to the latest representatives.
            let mut by_class: Vec<(Id, BoolLang)> = Vec::new();
            let keys: Vec<Id> = self.nodes.keys().cloned().collect();
            for k in keys {
                let root = self.uf.find(k);
                let ns = self.nodes.get(&k).cloned().unwrap_or_default();
                for n in ns {
                    let canon = n.with_children(&self.canon(&n));
                    by_class.push((root, canon));
                }
            }

            // Two classes sharing a canonical enode are congruent: union them.
            let mut first: HashMap<BoolLang, Id> = HashMap::new();
            for (root, canon) in &by_class {
                let r = self.uf.find(*root);
                match first.get(canon) {
                    Some(&prev) => {
                        if self.uf.find(prev) != r {
                            self.uf.union(self.uf.find(prev), r);
                            changed = true;
                        }
                    }
                    None => {
                        first.insert(canon.clone(), r);
                    }
                }
            }

            // Rebuild the node/memo tables from the (now re-canonicalized) enodes,
            // deduplicating within each representative class.
            let mut new_nodes: HashMap<Id, Vec<BoolLang>> = HashMap::new();
            let mut new_memo: HashMap<BoolLang, Id> = HashMap::new();
            let mut seen: HashMap<Id, HashSet<BoolLang>> = HashMap::new();
            for (root, canon) in by_class {
                let r = self.uf.find(root);
                if seen.entry(r).or_default().insert(canon.clone()) {
                    new_nodes.entry(r).or_default().push(canon.clone());
                    new_memo.insert(canon, r);
                }
            }
            self.nodes = new_nodes;
            self.memo = new_memo;

            if !changed {
                break;
            }
        }
    }

    // -- pattern matching (modulo equality) ---------------------------------

    /// Find all substitutions that match `pat` against the given class.
    fn match_class(&self, pat: &Pat, class_id: Id) -> Vec<Subst> {
        let class_id = self.uf.find(class_id);
        let mut out = Vec::new();
        if let Some(ns) = self.nodes.get(&class_id) {
            for enode in ns {
                let mut subst = Subst::new();
                if self.match_enode(pat, enode, class_id, &mut subst) {
                    out.push(subst);
                }
            }
        }
        out
    }

    fn match_enode(&self, pat: &Pat, enode: &BoolLang, class_id: Id, subst: &mut Subst) -> bool {
        match (pat, enode) {
            (Pat::Var(v), _) => {
                if let Some(&existing) = subst.get(v) {
                    existing == class_id
                } else {
                    subst.insert(v.clone(), class_id);
                    true
                }
            }
            (Pat::True, BoolLang::True) => true,
            (Pat::False, BoolLang::False) => true,
            (Pat::Sym(s), BoolLang::Sym(t)) => s == t,
            (Pat::Not(p), BoolLang::Not(c)) => self.match_child(p, *c, subst),
            (Pat::And(p1, p2), BoolLang::And(c1, c2)) => self.match_two(p1, p2, *c1, *c2, subst),
            (Pat::Or(p1, p2), BoolLang::Or(c1, c2)) => self.match_two(p1, p2, *c1, *c2, subst),
            (Pat::Xor(p1, p2), BoolLang::Xor(c1, c2)) => self.match_two(p1, p2, *c1, *c2, subst),
            (Pat::Iff(p1, p2), BoolLang::Iff(c1, c2)) => self.match_two(p1, p2, *c1, *c2, subst),
            (Pat::Ite(p1, p2, p3), BoolLang::Ite(c1, c2, c3)) => {
                self.match_two(p1, p2, *c1, *c2, subst) && self.match_child(p3, *c3, subst)
            }
            _ => false,
        }
    }

    /// Match `pat` against a child class, requiring the resulting binding to be
    /// consistent with the current `subst`.
    fn match_child(&self, pat: &Pat, child: Id, subst: &mut Subst) -> bool {
        for mut cand in self.match_class(pat, child) {
            if self.consistent(subst, &cand) {
                for (k, v) in cand.drain() {
                    subst.insert(k, v);
                }
                return true;
            }
        }
        false
    }

    fn match_two(
        &self,
        p1: &Pat,
        p2: &Pat,
        c1: Id,
        c2: Id,
        subst: &mut Subst,
    ) -> bool {
        for mut cand1 in self.match_class(p1, c1) {
            if !self.consistent(subst, &cand1) {
                continue;
            }
            let mut merged = subst.clone();
            for (k, v) in cand1.drain() {
                merged.insert(k, v);
            }
            for mut cand2 in self.match_class(p2, c2) {
                if !self.consistent(&merged, &cand2) {
                    continue;
                }
                let mut final_sub = merged.clone();
                for (k, v) in cand2.drain() {
                    final_sub.insert(k, v);
                }
                *subst = final_sub;
                return true;
            }
        }
        false
    }

    fn consistent(&self, a: &Subst, b: &Subst) -> bool {
        for (k, v) in b {
            if let Some(&av) = a.get(k) {
                if av != *v {
                    return false;
                }
            }
        }
        true
    }

    // -- building RHS templates --------------------------------------------

    /// Build the term denoted by `pat` under `subst`, returning its class id. Stops
    /// (returns `None`) once `limit` distinct enodes have been created.
    fn build(&mut self, pat: &Pat, subst: &Subst, limit: usize, count: &mut usize) -> Option<Id> {
        if *count >= limit {
            return None;
        }
        let id = match pat {
            Pat::Var(v) => subst.get(v).copied()?,
            Pat::True => self.add(BoolLang::True),
            Pat::False => self.add(BoolLang::False),
            Pat::Sym(s) => self.add(BoolLang::Sym(s.clone())),
            Pat::Not(p) => {
                let c = self.build(p, subst, limit, count)?;
                self.add(BoolLang::Not(c))
            }
            Pat::And(p1, p2) => {
                let a = self.build(p1, subst, limit, count)?;
                let b = self.build(p2, subst, limit, count)?;
                self.add(BoolLang::And(a, b))
            }
            Pat::Or(p1, p2) => {
                let a = self.build(p1, subst, limit, count)?;
                let b = self.build(p2, subst, limit, count)?;
                self.add(BoolLang::Or(a, b))
            }
            Pat::Xor(p1, p2) => {
                let a = self.build(p1, subst, limit, count)?;
                let b = self.build(p2, subst, limit, count)?;
                self.add(BoolLang::Xor(a, b))
            }
            Pat::Iff(p1, p2) => {
                let a = self.build(p1, subst, limit, count)?;
                let b = self.build(p2, subst, limit, count)?;
                self.add(BoolLang::Iff(a, b))
            }
            Pat::Ite(p1, p2, p3) => {
                let a = self.build(p1, subst, limit, count)?;
                let b = self.build(p2, subst, limit, count)?;
                let c = self.build(p3, subst, limit, count)?;
                self.add(BoolLang::Ite(a, b, c))
            }
        };
        *count = self.size();
        Some(id)
    }
}

type Subst = HashMap<String, Id>;

// ----------------------------------------------------------------------------
// Rewrite-rule patterns (parsed from S-expressions)
// ----------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum Pat {
    Var(String),
    True,
    False,
    Sym(String),
    Not(Box<Pat>),
    And(Box<Pat>, Box<Pat>),
    Or(Box<Pat>, Box<Pat>),
    Xor(Box<Pat>, Box<Pat>),
    Iff(Box<Pat>, Box<Pat>),
    Ite(Box<Pat>, Box<Pat>, Box<Pat>),
}

struct Rule {
    lhs: Pat,
    rhs: Pat,
}

impl Rule {
    fn new(lhs: &str, rhs: &str) -> Self {
        Rule {
            lhs: parse_pat(lhs),
            rhs: parse_pat(rhs),
        }
    }
}

fn tokenize(s: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
                toks.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    toks
}

fn parse_pat(s: &str) -> Pat {
    let toks = tokenize(s);
    let (pat, rest) = parse_pat_tokens(&toks, 0);
    assert!(rest == toks.len(), "trailing tokens in pattern: {s}");
    pat
}

fn parse_pat_tokens(toks: &[String], i: usize) -> (Pat, usize) {
    if toks[i] == "(" {
        let op = toks[i + 1].clone();
        let mut j = i + 2;
        let mut args = Vec::new();
        while toks[j] != ")" {
            let (p, nj) = parse_pat_tokens(toks, j);
            args.push(p);
            j = nj;
        }
        (make_op(&op, args), j + 1)
    } else {
        let atom = &toks[i];
        let pat = if atom.starts_with('?') {
            Pat::Var(atom[1..].to_string())
        } else if atom == "true" {
            Pat::True
        } else if atom == "false" {
            Pat::False
        } else {
            Pat::Sym(atom.clone())
        };
        (pat, i + 1)
    }
}

fn make_op(op: &str, args: Vec<Pat>) -> Pat {
    match op {
        "not" => Pat::Not(Box::new(args[0].clone())),
        "and" => Pat::And(Box::new(args[0].clone()), Box::new(args[1].clone())),
        "or" => Pat::Or(Box::new(args[0].clone()), Box::new(args[1].clone())),
        "xor" => Pat::Xor(Box::new(args[0].clone()), Box::new(args[1].clone())),
        "iff" => Pat::Iff(Box::new(args[0].clone()), Box::new(args[1].clone())),
        "ite" => Pat::Ite(
            Box::new(args[0].clone()),
            Box::new(args[1].clone()),
            Box::new(args[2].clone()),
        ),
        other => panic!("unknown operator in rewrite rule: {other}"),
    }
}

fn rules() -> Vec<Rule> {
    vec![
        Rule::new("(and ?a ?b)", "(and ?b ?a)"),
        Rule::new("(and (and ?a ?b) ?c)", "(and ?a (and ?b ?c))"),
        Rule::new("(and ?a (and ?b ?c))", "(and (and ?a ?b) ?c)"),
        Rule::new("(or ?a ?b)", "(or ?b ?a)"),
        Rule::new("(or (or ?a ?b) ?c)", "(or ?a (or ?b ?c))"),
        Rule::new("(or ?a (or ?b ?c))", "(or (or ?a ?b) ?c)"),
        // Only the eliminating direction: the reverse (`?a => (not (not ?a))`)
        // matches every term and would blow up the e-graph without bound.
        Rule::new("(not (not ?a))", "?a"),
        Rule::new("(not true)", "false"),
        Rule::new("(not false)", "true"),
        Rule::new("(and ?a true)", "?a"),
        Rule::new("(and true ?a)", "?a"),
        Rule::new("(and ?a false)", "false"),
        Rule::new("(and false ?a)", "false"),
        Rule::new("(or ?a true)", "true"),
        Rule::new("(or true ?a)", "true"),
        Rule::new("(or ?a false)", "?a"),
        Rule::new("(or false ?a)", "?a"),
        Rule::new("(and ?a ?a)", "?a"),
        Rule::new("(or ?a ?a)", "?a"),
        Rule::new("(not (and ?a ?b))", "(or (not ?a) (not ?b))"),
        Rule::new("(or (not ?a) (not ?b))", "(not (and ?a ?b))"),
        Rule::new("(not (or ?a ?b))", "(and (not ?a) (not ?b))"),
        Rule::new("(and (not ?a) (not ?b))", "(not (or ?a ?b))"),
        Rule::new("(and ?a (not ?a))", "false"),
        Rule::new("(and (not ?a) ?a)", "false"),
        Rule::new("(or ?a (not ?a))", "true"),
        Rule::new("(or (not ?a) ?a)", "true"),
        Rule::new("(and ?a (or ?a ?b))", "?a"),
        Rule::new("(or ?a (and ?a ?b))", "?a"),
        Rule::new("(xor ?a false)", "?a"),
        Rule::new("(xor ?a true)", "(not ?a)"),
        Rule::new("(xor ?a ?a)", "false"),
        Rule::new("(xor ?a ?b)", "(xor ?b ?a)"),
        Rule::new("(iff ?a true)", "?a"),
        Rule::new("(iff ?a false)", "(not ?a)"),
        Rule::new("(iff ?a ?a)", "true"),
        Rule::new("(iff ?a ?b)", "(iff ?b ?a)"),
        Rule::new("(not (xor ?a ?b))", "(iff ?a ?b)"),
        Rule::new("(not (iff ?a ?b))", "(xor ?a ?b)"),
        Rule::new("(ite true ?a ?b)", "?a"),
        Rule::new("(ite false ?a ?b)", "?b"),
        Rule::new("(ite ?c ?a ?a)", "?a"),
        Rule::new("(ite ?c true ?b)", "(or ?c ?b)"),
        Rule::new("(ite ?c false ?b)", "(and (not ?c) ?b)"),
        Rule::new("(ite ?c true false)", "?c"),
    ]
}

// ----------------------------------------------------------------------------
// Term <-> e-graph translation
// ----------------------------------------------------------------------------

fn add_term(eg: &mut EGraph, term: &Term) -> Result<Id, SmtError> {
    match term {
        Term::Bool(true) => Ok(eg.add(BoolLang::True)),
        Term::Bool(false) => Ok(eg.add(BoolLang::False)),
        Term::Sym(name) => Ok(eg.add(BoolLang::Sym(name.clone()))),
        Term::Num(_) => Err(SmtError::Unsupported(
            "numeric constant in boolean position".into(),
        )),
        // Non-propositional theories (QF_BV / QF_AX terms) are out of the
        // e-graph's Boolean fragment; they fail the same way the Tseitin
        // encoder would, after simplification.
        Term::BvLit(_, _)
        | Term::Extract(_, _)
        | Term::ConstArray(_)
        | Term::App(
            Op::BvNot
            | Op::BvNeg
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::BvAdd
            | Op::BvSub
            | Op::BvShl
            | Op::BvLShr
            | Op::BvUlt
            | Op::Concat
            | Op::Select
            | Op::Store,
            _,
        ) => Err(SmtError::Unsupported(
            "non-Boolean theory term in a propositional formula".into(),
        )),
        Term::App(Op::Not, args) => {
            if args.len() != 1 {
                return Err(SmtError::BadArity("not expects 1 argument".into()));
            }
            let a = add_term(eg, &args[0])?;
            Ok(eg.add(BoolLang::Not(a)))
        }
        Term::App(Op::And, args) => {
            fold_binary(eg, args, BoolLang::True, |a, b| BoolLang::And(a, b))
        }
        Term::App(Op::Or, args) => {
            fold_binary(eg, args, BoolLang::False, |a, b| BoolLang::Or(a, b))
        }
        Term::App(Op::Imp, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("=> expects 2 arguments".into()));
            }
            let a = add_term(eg, &args[0])?;
            let b = add_term(eg, &args[1])?;
            let not_a = eg.add(BoolLang::Not(a));
            Ok(eg.add(BoolLang::Or(not_a, b)))
        }
        Term::App(Op::Xor, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("xor expects 2 arguments".into()));
            }
            let a = add_term(eg, &args[0])?;
            let b = add_term(eg, &args[1])?;
            Ok(eg.add(BoolLang::Xor(a, b)))
        }
        Term::App(Op::Eq, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("= expects 2 arguments".into()));
            }
            let a = add_term(eg, &args[0])?;
            let b = add_term(eg, &args[1])?;
            Ok(eg.add(BoolLang::Iff(a, b)))
        }
        Term::App(Op::Distinct, args) => {
            if args.len() != 2 {
                return Err(SmtError::Unsupported(
                    "distinct is only supported on 2 boolean terms".into(),
                ));
            }
            let a = add_term(eg, &args[0])?;
            let b = add_term(eg, &args[1])?;
            Ok(eg.add(BoolLang::Xor(a, b)))
        }
        Term::App(Op::Ite, args) => {
            if args.len() != 3 {
                return Err(SmtError::BadArity("ite expects 3 arguments".into()));
            }
            let c = add_term(eg, &args[0])?;
            let a = add_term(eg, &args[1])?;
            let b = add_term(eg, &args[2])?;
            Ok(eg.add(BoolLang::Ite(c, a, b)))
        }
        Term::App(Op::Le, _)
        | Term::App(Op::Lt, _)
        | Term::App(Op::Ge, _)
        | Term::App(Op::Gt, _) => Err(SmtError::Unsupported(
            "arithmetic comparison in a boolean formula; use the LRA path".into(),
        )),
        Term::App(Op::Other, _)
        | Term::App(Op::Add, _)
        | Term::App(Op::Sub, _)
        | Term::App(Op::Mul, _)
        | Term::App(Op::Div, _) => Err(SmtError::Unsupported(
            "non-boolean term in a boolean formula".into(),
        )),
    }
}

/// Fold a variadic `and`/`or` (empty allowed, per SMT-LIB2) into a right-associated
/// binary chain, translating each child first.
fn fold_binary<F>(eg: &mut EGraph, args: &[Term], empty: BoolLang, node: F) -> Result<Id, SmtError>
where
    F: Fn(Id, Id) -> BoolLang,
{
    if args.is_empty() {
        return Ok(eg.add(empty));
    }
    let mut ids = Vec::with_capacity(args.len());
    for a in args {
        ids.push(add_term(eg, a)?);
    }
    let mut acc = ids[ids.len() - 1];
    for &id in ids[..ids.len() - 1].iter().rev() {
        acc = eg.add(node(id, acc));
    }
    Ok(acc)
}

/// Choose, for each class, the smallest (by node count) enode — the analogue of
/// egg's `AstSize` cost. Self-referential enodes are skipped so extraction stays
/// acyclic.
fn extract(eg: &EGraph) -> HashMap<Id, BoolLang> {
    let mut cost: HashMap<Id, usize> = HashMap::new();
    let mut best: HashMap<Id, BoolLang> = HashMap::new();
    let mut changed = true;
    while changed {
        changed = false;
        for cid in eg.reps() {
            if let Some(ns) = eg.nodes.get(&cid).cloned() {
                for enode in ns {
                    let mut c = 1usize;
                    let mut ok = true;
                    for child in enode.children() {
                        let fc = eg.uf.find(child);
                        if fc == cid {
                            ok = false;
                            break;
                        }
                        match cost.get(&fc) {
                            Some(&cc) => c = c.saturating_add(cc),
                            None => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if ok && cost.get(&cid).copied().unwrap_or(usize::MAX) > c {
                        cost.insert(cid, c);
                        best.insert(cid, enode.clone());
                        changed = true;
                    }
                }
            }
        }
    }
    // Defensive: ensure every representative has *some* enode (only reachable if a
    // class consisted solely of cyclic enodes, which these rules cannot produce).
    for cid in eg.reps() {
        if !best.contains_key(&cid) {
            if let Some(ns) = eg.nodes.get(&cid) {
                if let Some(n) = ns.first() {
                    best.insert(cid, n.clone());
                }
            }
        }
    }
    best
}

fn node_to_term(eg: &EGraph, best: &HashMap<Id, BoolLang>, class_id: Id) -> Term {
    let class_id = eg.uf.find(class_id);
    match &best[&class_id] {
        BoolLang::True => Term::Bool(true),
        BoolLang::False => Term::Bool(false),
        BoolLang::Sym(s) => Term::Sym(s.clone()),
        BoolLang::Not(c) => Term::App(Op::Not, vec![node_to_term(eg, best, *c)]),
        BoolLang::And(a, b) => Term::App(
            Op::And,
            vec![node_to_term(eg, best, *a), node_to_term(eg, best, *b)],
        ),
        BoolLang::Or(a, b) => Term::App(
            Op::Or,
            vec![node_to_term(eg, best, *a), node_to_term(eg, best, *b)],
        ),
        BoolLang::Xor(a, b) => Term::App(
            Op::Xor,
            vec![node_to_term(eg, best, *a), node_to_term(eg, best, *b)],
        ),
        BoolLang::Iff(a, b) => Term::App(
            Op::Eq,
            vec![node_to_term(eg, best, *a), node_to_term(eg, best, *b)],
        ),
        BoolLang::Ite(a, b, c) => Term::App(
            Op::Ite,
            vec![
                node_to_term(eg, best, *a),
                node_to_term(eg, best, *b),
                node_to_term(eg, best, *c),
            ],
        ),
    }
}

/// Simplify a purely-Boolean [`Term`] via e-graph equality saturation, returning an
/// equivalent (usually smaller) term. `Err` only when `term` uses a construct
/// outside the Boolean fragment (matching the errors `to_cnf`'s Tseitin encoder
/// itself would raise) or has a malformed arity.
pub(crate) fn simplify_boolean(term: &Term) -> Result<Term, SmtError> {
    let mut eg = EGraph::new();
    let root = add_term(&mut eg, term)?;

    let rules = rules();
    let mut count = eg.size();
    for _ in 0..ITER_LIMIT {
        let mut applied = false;
        let roots = eg.reps();
        for rule in &rules {
            for cid in &roots {
                let cid = eg.uf.find(*cid);
                let matches = eg.match_class(&rule.lhs, cid);
                for subst in matches {
                    if let Some(new_id) = eg.build(&rule.rhs, &subst, NODE_LIMIT, &mut count) {
                        let (a, b) = (eg.uf.find(cid), eg.uf.find(new_id));
                        if a != b {
                            eg.union(a, b);
                            applied = true;
                        }
                    }
                }
            }
        }
        eg.rebuild();
        if !applied || count >= NODE_LIMIT {
            break;
        }
    }

    let best = extract(&eg);
    Ok(node_to_term(&eg, &best, eg.uf.find(root)))
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// A tiny recursive Boolean-formula generator over 3 variables, for the
    /// truth-table equivalence property test below.
    fn arb_term() -> impl Strategy<Value = Term> {
        let leaf = prop_oneof![
            Just(Term::Bool(true)),
            Just(Term::Bool(false)),
            (0..3usize).prop_map(|i| Term::Sym(format!("v{i}"))),
        ];
        leaf.prop_recursive(4, 64, 4, |inner| {
            prop_oneof![
                inner.clone().prop_map(|a| Term::App(Op::Not, vec![a])),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| Term::App(Op::And, vec![a, b])),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| Term::App(Op::Or, vec![a, b])),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| Term::App(Op::Xor, vec![a, b])),
                (inner.clone(), inner.clone()).prop_map(|(a, b)| Term::App(Op::Eq, vec![a, b])),
                (inner.clone(), inner.clone(), inner)
                    .prop_map(|(c, a, b)| Term::App(Op::Ite, vec![c, a, b])),
            ]
        })
    }

    /// Evaluate a purely-Boolean term under an assignment `v0, v1, v2`.
    fn eval(term: &Term, assign: [bool; 3]) -> bool {
        match term {
            Term::Bool(b) => *b,
            Term::Sym(name) => {
                let i: usize = name.trim_start_matches('v').parse().unwrap();
                assign[i]
            }
            Term::Num(_) => panic!("non-boolean leaf in a boolean-only test generator"),
            Term::App(Op::Not, a) => !eval(&a[0], assign),
            Term::App(Op::And, a) => eval(&a[0], assign) && eval(&a[1], assign),
            Term::App(Op::Or, a) => eval(&a[0], assign) || eval(&a[1], assign),
            Term::App(Op::Xor, a) => eval(&a[0], assign) ^ eval(&a[1], assign),
            Term::App(Op::Eq, a) => eval(&a[0], assign) == eval(&a[1], assign),
            Term::App(Op::Ite, a) => {
                if eval(&a[0], assign) {
                    eval(&a[1], assign)
                } else {
                    eval(&a[2], assign)
                }
            }
            _ => panic!("term outside the generator's boolean fragment"),
        }
    }

    proptest! {
        /// The e-graph pass must never change what a formula means: for every
        /// assignment of its (at most 3) variables, the original and the
        /// simplified term must evaluate to the same truth value. This is a
        /// direct semantic check, not an indirect "the solver still agrees" one —
        /// exactly the kind of differential/property testing the suite treats as
        /// first-class (spec §5.4).
        #[test]
        fn simplify_boolean_preserves_truth_table(t in arb_term()) {
            let simplified = simplify_boolean(&t).unwrap();
            for a0 in [false, true] {
                for a1 in [false, true] {
                    for a2 in [false, true] {
                        let assign = [a0, a1, a2];
                        prop_assert_eq!(
                            eval(&t, assign),
                            eval(&simplified, assign),
                            "mismatch under {:?} for {:?} -> {:?}",
                            assign,
                            t,
                            simplified
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn eliminates_double_negation() {
        let t = Term::App(
            Op::Not,
            vec![Term::App(Op::Not, vec![Term::Sym("v0".into())])],
        );
        let s = simplify_boolean(&t).unwrap();
        assert!(matches!(s, Term::Sym(n) if n == "v0"));
    }

    #[test]
    fn folds_and_with_false_to_false() {
        let t = Term::App(
            Op::And,
            vec![Term::Sym("v0".into()), Term::Bool(false)],
        );
        let s = simplify_boolean(&t).unwrap();
        assert!(matches!(s, Term::Bool(false)));
    }

    #[test]
    fn rejects_arithmetic_terms() {
        let t = Term::App(
            Op::Le,
            vec![
                Term::Sym("v0".into()),
                Term::Num(tpt_solver_core::rational::Rational::zero()),
            ],
        );
        assert!(matches!(
            simplify_boolean(&t),
            Err(SmtError::Unsupported(_))
        ));
    }
}
