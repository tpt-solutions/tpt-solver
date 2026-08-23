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

use crate::parsers::smtlib2::{Op, SmtError, Term};
use egg::{define_language, rewrite, AstSize, Extractor, Id, RecExpr, Rewrite, Runner};

define_language! {
    enum BoolLang {
        "true" = True([Id; 0]),
        "false" = False([Id; 0]),
        "not" = Not([Id; 1]),
        "and" = And([Id; 2]),
        "or" = Or([Id; 2]),
        "xor" = Xor([Id; 2]),
        "iff" = Iff([Id; 2]),
        "ite" = Ite([Id; 3]),
        Symbol(egg::Symbol),
    }
}

/// Bounds saturation the same way `Fuel` bounds every loop in the core: this is
/// preprocessing, not the trusted kernel, but it still must never run unbounded.
const NODE_LIMIT: usize = 10_000;
const ITER_LIMIT: usize = 20;

fn rules() -> Vec<Rewrite<BoolLang, ()>> {
    vec![
        rewrite!("and-comm"; "(and ?a ?b)" => "(and ?b ?a)"),
        rewrite!("and-assoc"; "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))"),
        rewrite!("and-assoc-rev"; "(and ?a (and ?b ?c))" => "(and (and ?a ?b) ?c)"),
        rewrite!("or-comm"; "(or ?a ?b)" => "(or ?b ?a)"),
        rewrite!("or-assoc"; "(or (or ?a ?b) ?c)" => "(or ?a (or ?b ?c))"),
        rewrite!("or-assoc-rev"; "(or ?a (or ?b ?c))" => "(or (or ?a ?b) ?c)"),
        // Only the eliminating direction: the reverse (`?a => (not (not ?a))`)
        // matches every term and would blow up the e-graph without bound.
        rewrite!("double-neg"; "(not (not ?a))" => "?a"),
        rewrite!("not-true"; "(not true)" => "false"),
        rewrite!("not-false"; "(not false)" => "true"),
        rewrite!("and-true-l"; "(and ?a true)" => "?a"),
        rewrite!("and-true-r"; "(and true ?a)" => "?a"),
        rewrite!("and-false-l"; "(and ?a false)" => "false"),
        rewrite!("and-false-r"; "(and false ?a)" => "false"),
        rewrite!("or-true-l"; "(or ?a true)" => "true"),
        rewrite!("or-true-r"; "(or true ?a)" => "true"),
        rewrite!("or-false-l"; "(or ?a false)" => "?a"),
        rewrite!("or-false-r"; "(or false ?a)" => "?a"),
        rewrite!("and-idem"; "(and ?a ?a)" => "?a"),
        rewrite!("or-idem"; "(or ?a ?a)" => "?a"),
        rewrite!("demorgan-and"; "(not (and ?a ?b))" => "(or (not ?a) (not ?b))"),
        rewrite!("demorgan-and-rev"; "(or (not ?a) (not ?b))" => "(not (and ?a ?b))"),
        rewrite!("demorgan-or"; "(not (or ?a ?b))" => "(and (not ?a) (not ?b))"),
        rewrite!("demorgan-or-rev"; "(and (not ?a) (not ?b))" => "(not (or ?a ?b))"),
        rewrite!("contradiction-l"; "(and ?a (not ?a))" => "false"),
        rewrite!("contradiction-r"; "(and (not ?a) ?a)" => "false"),
        rewrite!("excluded-middle-l"; "(or ?a (not ?a))" => "true"),
        rewrite!("excluded-middle-r"; "(or (not ?a) ?a)" => "true"),
        rewrite!("absorb-and"; "(and ?a (or ?a ?b))" => "?a"),
        rewrite!("absorb-or"; "(or ?a (and ?a ?b))" => "?a"),
        rewrite!("xor-false"; "(xor ?a false)" => "?a"),
        rewrite!("xor-true"; "(xor ?a true)" => "(not ?a)"),
        rewrite!("xor-self"; "(xor ?a ?a)" => "false"),
        rewrite!("xor-comm"; "(xor ?a ?b)" => "(xor ?b ?a)"),
        rewrite!("iff-true"; "(iff ?a true)" => "?a"),
        rewrite!("iff-false"; "(iff ?a false)" => "(not ?a)"),
        rewrite!("iff-self"; "(iff ?a ?a)" => "true"),
        rewrite!("iff-comm"; "(iff ?a ?b)" => "(iff ?b ?a)"),
        rewrite!("not-xor-is-iff"; "(not (xor ?a ?b))" => "(iff ?a ?b)"),
        rewrite!("not-iff-is-xor"; "(not (iff ?a ?b))" => "(xor ?a ?b)"),
        rewrite!("ite-true-cond"; "(ite true ?a ?b)" => "?a"),
        rewrite!("ite-false-cond"; "(ite false ?a ?b)" => "?b"),
        rewrite!("ite-same-branch"; "(ite ?c ?a ?a)" => "?a"),
        rewrite!("ite-then-true"; "(ite ?c true ?b)" => "(or ?c ?b)"),
        rewrite!("ite-then-false"; "(ite ?c false ?b)" => "(and (not ?c) ?b)"),
        rewrite!("ite-bool"; "(ite ?c true false)" => "?c"),
    ]
}

/// Fold a variadic `and`/`or` (empty allowed, per SMT-LIB2) into a right-associated
/// binary chain in `expr`, translating each child with `leaf`.
fn fold_binary(
    args: &[Term],
    expr: &mut RecExpr<BoolLang>,
    empty: BoolLang,
    node: fn([Id; 2]) -> BoolLang,
) -> Result<Id, SmtError> {
    if args.is_empty() {
        return Ok(expr.add(empty));
    }
    let mut ids = Vec::with_capacity(args.len());
    for a in args {
        ids.push(term_to_expr(a, expr)?);
    }
    let mut acc = ids[ids.len() - 1];
    for &id in ids[..ids.len() - 1].iter().rev() {
        acc = expr.add(node([id, acc]));
    }
    Ok(acc)
}

fn term_to_expr(term: &Term, expr: &mut RecExpr<BoolLang>) -> Result<Id, SmtError> {
    match term {
        Term::Bool(true) => Ok(expr.add(BoolLang::True([]))),
        Term::Bool(false) => Ok(expr.add(BoolLang::False([]))),
        Term::Sym(name) => Ok(expr.add(BoolLang::Symbol(egg::Symbol::from(name.as_str())))),
        Term::Num(_) => Err(SmtError::Unsupported(
            "numeric constant in boolean position".into(),
        )),
        Term::App(Op::Not, args) => {
            if args.len() != 1 {
                return Err(SmtError::BadArity("not expects 1 argument".into()));
            }
            let a = term_to_expr(&args[0], expr)?;
            Ok(expr.add(BoolLang::Not([a])))
        }
        Term::App(Op::And, args) => fold_binary(args, expr, BoolLang::True([]), BoolLang::And),
        Term::App(Op::Or, args) => fold_binary(args, expr, BoolLang::False([]), BoolLang::Or),
        Term::App(Op::Imp, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("=> expects 2 arguments".into()));
            }
            let a = term_to_expr(&args[0], expr)?;
            let b = term_to_expr(&args[1], expr)?;
            let not_a = expr.add(BoolLang::Not([a]));
            Ok(expr.add(BoolLang::Or([not_a, b])))
        }
        Term::App(Op::Xor, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("xor expects 2 arguments".into()));
            }
            let a = term_to_expr(&args[0], expr)?;
            let b = term_to_expr(&args[1], expr)?;
            Ok(expr.add(BoolLang::Xor([a, b])))
        }
        Term::App(Op::Eq, args) => {
            if args.len() != 2 {
                return Err(SmtError::BadArity("= expects 2 arguments".into()));
            }
            let a = term_to_expr(&args[0], expr)?;
            let b = term_to_expr(&args[1], expr)?;
            Ok(expr.add(BoolLang::Iff([a, b])))
        }
        Term::App(Op::Distinct, args) => {
            if args.len() != 2 {
                return Err(SmtError::Unsupported(
                    "distinct is only supported on 2 boolean terms".into(),
                ));
            }
            let a = term_to_expr(&args[0], expr)?;
            let b = term_to_expr(&args[1], expr)?;
            Ok(expr.add(BoolLang::Xor([a, b])))
        }
        Term::App(Op::Ite, args) => {
            if args.len() != 3 {
                return Err(SmtError::BadArity("ite expects 3 arguments".into()));
            }
            let c = term_to_expr(&args[0], expr)?;
            let a = term_to_expr(&args[1], expr)?;
            let b = term_to_expr(&args[2], expr)?;
            Ok(expr.add(BoolLang::Ite([c, a, b])))
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

fn node_to_term(expr: &RecExpr<BoolLang>, id: Id) -> Term {
    match &expr[id] {
        BoolLang::True(_) => Term::Bool(true),
        BoolLang::False(_) => Term::Bool(false),
        BoolLang::Symbol(s) => Term::Sym(s.to_string()),
        BoolLang::Not([a]) => Term::App(Op::Not, vec![node_to_term(expr, *a)]),
        BoolLang::And([a, b]) => Term::App(
            Op::And,
            vec![node_to_term(expr, *a), node_to_term(expr, *b)],
        ),
        BoolLang::Or([a, b]) => {
            Term::App(Op::Or, vec![node_to_term(expr, *a), node_to_term(expr, *b)])
        }
        BoolLang::Xor([a, b]) => Term::App(
            Op::Xor,
            vec![node_to_term(expr, *a), node_to_term(expr, *b)],
        ),
        BoolLang::Iff([a, b]) => {
            Term::App(Op::Eq, vec![node_to_term(expr, *a), node_to_term(expr, *b)])
        }
        BoolLang::Ite([c, a, b]) => Term::App(
            Op::Ite,
            vec![
                node_to_term(expr, *c),
                node_to_term(expr, *a),
                node_to_term(expr, *b),
            ],
        ),
    }
}

/// Simplify a purely-Boolean [`Term`] via e-graph equality saturation, returning an
/// equivalent (usually smaller) term. `Err` only when `term` uses a construct
/// outside the Boolean fragment (matching the errors `to_cnf`'s Tseitin encoder
/// itself would raise) or has a malformed arity.
pub(crate) fn simplify_boolean(term: &Term) -> Result<Term, SmtError> {
    let mut expr = RecExpr::default();
    term_to_expr(term, &mut expr)?;

    let runner = Runner::<BoolLang, ()>::default()
        .with_node_limit(NODE_LIMIT)
        .with_iter_limit(ITER_LIMIT)
        .with_expr(&expr)
        .run(&rules());
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(root);
    Ok(node_to_term(&best, Id::from(best.as_ref().len() - 1)))
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
        let t = Term::App(Op::And, vec![Term::Sym("v0".into()), Term::Bool(false)]);
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
