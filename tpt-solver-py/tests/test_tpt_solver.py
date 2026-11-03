"""Smoke tests for the tpt-solver Python bindings."""

import pytest

import tpt_solver

UNSAT = [[1, 2], [-1, 3], [-2, 3], [-3]]


def test_unsat_cnf_is_certified_with_proof_and_core():
    r = tpt_solver.solve_cnf(UNSAT, proof=True, explain=True)
    assert r["result"] == "unsat"
    assert r["checker"] == "accept"
    assert r["proof"][-1] == [], "the proof ends in the empty clause"
    assert r["core"] == [0, 1, 2, 3]


def test_sat_cnf_returns_checked_model():
    r = tpt_solver.solve_cnf([[1], [-2]])
    assert r["result"] == "sat"
    assert r["checker"] == "accept"
    assert r["model"] == [1, -2]


def test_solve_detects_dimacs_from_content():
    r = tpt_solver.solve("c comment\np cnf 2 2\n1 0\n-2 0\n")
    assert r["result"] == "sat"
    assert r["theory"] == "CNF"


def test_solve_smtlib_lra_returns_named_model():
    text = "(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 1))(check-sat)"
    r = tpt_solver.solve(text, format="smt2")
    assert r["result"] == "sat"
    assert r["checker"] == "accept"
    assert "x" in r["model"]


def test_bitvector_contradiction_is_unsat():
    text = (
        "(set-logic QF_BV)(declare-fun a () (_ BitVec 4))"
        "(assert (= a #x3))(assert (= a #x7))"
    )
    r = tpt_solver.solve(text)
    assert r["theory"] == "BV"
    assert r["result"] == "unsat"
    assert r["checker"] == "accept"


def test_check_rejects_a_bogus_proof():
    problem = "p cnf 2 2\n1 0\n-2 0\n"
    assert tpt_solver.check(problem, "0\n") == "reject"


def test_check_accepts_a_genuine_proof():
    r = tpt_solver.solve_cnf(UNSAT, proof=True)
    lines = "".join(" ".join(map(str, c)) + " 0\n" for c in r["proof"])
    dimacs = "p cnf 3 4\n1 2 0\n-1 3 0\n-2 3 0\n-3 0\n"
    assert tpt_solver.check(dimacs, lines) == "accept"


def test_zero_literal_is_rejected():
    with pytest.raises(ValueError):
        tpt_solver.solve_cnf([[1, 0]])


def test_malformed_input_raises_value_error():
    with pytest.raises(ValueError):
        tpt_solver.solve("hello world", format="auto")


def test_unknown_format_name_raises():
    with pytest.raises(ValueError):
        tpt_solver.solve("p cnf 1 0", format="nope")
