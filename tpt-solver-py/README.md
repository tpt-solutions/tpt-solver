# tpt-solver for Python

Python bindings for tpt-solver. Each answer comes back with the verdict of an
independent checker kernel, so you can tell whether the solver's answer was verified.

```python
import tpt_solver

r = tpt_solver.solve_cnf([[1, 2], [-1, 3], [-2, 3], [-3]], proof=True, explain=True)
assert r["result"] == "unsat" and r["checker"] == "accept"
print(r["proof"])   # DRAT-style clauses, ending in []
print(r["core"])    # indices of the clauses needed for the contradiction

r = tpt_solver.solve("(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 1))")
print(r["result"], r["model"])
```

## Functions

- `solve(text, format="auto", fuel=10_000_000, proof=False, explain=False)`
- `solve_cnf(clauses, num_vars=None, fuel=10_000_000, proof=False, explain=False)`
- `check(problem, proof, format="auto") -> "accept" | "reject" | "inconclusive"`

Malformed input raises `ValueError`. The `checker` key is the verdict. Trust a
result only when it is `"accept"`.

## Building

```sh
pip install maturin
maturin develop --release   # installs into the active virtualenv
python -m pytest tests
```
