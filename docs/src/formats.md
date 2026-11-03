# Input formats and theories

## DIMACS CNF

Standard `p cnf` input. Clauses end in `0`, and a missing final `0` is tolerated.
The variable count may be larger than the header declares. Inputs above the
per-variable, per-clause, or per-clause-length caps are rejected.

## SMT-LIB2

The parser accepts these theories. The engine is chosen from the content, in this
order: linear arithmetic, then bit-vectors, then arrays, then propositional.

| Theory | Supported |
|--------|-----------|
| QF_LRA | Linear real arithmetic. `+ - *`, where `*` and `/` take a constant operand. Integers are treated as reals. Strict `<` and `>` are treated as non-strict, which is a known limitation. |
| QF_BV | Fixed-width vectors of up to 64 bits. Bitwise and arithmetic operators, constant shifts, `concat`, and `extract`. |
| QF_AX | Ground equalities and disequalities over arrays and elements. Arrays range over an unbounded index universe, so two arrays are distinct when they differ at some index. The answer is decided when the congruence closure or the model settles the question, and is `unknown` otherwise. |
| QF_SAT | Propositional connectives, lowered to CNF by Tseitin encoding. |

Commands are handled as follows. `set-logic`, `set-option`, `declare-fun`,
`declare-const`, `assert`, `check-sat`, `get-model`, and `exit` are supported.
`push`, `pop`, `reset`, `define-fun`, `define-sort`, `declare-sort`,
`check-sat-assuming`, and `get-value` are rejected with an error rather than ignored.

## LP-MPS

Free-format MPS with `ROWS`, `COLUMNS`, `RHS`, `RANGES`, `BOUNDS`, and `ENDATA`.
The problem is lowered to the same linear constraint system as SMT-LIB2 LRA. The
objective is dropped, so this is a feasibility engine and not an optimizer.
