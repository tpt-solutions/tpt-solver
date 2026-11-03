# Trust model

The solver engines are large and optimized, so they are treated as untrusted. The
kernel in `tpt-solver-check` is kept small and has no dependencies. It is the only
code whose verdicts the design relies on.

For each theory the kernel checks the following.

| Theory | SAT witness | UNSAT witness |
|--------|-------------|---------------|
| CNF | model substituted into every clause | RUP derivation of each learned clause, ending in the empty clause |
| LRA (SMT-LIB2, MPS) | model re-evaluated against each linear constraint | Farkas multipliers that combine to `0 <= negative` |
| BV | word model evaluated against the assertions | RUP proof over the bit-blasted CNF |
| QF_AX | concrete array model re-checked | congruence-closure certificate |

The kernel never assumes that the engine's bookkeeping is right. If a witness fails
to check, the answer is not reported as trusted.

## Fail-closed policy

For CNF input the pipeline runs in tiers. If the CDCL answer is not `Accept`, the
reference DPLL solver is tried and certified in turn. If that also fails, the result
is `Unknown` and a rejection record is kept. A rejected answer is never returned as
trusted.

## What is not yet covered

- The bit-blasting encoder for BV is not re-derived by the kernel. Differential
  property tests against brute-force enumeration cover it.
- The DRAT output has not yet been cross-checked against `drat-trim`. The format is
  designed to match, but that check has not been run.
- `--explain` for CNF is a deletion core. It is irreducible but not guaranteed to be
  minimum.
