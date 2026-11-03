# tpt-solver

tpt-solver is a SAT and SMT solver suite in pure Rust. Its answers are checked
before you see them. The search engine is fast and untrusted. A small checker kernel
independently revalidates every answer:

- **SAT** comes with a model, and the kernel re-evaluates the input against it.
- **UNSAT** comes with a proof (a DRAT-style clause list for CNF and bit-vectors, or
  Farkas multipliers for linear arithmetic), and the kernel re-derives it.

A verdict of `Accept` means the kernel confirmed the answer. `Reject` means it
refuted the answer. `Inconclusive` means it could not decide either way. Only
`Accept` should be trusted.

The workspace has three crates:

| Crate | Role | Trust |
|-------|------|-------|
| `tpt-solver-core` | Search engine: CDCL, Simplex, bit-blasting, congruence closure | Untrusted |
| `tpt-solver-check` | Certificate checker kernel | Trusted |
| `tpt-solver` | Parsers, CLI, the library API, and the e-graph preprocessor | Periphery |

Start with [the trust model](trust-model.md), or jump to [the command line](cli.md).

To try the solver without installing anything, open the
[browser playground](playground/index.html). It runs the same certified pipeline as
the command line, compiled to WebAssembly.
