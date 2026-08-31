# Changelog

All notable changes to the `tpt-solver` crate are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] — 2026-08-31

Initial public workspace release of the three-crate `tpt-solver` suite.

### Added

- **DIMACS parser** (`parsers::dimacs`): safe CNF parsing with propagated `SmtError`-style
  error handling.
- **SMT-LIB2 parser** (`parsers::smtlib2`): tokenizer, S-expression parser, term AST, and
  lowerings to QF_LRA, QF_BV, QF_AX, and QF_SAT (Tseitin CNF), wired into the CLI.
- **LP-MPS parser** (`parsers::mps`): free-format MPS lowering to the same `LraProblem` the
  SMT-LIB2 LRA path uses (feasibility engine, no objective optimization).
- **E-graph preprocessing** (`egraph`): dependency-free, bounded equality saturation over the
  Boolean fragment, verified by truth-table equivalence against exhaustive enumeration plus
  targeted rewrite unit tests.
- **Tiered fail-closed policy** (`policy`): `solve_certified` reseeds-and-rechecks on
  rejected SAT, falls back to the reference DPLL, then returns `Unknown`; plus an automatic
  rejection dump (`RejectionDump`) and a `VerdictTracker` for the accept/reject/inconclusive
  rate triad with a reject-threshold gate.
- **Parallel portfolio** (`portfolio` + `policy::solve_certified_portfolio`): diverse CDCL
  workers race the same CNF behind a cooperative-cancellation flag, with the same fail-closed
  fallback as the sequential path; covered by an oracle test trusting only `Accept`ed claims.
- **Reference solver and integration glue** (`reference`): `solve_and_check_*` entry points
  returning `(claim, verdict)` for CDCL, LRA, BV, and arrays, all certified end-to-end.
- **CLI** (`main`): file dispatch by extension (`.cnf` / `.smt2` / `.mps`), `--fuel`,
  `--parallel`, and `--bench` flags; re-export of `core` and `check`.
- Differential test harness vs. Z3 (`differential`) wired into CI, no-opping when `z3` is not
  on `PATH`.

[0.1.0]: https://github.com/tpt-solutions/tpt-solver/releases/tag/v0.1.0
