# Changelog

All notable changes to tpt-solver are recorded here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added

- `api` module: `solve_str` and `solve_file` return a `Report` with the checker
  verdict, model, proof and core. The `prelude` module collects the common names.
- `check` subcommand, which verifies a proof file against its problem without
  solving.
- CLI output modes `--output human|json|competition`, using SAT-competition exit
  codes 10/20/0 in competition mode. Also `--timeout`, `--model`, `--stats`, `-v` and
  `-q`, plus `--format` and stdin (`-`).
- Gzip input, detected from its content.
- `bench` subcommand writing CSV, plus `completions` and `man` subcommands.
- `--emit-proof` works with `--parallel` and for QF_BV.
- `--explain` works for CNF, using a deletion core.
- Line numbers in DIMACS and MPS parse errors.
- Caps on DIMACS clause count and clause length, and on MPS and SMT-LIB2 variable
  counts.
- mdBook user guide in `docs/`.

### Changed

- `--bench` is now the `bench` subcommand.
- The CLI exit status for an answer the checker refused is `1`.
- Unsupported SMT-LIB2 commands (`push`, `pop`, `define-fun` and others) are errors,
  where they used to be silently ignored.
- Farkas certificate files print multipliers as `n` or `n/d`, where they used to
  print the `Debug` form.
- `todo.md` and `spec.txt` moved to `docs/internal/`.

### Fixed

- The QF_BV proof note is only printed for UNSAT answers.
- The `changelog` manifest key, which Cargo rejected, is removed.
- The egraph rule table reports malformed rules as errors instead of panicking.

## Earlier history

Phases 0 through 6 of the project plan are recorded in `docs/internal/todo.md`. They
cover the certified CDCL engine, Simplex and Farkas certificates, bit-vector and
array theories, the parsers, the parallel portfolio, and the initial CLI.
