# Command line

```text
tpt-solver [OPTIONS] [INPUT]          solve INPUT ("-" reads standard input)
tpt-solver check PROBLEM PROOF        check a proof against its problem, without solving
tpt-solver bench [--seeds N]          random 3-SAT ladder, CSV on standard output
tpt-solver completions <SHELL>        print a shell completion script
tpt-solver man                        print the man page
```

Running `tpt-solver` with no input runs a short built-in demo of the pipeline.

## Input and format

INPUT may be DIMACS CNF, SMT-LIB2, or LP-MPS. It may also be gzip-compressed, which
is detected from its magic bytes. The format is chosen in this order:

1. `--format dimacs|smt2|mps`, if given.
2. The file extension: `.cnf`, `.smt2`, `.smt`, `.mps`, optionally followed by `.gz`.
3. The content: a `p cnf` header, a leading `(`, or a column-zero `NAME`/`ROWS`
   section keyword.

Standard input has no extension, so either pass `--format` or rely on content
detection.

## Options

| Flag | Meaning |
|------|---------|
| `--format FORMAT` | Input format when it cannot be detected |
| `--output human\|json\|competition` | Output style (default `human`) |
| `--fuel N` | Engine step budget per run (default `10000000`) |
| `--timeout SECS` | Wall-clock limit; expiry reports `unknown` |
| `--parallel N` | Race `N` diverse CDCL workers (CNF only) |
| `--emit-proof FILE` | On UNSAT, write the checked certificate to `FILE` |
| `--explain` | On UNSAT, report the needed clauses or constraints |
| `--model` | Print the model on SAT |
| `--stats` | Print sizes and timing to stderr |
| `-v`, `-q` | More or less detail on stderr |

`--parallel` applies only to CNF input. For SMT-LIB2 and MPS it is ignored.

MPS input is feasibility-only. The objective (`N`) row is dropped, so the solver
answers whether the constraints are satisfiable and does not optimize.

## Output

`human` prints one result line such as `UNSAT: proof verified by the trusted kernel`,
followed by details. `json` prints a single object with `result`, `checker`,
`theory`, `model`, `core`, `proof_file`, and `stats`. `competition` uses SAT-competition
conventions: `s SATISFIABLE` followed by `v` lines, `s UNSATISFIABLE`, or
`s UNKNOWN`.

## Exit codes

| Code | Meaning |
|------|---------|
| `0` | Answer accepted by the checker, or `unknown` |
| `1` | The checker did not accept a SAT or UNSAT claim |
| `2` | Usage, I/O, parse, or lowering error |
| `10` | SAT, accepted (`--output competition` only) |
| `20` | UNSAT, accepted (`--output competition` only) |

For `check`, the exit codes are `0` when the proof is verified and `1` otherwise.
