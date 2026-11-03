# Library use

The crate `tpt-solver` exposes the same pipeline as the binary. The shortest path is
`solve_str` or `solve_file`, both in the prelude:

```rust
use tpt_solver::prelude::*;

let report = solve_str(
    "p cnf 3 4\n1 2 0\n-1 3 0\n-2 3 0\n-3 0\n",
    Format::Dimacs,
    &Options {
        want_proof: true,
        explain: true,
        ..Options::default()
    },
)?;

assert_eq!(report.claim, SolveResult::Unsat);
assert!(report.verdict.is_accept());
println!("needed clauses: {:?}", report.core);
# Ok::<(), Error>(())
```

A `Report` holds the claim, the checker's verdict, a model on SAT, a proof on UNSAT
when requested, a core when requested, and some stats. Check the `verdict` before
trusting anything in the report.

## Standalone checking

`check_proof_text` verifies a proof file against its problem without solving, so
an external solver's proof can be checked with the same kernel. It takes the problem
text, its format, and the proof text.

## Feature status

The only feature flag is `std`, which is on by default and does not change behaviour yet.
Serde support is planned but not added.
