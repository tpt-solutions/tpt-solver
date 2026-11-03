# Proof formats

Every UNSAT answer can be exported as a proof with `--emit-proof FILE`, or with
`Options::want_proof` in the library. The format depends on the theory. The
checker accepts exactly these formats when you run `tpt-solver check`.

## CNF and DRAT-style clause lists

Used for DIMACS input, and for SMT-LIB2 QF_SAT lowered to CNF.

Each line is one derived clause. It lists its literals as signed DIMACS integers,
then a `0`:

```text
3 -1 0
2 0
0
```

- Clauses appear in derivation order.
- Each clause must follow from the input clauses and earlier lines by reverse unit
  propagation (RUP): assume the negation of the clause and propagate. If that
  reaches a conflict, the clause is valid.
- The final line is the empty clause, `0`. Its presence is what makes the proof an
  UNSAT proof.
- There are no deletion (`d`) lines and no LRAT hints. This is the RUP subset of DRAT.

The engine's learned clauses are checked this way. The checker does not trust the
solver's own bookkeeping.

`tpt-solver check PROBLEM PROOF` reads this format. A file containing a `d` line is
refused as unsupported.

### Compatibility with external checkers

The output is designed to be valid DRAT, so `drat-trim` should accept it. This has
not been run yet, because `drat-trim` is not available in the development
environment. Treat that as unverified until someone runs it.

## Bit-vector proofs

For QF_BV, the proof is a DRAT-style list over the bit-blasted CNF that the engine
built. That CNF is not exported yet, so `tpt-solver check` cannot check a BV proof
on its own. The library API returns the clauses, and the blast is available inside
`tpt_solver_core::bv`.

## Farkas certificates (linear arithmetic)

Used for SMT-LIB2 QF_LRA and MPS input.

The file starts with `#` comment lines. Each following line is an `index multiplier`
pair, and both fields are plain text:

```text
# Farkas certificate: nonzero (index multiplier) pairs
0 1
1 1
2 1
```

- The index refers to the constraint list that the input was lowered to. For
  SMT-LIB2 that is `Script::to_lra`. For MPS it is `parse_mps`, where an equality row
  produces two constraints and each variable bound adds more.
- A multiplier is an exact rational, written `n` or `n/d`. Multipliers are
  nonnegative, and only nonzero ones are listed.
- Summed with the multipliers, the constraints give a contradiction of the form
  `0 <= negative`.

The checker verifies the combination exactly, using the same rational arithmetic as
the solver.

## Choosing a format

| Input | Proof | Standalone `check` |
|-------|-------|--------------------|
| DIMACS | DRAT-style clause list | yes |
| SMT-LIB2 QF_SAT | DRAT-style clause list | yes, over the lowered CNF |
| SMT-LIB2 QF_LRA, MPS | Farkas certificate | yes |
| SMT-LIB2 QF_BV | DRAT-style clause list over the blast | no (see above) |
| SMT-LIB2 QF_AX | none yet | no |
