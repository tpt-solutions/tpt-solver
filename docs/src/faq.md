# FAQ

**Why does an answer come back as `unknown`?**
The search ran out of fuel, or the timeout expired. Raise `--fuel` or `--timeout`. For
linear arithmetic, the engine can also decline to decide when a model cannot be
recovered.

**The checker said `inconclusive`. Is that a bug?**
Not necessarily. The kernel could not confirm the witness, usually because it is too
short or incomplete. It is treated as not trusted. If you see it on a valid input,
please report it with the input file.

**Why is `--explain` slow on CNF?**
The CNF core is found by deletion. Each clause is tried for removal, which means one
certified solve per clause. Use it on small and medium formulas.

**Does `--parallel` produce proofs?**
Yes. The winning worker's certificate is checked and exported, the same as the
sequential path.

**Can I read a `.gz` file directly?**
Yes. Gzip input is detected by its magic bytes and decompressed, so the file name
does not matter.

**Why is `push` rejected?**
Incremental solving is not implemented. Silently ignoring `push` and `pop` could
answer a different problem than the script states, so the solver refuses instead.
