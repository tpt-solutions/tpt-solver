# Fuel versus timeout

Two limits stop a search from running forever. They fail in different ways.

**Fuel** (`--fuel N`) is a step budget. Each engine run counts steps, and when the
budget is used up the run returns `unknown`. Fuel is deterministic. The same input
with the same budget gives the same result on every machine. Use fuel for
reproducible runs, for tests, and for benchmarks.

**Timeout** (`--timeout SECS`) is wall-clock time. The solve runs on a helper
thread, and if it has not finished when the limit expires, the call reports
`unknown`. Results depend on machine speed and load.

When either limit is hit, the answer is `unknown`. The checker is never asked to
accept a guess, so `unknown` is always safe to report.

The CLI exits the process after printing, so a timed-out helper thread is cleaned up
when the process ends. A library caller that keeps running should prefer fuel. See
[Library use](library.md).
