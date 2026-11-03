# Contributing to tpt-solver

Thanks for your interest. This project's central rule is that nothing the solver
reports is trusted until the independent checker accepts it. Contributions are
judged against that rule first.

## Getting set up

```sh
cargo build --workspace
cargo test  --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

The toolchain is pinned to 1.85 in `rust-toolchain.toml`, which is also the MSRV.

## Where changes go

- `tpt-solver-check` is the trusted kernel. It has no dependencies and must stay
  `no_std`. Any change to it needs a regression test, and it should be easy to audit
  line by line.
- `tpt-solver-core` is the untrusted engine. It has no dependencies, and its checks
  are the fuel budget and the checker's verdict, not the engine's own bookkeeping.
- `tpt-solver` is the periphery: parsers, the `api` module, the CLI, and glue. It may
  use MIT- or Apache-compatible dependencies.

## Expectations for a change

- Add a test that would have failed before the change. Parser fixes get a regression
  case, and solver fixes get an oracle or property test where one applies.
- Keep the tests passing on Linux, Windows and macOS.
- Do not add a new trust path. If an answer is reported, it must go through the
  checker first.
- Keep public APIs documented. The library builds with `missing_docs` warnings
  denied in CI.
- User-visible changes get a line in `CHANGELOG.md`.

## Commits and pull requests

Keep commits focused, and write the message in the imperative mood. A pull request
description should say what changed and why, and how you tested it.

## Reporting bugs

For a wrong answer, include the input and the exact command. If the checker rejected
something valid, say so explicitly, since that is itself a bug report. For security
issues, follow [SECURITY.md](SECURITY.md) instead of opening a public issue.
