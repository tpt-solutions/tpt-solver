# Security policy

## Supported versions

tpt-solver is pre-1.0. Only the latest release on `master` receives security fixes.

## Reporting a vulnerability

Please do not open a public issue for a security problem. Report it privately
through GitHub's "Report a vulnerability" button on the repository's Security tab.
If that is not available, contact the maintainers at TPT Solutions.

Please include the input that triggers the problem, the command you ran, and what
you observed. We aim to acknowledge reports within a few working days.

## What counts

- A way to make the checker accept a wrong answer or an invalid proof. This is the
  most serious class of issue for this project.
- A crash, panic, hang or unbounded memory use reachable from untrusted input. The
  parsers are fuzzed, and any input that bypasses their limits is in scope.
- A path that reports a result the checker did not accept.

Denial of service through a legitimately hard problem is not a vulnerability. The
fuel and timeout limits are the intended mitigation for that.
