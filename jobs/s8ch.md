# Job: S8ch -- new slice (S8cc's remainder; PRECISION)

## Setup
- Branch: create `rfc-0005-s8ch` from origin/rfc-0005-s8cc at ab4e5b5 (base 136ad60).
- Walker number is assigned at integration; use the next free one above 240 locally, and update the CR2 pin to match.
- Read WORKER-BRIEF.md, WORKER-LOCAL.md and worker-reports/s8cc.md first.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8ch"
title = "S8cc's remainder: the address of a global in a walked callee halts the path, unsafeAddr of a by-value array formal in a walked callee declines"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first, against native Nim)
1. Taking the address of a global in a walked callee halts the path. Make the path continue, with the address aimed at the global's cell.
2. `unsafeAddr` of a by-value array formal in a walked callee declines. Model it as the address of the callee's own copy of the array, so writes through it stay local to the callee.

## Verification
- Suites: yours, s8cc, s8br (2), s8bw, s8be, b6_globalrecv, b7_integration, CR2.
- Run on Z3 5.1 and 4.13.4, plus cpp for the new suite. All three Windows legs green.
- Report DONE to `worker-reports/s8ch.md`, with per-file Windows times.
