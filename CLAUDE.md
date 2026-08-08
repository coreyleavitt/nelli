# proptest

Property-based testing for Nim with internal choice-sequence shrinking, plus
the `proptest/symex` symbolic-execution engine (Z3 via nim-z3/softlink).

- nim is NOT installed on the host — build/run tests in the Windows container
  `chapulin-symex:2.2.10` (see the `windows-symex-toolchain` memory for the
  exact `docker run` invocation and `--cincludes:C:/z3/include`).
- Active RFC: `docs/RFC-chapulin-hardening.md` (round 6 current) with handoff
  at `docs/RFC-chapulin-hardening.handoff.md`; symex design ADRs live in
  `docs/SYMEX_PLAN.md`.
- Walker semantics changes bump `symexWalkerVersion` (`smt/canonicalize.nim`)
  and add a version-floor pin in the round's test file.

## Compact Instructions
When compacting, preserve in the summary: the active RFC and its handoff-doc path, the current stage/round, slices done vs remaining, open forks awaiting me, and the exact resume command. After compacting, re-read the handoff doc and MEMORY.md before continuing.
