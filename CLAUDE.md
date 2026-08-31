# nelli

Property-based testing for Nim with internal choice-sequence shrinking, plus
the `nelli/symex` symbolic-execution engine (Z3 via nim-z3/softlink).

- nim is NOT installed on the host — build/run tests in the Windows container
  `chapulin-symex:2.2.10` (see the `windows-symex-toolchain` memory for the
  exact `docker run` invocation and `--cincludes:C:/z3/include`).
- RFCs are numbered `docs/rfc/NNNN-slug.md` (+ `.handoff.md`). Conventions —
  the controlled Status vocabulary, Category slugs, and the Depends-on shape
  that actually produces graph edges — are in `docs/rfc/README.md`. Read it
  before adding or restatusing an RFC.
- Active RFC: `docs/rfc/0001-chapulin-hardening.md` (round 6 current) with handoff
  at `docs/rfc/0001-chapulin-hardening.handoff.md`; symex design ADRs live in
  `docs/SYMEX_PLAN.md`.
- Work status is tracked by quipu at `quipu.leavitt.dev` (project `nelli`),
  which mounts this repo read-only and never writes to it. Query the hub
  instead of re-auditing the docs tree — see `.claude/skills/tracker/`.
- Walker semantics changes bump `symexWalkerVersion` (`smt/canonicalize.nim`)
  and add a version-floor pin in the round's test file.

## Compact Instructions
When compacting, preserve in the summary: the active RFC and its handoff-doc path, the current stage/round, slices done vs remaining, open forks awaiting me, and the exact resume command. After compacting, re-read the handoff doc and MEMORY.md before continuing.
