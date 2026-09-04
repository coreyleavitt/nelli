# nelli

Property-based testing for Nim with internal choice-sequence shrinking, plus
the `nelli/symex` symbolic-execution engine (Z3 via nim-z3/softlink).

- nim is NOT installed on the host. Build/run tests via `scripts/dt.sh` or
  `scripts/dt-bounded.sh <c|cpp> <test.nim>` (podman, `localhost/nelli-dev`);
  `scripts/dt-crosswin.sh` cross-compiles for `--os:windows` to catch Windows
  API misuse without a Windows host. Six `tsymex_r6_*` suites hang under
  Linux/podman — see the `symex-r6-linux-hangs` memory before reading a red
  sweep as a regression.
- Whole-suite work is gated by `scripts/sweep.sh <outlog>` (every
  `tests/t*.nim` in parallel, the six Linux hangers skipped by name) and
  `scripts/sweep-diff.sh <baseline> <current>`. The suite is not green on a
  good day, so the gate is *what moved against a recorded baseline*, never
  "the sweep passed". `scripts/psweep.sh` remains the `tsymex_*`-only,
  both-backends sweep. `sweep.sh` also writes `<outlog>.drift`: 92
  `tests/t*.nim` are registered in neither `nelli.nimble` nor any CI leg.
- The patched Nim toolchain is also published as an OCI **artifact**
  (`ghcr.io/coreyleavitt/nim:2.2.10-<platform>`), pullable with plain curl and
  usable directly on the host — no container required. CI uses it via
  `.github/actions/setup-nim-artifact`. It ships Nim ALONE, so the C compiler
  must be supplied and `--cc:` pinned explicitly, or Nim falls through to
  `vcc` on Windows. (This replaced `chapulin-symex:2.2.10`, a container
  defined in the CHAPULIN repo — nelli no longer depends on a consumer for
  its own toolchain.)
- Three Windows CI legs, named by C compiler: `fuzzer-msvc`, `fuzzer-mingw`,
  `symex-mingw`. All containerless. New RFC branches must be named `rfc-*` to
  get Windows verification (the triggers are `[main, 'rfc-*']`).
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
