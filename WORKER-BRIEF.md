# RFC-0005 worker brief (remote worker sls2)

Read this before every job. Jobs are in `jobs/` on this branch (`worker-jobs`).
The coordinator session on Corey's Linux box writes them. You report by
pushing `worker-reports/<job>.md` to branch `worker-sls2`, and by trying
SendMessage to `Fix native crashes in proptest symex walker [13a13f]`.

## Environment (set up by job 1)

- Main clone: `~/work/nelli`. Deps: `~/work/deps/{softlink,nim-z3}`.
- Test image: `localhost/nelli-dev:latest`.
- Z3 4.13.4 runner: `~/work/dt413.sh <c|cpp> <test> [secs]` (runs from cwd).
- Nim, gcc and Z3 are NOT installed on the host. Everything that compiles
  or runs goes through podman (`scripts/dt-bounded.sh`, `~/work/dt413.sh`,
  `scripts/sweep.sh`).

## Hard rules (from the project's slice brief)

- **TDD, vertical.** Write one test and watch it fail (RED). Write the
  minimal code that makes it pass (GREEN). Then refactor. Always RUN the
  test; never assume RED or GREEN.
- **Bound every test run.** `scripts/dt-bounded.sh`, because non-termination
  is a real failure mode. Never run two runs of the SAME test file
  concurrently in one tree, because they clobber one binary.
- **Grep.** `grep` may be ugrep and skip gitignored files; use `command grep`
  for exhaustive sweeps.
- **Register tests.** New test files must be registered in `nelli.nimble`'s
  `test` task.
- **Walker version.** Walker-semantics slices bump `symexWalkerVersion`
  (`src/nelli/smt/canonicalize.nim`), update the `==` pin in
  `tests/tsymex_phase15_CR2_cachekey.nim` and RUN it, and add a `>=` floor
  pin in the slice's test file.
- **No `try`/`except` in the walker** except at top level (RFC §1.5).
- **No dormant substrate.** Never add a field, branch or enum arm without the
  producer that makes it live in the same slice.
- **Spec assumptions are escalations.** If the RFC is wrong about the code in
  a way that changes the design, stop and report a BLOCKER.
- **Do not narrow scope or defer.** Nothing is "for a future round".
- **Style.** Match the surrounding code's style and comment density. Cite
  `RFC-0005 S<n>` in comments.

## Git

- Work in a `git worktree` per job (`git worktree add ~/work/wt/<job> <ref>`),
  never in `~/work/nelli` itself. A fresh worktree does not compile until you
  set it up:
  - copy `nim.cfg` into it;
  - COPY the deps in as real directories (`mkdir -p _deps && cp -r ~/work/nelli/_deps/softlink ~/work/nelli/_deps/z3 _deps/`).
    Symlinks do not work: only the checkout is mounted into the container at /work, so they dangle (`cannot open file: z3`).
- Image builds on this WSL host need `podman --cgroup-manager=cgroupfs build ...`.
- Stage explicit paths only. Never use `git add -A` or `git add .`.
- **Commits.** Conventional messages (`feat(symex): RFC-0005 S8xx -- ...`)
  with a body that explains why. NO Co-Authored-By trailer, and never mention
  Claude or AI.
- **Pushing.** You may push `rfc-0005-*` slice and batch branches, and
  `worker-sls2`. Never push `main` or `rfc-0005-soundness-channels`. Never
  open a PR.
- **Windows CI.** Pushing an `rfc-*` branch triggers three Windows CI legs
  (symex-mingw, fuzzer-mingw, fuzzer-msvc). If `gh` is authenticated here,
  watch them with `gh run list --branch <b> --json headSha,conclusion,name,status`,
  polling no more often than every 5 minutes, and read failures with
  `gh run view <id> --log-failed`. If `gh` is not authenticated, say so; the
  coordinator watches CI.

## Slice report format

Report either `DONE` or `BLOCKER`.

**DONE** must include:
- sha, base and walker;
- the RED and GREEN you observed;
- the soundness bugs found;
- the design for each item;
- a per-suite table on both Z3 versions;
- the Windows run ids;
- "Different mechanisms, reported and not fixed here", with each item marked
  SOUNDNESS or PRECISION. Also commit this list in the RFC under
  "As landed (S8xx)".

**BLOCKER** must include:
- the wrong assumption or genuine fork;
- the evidence (file:line);
- your best read;
- the tree state.

## Gate sweeps

- Sweep from a worktree checked out at EXACTLY the sha being certified, and
  never edit that worktree while the sweep runs.
- Run `scripts/sweep.sh -j <N> <log>`, then push the log, plus `.summary`,
  `.drift` and `.warnings`, to `worker-sls2` as
  `worker-reports/<job>-gate.log` and the matching sibling names.
- The coordinator diffs against its baseline. A kill (rc=137) is a real
  signal; no suite is a known hang.
