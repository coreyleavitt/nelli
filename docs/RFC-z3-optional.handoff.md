# RFC-z3-optional — handoff

- **Stage:** 2 (architect) — **rounds 1–2 COMPLETE**, mechanism resolved,
  refined & spiked
- **Round:** 1 and 2 done (5 lenses each: depth, breadth, design, feasibility,
  liveness). Round 2 ran on fable.
- **Mechanism:** RESOLVED — **design D** ("stop auto-wiring the seam"),
  Corey-approved 2026-08-28, **plus the round-2 `ConcolicAssist` refinement**
  (reify the assist; delete `GuidanceConfig.stallRounds` /
  `concolicMaxBranchAttempts`). All spike unknowns green, including the
  macro-vs-proc arity collision the round-1 spike missed.
- **Resume:** `/tdd docs/RFC-z3-optional.md S1a`

## Round 2 — headline outcomes

- **CRITICAL, verified by running it: `tests/tsmoke.nim:32` is RED on this
  tree.** `export symex` → `export choice` leaks `integerChoice` into bare
  `import nelli`. Undetected because **no workflow runs `nimble test` at all**
  (the tree says so at `symex-windows.yaml:64-68`). Gives the flip slice a
  pre-existing achievable RED and is the strongest evidence for the regression
  framing.
- **"Only `tfuzzconcolicbridge_real` changes" was false** — both
  `tfuzzconcolicbridge_g6_{affine,predicated}` also break, and they are the
  *only* end-to-end pins of the classifier S1a relocates.
- **S1a as written did not compile.** Relocation range corrected
  `:526-643` → `:382-643` (+ both bridge arms at `:799-823`, + concolic.nim's
  real import list, + a shared-helper decision).
- **`ConcolicAssist` refinement adopted** — deletes the §Required diagnostic
  surface wholesale and converts "the one risk D does not delete" into a
  compile error.
- **§Runtime error surface had no viable design** — split out as S1b2.
- Slices re-cut: S1a, **S1b1** (the flip; S1c folded in), **S1b2**, S2, S4, S5.

## Context

Follow-on to issue #160, filed after v0.6.0 shipped. Branch `rfc-z3-optional`
off `main` at `1f50752` (v0.6.0). Nothing implemented yet — RFC + slices only.

## Slices (re-cut in round 2)

- [ ] **S1a** — relocate the bridge builder to `src/nelli/concolic.nim`.
      Moves `fuzzmacro.nim:382-643` (the whole G6 cluster — the seven helpers
      at `:382-526` are load-bearing) **plus both** bridge arms at `:799-823`.
      concolic.nim imports `std/macros`, `./symex` (+export), `./fuzz`,
      `./smt/transparency`, `./fuzzmacro` (for the shared
      `propFormalParams`/`countFormalParams`/`liftPropIfNeeded`, which get
      exported). Core still auto-wires — pure relocation.
      **RED:** new `tests/tfuzzconcolicassist.nim` (must be `tfuzz*`-prefixed
      for CI). DoD: bounded suites via `dt-bounded.sh`, not `nimble test`.
- [ ] **S1b1** — **produces the load-bearing property, both halves.** 4-arg
      `fuzz` overload (param literally named `assist`); drop
      `import ./symex`/`export symex`; `ConcolicAssist` reification +
      `GuidanceConfig` field removal; `fuzzConcolic` (folded in from old S1c);
      migrate **three** real-bridge tests + 3 loop-level sites +
      `tfuzzconfigdefaults:40-41`. DoD: probe Z3-free, **`tsmoke` green**,
      gate + both g6 suites green with positive-signal checks, `tfuzzloop` +
      `tfuzzmacro` green (arity pin), paired negative control.
- [ ] **S1b2** — missing-libz3 degradation. Catch in `concolicAssist`'s
      generated closure (NOT `fuzz.nim` — can't name `SoftlinkError` there);
      new `cfoSolverUnavailable` outcome; once-per-campaign latch.
- [ ] **S2** — pin the probe in **both** fuzzer legs (windows + msvc twins),
      corrected flags, **plus an explicit half-(2) discovery assertion**.
- [ ] ~~**S3**~~ — deleted. (Round 2: its premise "no achievable RED" was
      wrong — `tsmoke` was one; now claimed by S1b1.)
- [ ] **S4** — consumer docs + build matrix + missing-libz3 behavior +
      **`docs/fuzz/INTERFACE.md`** (normative, pinned by `tfuzzpackaging`).
- [ ] **S5** — release mechanics: 0.7.0, **no CHANGELOG exists** (commit msg +
      tag + tianguis-publish), **three** stale version sites
      (`src/nelli.nim:20`, `milpa.kdl:5`, `nelli.nimble`), chapulin audit spec.
      amoxtli audited clean — zero nelli imports.

## Open forks (awaiting Corey)

None. The mechanism fork closed on design D in round 1; round 2's
`ConcolicAssist` refinement was applied under the standing bar (verified sole
consumer chain, deletes more than it adds). Flagged for sanity-check, not
blocking — it widens the 0.7.0 break from `export symex` to also include two
`GuidanceConfig` fields.

## Spike results (2026-08-28, `localhost/nelli-dev:latest`)

Artifacts in `scratchpad/z3spike/` (throwaway; safe to delete).

- Assist expression semchecks in the **caller's** scope and splices into core's
  `quote do` — **yes**, positional and named. Proven by branch-count: a
  2-branch property returned 2, a 1-branch property 1.
- 2-/3-/4-arg `fuzz` overloads coexist — **yes**.
- Core-only consumer with the walker unreachable compiles, `assist=NONE`.
- `fuzzConcolic` sugar works.
- **Gotcha:** the named-arg form needs the macro param literally named
  `assist`; `assistExpr` fails with "unknown named parameter: assist".
- **Real-tree half (1) proven:** with symex dropped, both bridge arms nil'd and
  the classifier removed, `tests/tz3free_probe.nim` printed `z3-free probe OK`.
  Patch reverted; `tests/tz3free_probe.nim` is kept (untracked → commit in S1b).
- **Design refinement the spike forced:** `classifyStrategyExpr`/
  `bindingExprFor` reference `ccoEq` from the Z3-importing `smt/runtime.nim`
  and must move WITH the bridge — hence `concolicAssist` takes the strategy
  too. Without it: `fuzzmacro.nim(628): undeclared identifier: 'ccoEq'`.
  (Round 2 fixed the argument order to `(strat, prop)`, matching `fuzz`; the
  transposition was itself a latent coherence bug.)

## Round 1 findings (all 5 lenses, verified against `1f50752`)

- **Unanimous CRITICAL:** `concolicFlip` is a **macro** (`symex.nim:1247`),
  not a proc. It does compile-time AST capture via `parseEntryImpl`
  (`smt/dsl_parser.nim:8850`) and splices a `SymexProgram` IR literal +
  `runConcolicFlipImpl` into the caller. A runtime proc-var cannot route it.
  The real seam is **parse/IR (Z3-free) vs walk/solve (Z3-bound)**; only
  `symex.nim:22`, `smt/runtime.nim:28`, `smt/regex_parser.nim` import z3.
- **Probe flags unsound:** need `--skipUserCfg --noNimblePath`; drop the
  softlink path. Current baseline passes RED only by environment luck.
- **Liveness:** most Track-G tests don't discriminate; exactly one does.
- **Breaking change** (`export symex` removal) was undeclared; needs 0.7.0.
- **README already promises the target state** (`:91-95`) — this is a
  regression fix, and the v0.6.0 wiring broke a documented contract.

## Key decisions (this session)

- ~~**Feasibility resolved before writing the RFC, not assumed.**~~
  **OVERTURNED IN ROUND 1.** The stage-1 conclusion — "the only walker-bound
  symbol is `concolicFlip`, a proc — exactly what a hook routes" — was wrong.
  It inspected only `fuzzmacro`'s *pre-expansion* output. `concolicFlip` is a
  macro; post-expansion the spliced code carries the walker's IR surface. The
  issue's original open question ("does the hook signature have to widen?")
  resolves **yes**, or is dispensed with entirely by compile-time gating.
  The four-type claim itself still holds (verified `smt/runtime.nim:12687-12732`),
  but the inventory was incomplete — enum *values* and three static defaults
  were missed.
- **The type move is no longer needed.** R29b's precedent was real, but under
  design D core constructs no bindings, so the four types / enum values /
  static defaults stay put in `smt/runtime.nim` — they are only needed where
  the bridge is built, which is now `nelli/concolic` (which imports symex
  anyway). Round 1 correctly found the draft's inventory incomplete; the right
  fix turned out to be deleting the requirement, not completing the list.
- **Verification channel simplified** (still true), **but the flag set was
  wrong.** `--skipProjCfg --skipParentCfg` misses `~/.config/nim/nim.cfg` and
  the nimblepath; add `--skipUserCfg --noNimblePath`. "Local, seconds" also
  assumed a host Nim, which does not exist — the probe runs in the podman
  image. Corrected invocation is in the RFC.
- **RED baseline captured and re-confirmed under the corrected flags:**
  `src/nelli/symex.nim(22, 8) Error: cannot open file: z3`, rc=1. Then proven
  invertible — see §Spike results.
- **Design D approved by Corey 2026-08-28**, together with spike-before-slice
  sequencing.

## Review ledger (stage 4)

Not started.
