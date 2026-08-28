# RFC — make `import nelli` Z3-free by inverting the concolic bridge

**Issue:** #160 · **Branch:** `rfc-z3-optional` (off `main` at v0.6.0, `1f50752`)
**Status:** stage 2 (architect) — round 1 applied · **BLOCKED** on §Mechanism

## §0 — Thesis

`import nelli` forces every downstream consumer to resolve Z3 at compile time,
to serve a capability that is **runtime-off by default**. A consumer using only
`property`/`StateMachine`/`forAll` — or `fuzz(...)` without concolic assist —
pays the heaviest native dependency in the tree for code it never executes.

Invert it: the core keeps a bridge that is absent by default, and the
walker-touching implementation moves to an opt-in module. `import nelli` stops
reaching Z3; `import nelli/concolic` restores today's behavior.

*(Round 1: the draft said "a nil-defaultable bridge hook … an opt-in module
that registers into that hook." That specific mechanism is unbuildable —
`concolicFlip` is a macro, not a proc. The thesis survives; the instrument is
an open decision. See §The crux and §Mechanism.)*

## Ground truth — verified, not assumed (2026-08-28)

Every claim below was checked against the tree at `1f50752`.

**The chain is real.** `nelli.nim:22` imports/exports `fuzzmacro`;
`fuzzmacro.nim:49` does an unconditional `import ./symex`, `:51` `export symex`;
`symex` reaches the walker, which imports `z3`.

**Proven RED, with a repro** (flags corrected in round 1 — see §Verification
channel for why the original set was unsound):

    nim c --hints:off \
          --skipProjCfg --skipParentCfg --skipUserCfg --noNimblePath \
          --path:src <probe importing nelli>
    => src/nelli/symex.nim(22, 8) Error: cannot open file: z3   (rc=1)

The baseline itself still holds; it was captured in an environment with no
nimble-installed z3, which is exactly the fragility the corrected flags remove.

**The runtime path is already off by default.** `GuidanceConfig.stallRounds`
defaults `0`, and `tryConcolicBridge` early-returns unless the bridge is
non-nil AND `stallRounds > 0` AND the frontier is stalled. So the link is
unconditional for a feature almost nobody runs.

**`fuzz.nim` already proves the separation works.** It imports
`./smt/concolictaxonomy` (`:21`) and stays Z3-free; that leaf module's own doc
records that none of its types reference Z3. R29b moved `ConcolicFlipResult`/
`ConcolicFlipCounters` there for exactly this reason — the precedent is in-tree.

### The crux — the issue's risk is REAL (round-1 correction)

> **Round 1 overturned this section.** The pre-round-1 draft claimed
> `concolicFlip` was a proc and therefore routable by a runtime hook. It is
> not. All five review lenses refuted this independently against source. The
> corrected analysis follows; the mechanism it implies is an **open decision**
> (see §Mechanism — open decision).

The issue flagged one risk: if the macro's spliced codegen inlines walker-*typed
expressions* rather than a single call, the hook signature must widen. **It
does.**

`concolicFlip` is a **macro**, not a proc — `symex.nim:1247`:

    macro concolicFlip*(fn: typed, trace, bindings: typed,
                        targetBranchIndex: typed,
                        settings: static SymexSettings = ...): ConcolicFlipResult

Its whole job is compile-time AST capture. It calls `parseEntryImpl`
(`smt/dsl_parser.nim:8850`) at macro-expansion time to walk the property's
typed AST, then splices into the **caller's module** a `SymexProgram(...)` IR
literal plus a call to `runConcolicFlipImpl` (`smt/runtime.nim:13098` — the
module that does `import z3` at `:28`).

Two consequences:

1. **A runtime proc-var cannot hold a macro.** "Register the real
   `concolicFlip` into a nil-defaultable hook" is a type error, not a slice.
2. **The walker's only ingestion door is `fn: typed → getImpl → parseProc`**
   (`fuzzmacro.nim:10-11`). A runtime closure is unwalkable *by design*, so no
   hook of the originally proposed shape can carry the property.

The prior draft inspected only fuzzmacro's **pre-expansion** output
(`:797-823`) and stopped there. Post-expansion, the spliced code references the
walker's IR surface — `fuzzmacro.nim:52-60` says so in-tree: free identifiers
include "IR constructor names, `IRExprKind` enum values like `iekStrLen`".

**The good news: a seam still exists, and it cuts cleanly — just not where the
draft put it.** Only three modules under `src/` import z3:

| Z3-free (verified import lists) | Z3-bound |
|---|---|
| `smt/types.nim` — `SymexProgram:1516`, `SymexSettings:1750` | `symex.nim:22` |
| `smt/dsl_parser.nim` — `parseEntryImpl:8850` | `smt/runtime.nim:28` |
| `smt/concolictaxonomy.nim`, `dsl_typebridge`, `stdlib_models`, `exn_hierarchy` | `smt/regex_parser.nim:37-41` |

So the boundary is **parse/IR (Z3-free) vs. walk/solve (Z3-bound)**, not
`fuzzmacro` vs. `symex`. Z3 enters only at `runConcolicFlipImpl`.

### What survives from the draft

- The four binding types **are** pure data and movable — verified at
  `smt/runtime.nim:12687-12732` (int/int64/bool/enum/seq only). The R29b
  precedent is real (`:12734` documents the prior move).
- `smt/concolictaxonomy.nim` is genuinely Z3-free (its only `z3` hit is a doc
  comment at `:9`), `smt/runtime.nim:36/:42` already imports **and re-exports**
  it, and `concolictaxonomy` imports only `std/tables` + `../choice` — **no
  cycle**. The move target is pre-wired.
- `tryConcolicBridge` really is inert by default (`fuzz.nim:1595-1596`;
  `stallRounds = 0` default at `:1009`).

### Inventory gaps the draft missed

The "four types" set is incomplete. Also required:

- **Enum *values***, not just type names: `cbDrawLinked`, `cbTransformLinked`,
  `ccoEq`…`ccoGe` (`fuzzmacro.nim:608,629-642,817`). These resolve today only
  via `fuzz.nim:30`'s **module-level** `export concolictaxonomy` — S1 must
  preserve a module-level re-export, not an enumerated per-type list.
- **The macro's static defaults** `defaultMaxConcolicDraws`,
  `defaultMaxRelaxationAttempts`, `defaultZ3TimeoutMs` live in the
  **Z3-importing** `smt/runtime.nim:12763,13005,13011`. They must move to a
  Z3-free home or be frozen into the registrar.

### Mechanism — OPEN DECISION (awaiting sign-off)

Three candidate mechanisms. **This RFC does not yet pick one**; S1 cannot be
written until it does.

- **(A) Caller-scope compile-time gating.** `fuzzmacro` emits
  `when declared(concolicFlip): <today's exact bridge> else: <nil bridge>`,
  resolved in the caller's scope. `import nelli/concolic` flips codegen on,
  **per call site**. No global state, no registration timing, no gcsafe
  hazard; core pulls *zero* symex (not even the parser); byte-identical
  codegen when opted in. Cost: opt-in is module-granular and invisible at the
  call expression; needs a collision-proof marker symbol; requires verifying
  `when declared` re-semas correctly in typed-macro output.
- **(B) Explicit solver in `GuidanceConfig`.** Split frontend from solver;
  `fuzzmacro` parses (Z3-free) and calls a `ConcolicSolver` proc field the
  user sets: `GuidanceConfig(stallRounds: 40, solver: concolicSolver)`.
  Forgetting the import is a **compile error**, not silent degradation;
  matches the in-tree precedent of `fuzz*[T](..., concolicBridge = nil)`
  (`fuzz.nim:1798`). Cost: every `fuzz(...)` caller compiles the ~9k-line
  `dsl_parser` + 3.3k-line `types.nim` frontend and embeds the IR literal even
  when concolic is never used; adds public API surface.
- **(C) Widened runtime hook over `SymexProgram`.** The draft's registry,
  repaired. **Dominated** — carries B's frontend cost *and* the global-state
  hazards A and B both avoid. Recorded for completeness; not recommended.

A process-global proc-var **cannot vary per call site**, so the Non-goals'
stated reason for rejecting `-d:nelliConcolic` also indicts (C).

## Load-bearing property

> **A module that does `import nelli` compiles with no Z3 on the path, and
> adding `import nelli/concolic` restores end-to-end concolic solving.**

Both halves, or it has not landed. The first half alone is achievable by
deleting the feature; the second half is what proves the seam rather than a
removal. **S1c produces both** (S1a/S1b are its prerequisites, and S1b ships
the negative control that makes half (2) falsifiable).

Half (2) must be proven by a **positive signal through the real entry point**,
not by a green suite. The discriminating assertion already exists in-tree —
`concolicYield.solvedExact + solvedOptimistic > 0` and
`provenanceCounts[pvConcolic] > 0` — see S1c. Most Track-G tests do **not**
discriminate: `tfuzzconcolicbridge.nim` passes a *fake* bridge by parameter at
every call site (`:32,47,67,92,108,136,181,226-227,247`), bypassing any seam
entirely, and `tfuzzconcolicbridge_real.nim:49-66` asserts only
`iterations == 60` / `coverageHits >= 1` — green whether or not the bridge ever
fires. Naming the exact test and the exact assertions is therefore load-bearing,
not pedantry.

## Verification channel — cheaper than the issue assumed

The issue proposed a Z3-free CI image. Not required. Withholding the z3
`--path` makes any transitive `import z3` fail at Nim compile time, which is
the dependency we care about — z3 binds via softlink/dynlib, so there is no
separate static-link step to catch. Deterministic, needs no new image.

**The draft's flag set was unsound.** `--skipProjCfg --skipParentCfg` does
**not** exclude two channels that can still resolve `import z3`:

- the *user* config `~/.config/nim/nim.cfg` — needs `--skipUserCfg`;
- the nimblepath `~/.nimble/pkgs2` — needs `--noNimblePath`.

The repo's z3 is vendored via the milpa-generated root `nim.cfg`
(`--path:"_deps/z3/src"`), so the captured RED baseline passes today only by
luck of this environment having no nimble-installed z3. On any machine or
container where a z3 package lands in the nimble dir, the check goes **silently
green even if `import nelli` has regressed**. The probe must not depend on what
happens to be installed.

`--path:_deps/softlink/src` is also unnecessary — nothing under `src/` imports
softlink — and dropping it makes an accidental direct softlink import fail too.

**Committed probe.** `tests/tz3free_probe.nim`, body `import nelli`.

**Exact invocation** (there is no host Nim — see CLAUDE.md):

    podman run --rm -v "$PWD:/work" -w /work localhost/nelli-dev:latest \
      nim c --hints:off \
            --skipProjCfg --skipParentCfg --skipUserCfg --noNimblePath \
            --path:src tests/tz3free_probe.nim

S2 must confirm `scripts/derive-ci-suites.ps1` does not auto-pick the probe
into the normal (z3-pathed) suite run — harmless if it does, but stated.

## This is a regression fix, not a new feature

`README.md:91-95` **already documents the target state**:

> | Everything except symex | Nim ≥ 2.0.0, no external dependencies |
>
> "`import nelli` never touches Z3 — symbolic execution lives behind the
> separate `import nelli/symex`."

The v0.6.0 G3 C4 wiring silently broke that documented contract;
`fuzzmacro.nim:53-72` calls it an "accepted, already-anticipated consequence."
So this work restores a promise the README still makes. The CHANGELOG entry is
**Fixed**, not **Changed**.

## Slices — producer first

Ordered so the load-bearing property runs end-to-end at S1c; later slices
harden rather than complete it.

**The draft's single S1 was a round mislabeled as a slice.** Its honest file
list spans 7-8 modules across a compile-time/runtime seam: `smt/runtime.nim`
(extract types from a 13k-line module), `smt/concolictaxonomy.nim`, a new
Z3-free hook/gating module, `fuzzmacro.nim` (drop `:49/:51`, rewrite both
emitted arms `:797-823`), new `src/nelli/concolic.nim`, `nelli.nim`, the
committed probe, and `tests/tfuzzconcolicbridge_real.nim`. One implementing
agent would inherit that whole blast radius. Re-sliced:

- **S1a — pure type move.** The four binding types + the three static defaults
  (`defaultMaxConcolicDraws`, `defaultMaxRelaxationAttempts`,
  `defaultZ3TimeoutMs`) from `smt/runtime.nim` → `smt/concolictaxonomy.nim`.
  Mechanically safe: the re-export is pre-wired (`smt/runtime.nim:36/:42`),
  no cycle. Preserve the **module-level** `export concolictaxonomy` so enum
  *values* keep resolving. **DoD:** full `nimble test` green, zero behavior
  change. Additive — trivially revertible.

- **S1b — the seam, bridge-absent half.** Add the chosen mechanism
  (A/B/C — *blocked on §Mechanism*); `fuzzmacro`'s emitted bridge routes
  through it; no registrar yet. **DoD (RED asserted deliberately):**
  `tfuzzconcolicbridge_real`'s `stallRounds > 0` gate test now **fails** —
  that is the new bridge-absent behavior — plus the negative control below
  passes. Must also state whether the unregistered path passes `nil` or a
  no-op closure to `fuzz(...)`: a no-op closure shifts `tryConcolicBridge`'s
  attempt counters and `tfuzzconcolicbridge.nim`'s fake-bridge assertions.

- **S1c — the registrar (produces the load-bearing property).**
  `nelli/concolic` becomes the sole walker importer and supplies the real
  solve. **DoD:** `tests/tfuzzconcolicbridge_real.nim` test *"stalled campaign
  with the real bridge wired (stallRounds > 0) breaks the 0xCAFEBABE gate"*
  is **red on S1b's tree and green here**, with its positive-signal checks
  intact:

      check report.coverageHits == 2
      check report.stats.concolicYield.solvedExact +
            report.stats.concolicYield.solvedOptimistic > 0
      check report.stats.provenanceCounts[pvConcolic] > 0

  Note this test **cannot pass "unchanged"** — its header (`:9-11`) documents
  "deliberately just `import nelli` … still gets it for free" as its whole
  point. S1c inverts that contract: the import *and* the docstring change.

- **S1d — drop the dependency.** Remove `import ./symex` / `export symex`
  from `fuzzmacro`. **DoD:** the Z3-free probe compiles (the captured RED
  baseline goes green) AND full `nimble test` green. Fold into S1b/S1c only
  if the diff stays small.

- **S2 — pin it in CI.** Add the probe as a step in `fuzzer-windows.yaml`
  (PowerShell), with the corrected flag set. **S2 pins only half (1).** The
  probe passes identically if `nelli/concolic` were deleted outright — the
  exact scenario "Both halves, or it has not landed" forbids. Half (2) is
  pinned by `tfuzzconcolicbridge_real` inside the existing
  `^(tfuzz|tdb|tengine_)` glob (`fuzzer-windows.yaml:183`); S2 must state that
  coupling so it is not silently broken later.

- **S3 — deleted.** Pre-verified green: `fuzzmacro.nim:49/:51` is the only
  `import ./symex` in `src/` outside `symex` itself; every other umbrella
  re-export (`fuzzworker`, `parallel`, `bmc`, `symbolic`, `mining`, `bisim`,
  `mutation`, `laws`, `metamorphic`, `jsonschema`, `engine/*`) reaches neither
  z3 nor symex (`engine/types.nim:198` and `coverage.nim:95` document the
  deliberate avoidance). S3 had no achievable RED, and the probe compiles the
  entire `import nelli` closure anyway — a second route would already fail it.
  Its residual value *is* S2.

- **S4 — consumer-facing docs.** `docs/fuzz/USAGE.md` + README: concolic
  assist needs one extra import, and why. Include the consumer build matrix
  and the missing-libz3 runtime behavior (below).

- **S5 — release mechanics (NEW).** Breaking public-surface change ⇒ 0.7.0;
  CHANGELOG naming the removed transitive surface and the one-line migration;
  downstream note for chapulin (already pending the v0.6.0 `FuzzSettings`
  regroup) and amoxtli. Also fix `src/nelli.nim:20` — `nelliVersion*` is
  stale at `"0.1.0"` against a 0.6.0 package.

No slice ships a consumer without its producer: S1b's gating and S1c's
registrar land as a pair, and S1b is merged only with its negative control
asserting the bridge-absent behavior — never nil-only with "a later slice
registers it."

## Risks

- **Macro hygiene at the splice site.** Generated code resolves identifiers in
  the *caller's* scope. `fuzzmacro.nim:53-64` records a real prior footgun, so
  S1 must prove it with a macro-call-site test, not a unit test.
- **Silent regression.** Without S2, any future `import` in the wrong module
  reintroduces the dependency invisibly. S2 is not optional polish.
- **The real silent-inert channel is import SCOPE, not init order.** The
  draft's "registration timing" risk described a mechanism that does not
  apply. Under any of A/B/C, the module that *calls* `fuzz(...)` must itself
  opt in; `import nelli/concolic` in some *other* module of the same binary
  silently yields a nil bridge, the campaign runs clean, and the suite passes.
  Under (A) this is lexical and checkable; under (B) it is a compile error;
  under (C) it is a runtime ordering rule — the weakest of the three. Note
  the house pattern compiles per-file test binaries (`dt-bounded.sh`), so a
  test file can silently lose concolic that the app binary has.
- **Silent-skip is a NEW failure mode, not "today's default behavior."** The
  draft asserted otherwise. Today the macro wires the bridge
  *unconditionally*, so `stallRounds > 0` always gets a live solve
  (`tfuzzconcolicbridge_real` exists to prove it). Post-change, that same user
  upgrades and gets a silent no-op at `fuzz.nim:1595` — an explicitly
  requested feature doing nothing, indistinguishable from success. That
  combination **cannot occur today**.
- **Threads / gcsafe (mechanism C only).** Every leg compiles `--threads:on`
  (`dt-bounded.sh:37`, `symex-windows.yaml:164`). A module-level `var` of
  *closure* type read from a gcsafe-inferred context is a compile error
  waiting for its first caller. If C is chosen, the hook must be a
  `{.nimcall.}` proc pointer (the registrant wraps a top-level proc; no
  captured state), write-once at module init, with `doAssert` on conflicting
  re-registration — "last-wins silently" is the wrong default. Bounded today:
  fuzz workers are separate processes (`fuzzworker.nim`) that re-run module
  init, and `parallel.nim`'s real threads serve stateful testing, not fuzz —
  so `tryConcolicBridge` runs only on the orchestrator thread. But the RFC
  must *state* the invariant, since the in-tree `nelliWorkerRegistry`
  (`fuzzmacro.nim:82`) shows the pattern gets copied without it.

## Required diagnostic surface

Silence is the wrong answer for the affected cohort. S1b must ship a loud
surface for `stallRounds > 0` ∧ frontier stalled ∧ no solver:

- a one-shot campaign warning naming the fix ("concolic assist requested via
  `stallRounds > 0` but no solver is available — add `import nelli/concolic`
  to this module"), and/or
- a distinct `ConcolicYield` arm ("no solver available") so a campaign can see
  the misconfiguration in `report.stats` rather than inferring it from zeros.

This touches `concolictaxonomy` enums, so it belongs in S1a/S1b scope, not
"later."

**Negative control (S1b DoD).** Plain `import nelli`, no concolic import,
`GuidanceConfig(stallRounds: 1)`, same gate:

    check report.iterations == 60          # campaign completes, no exception
    check report.coverageHits == 1         # gate never broken
    check report.stats.concolicYield.solvedExact +
          report.stats.concolicYield.solvedOptimistic == 0
    check report.stats.provenanceCounts[pvConcolic] == 0

The existing "negative" test (`tfuzzconcolicbridge_real.nim:38-41`) is on the
**wrong axis** — it tests `stallRounds = 0` with the bridge *present*. The new
axis (`stallRounds > 0`, bridge *absent*) does not exist today and cannot,
since the macro wires the bridge unconditionally.

## Runtime error surface — missing libz3

`import nelli/concolic` on a machine with no libz3: softlink lazy-loads, so
failure surfaces as a `SoftlinkError` at the *first solve, mid-campaign, inside
`tryConcolicBridge`*. S1c must assert the behavior — recommended: catch,
degrade to mutation-only, reuse the diagnostic surface above; do **not** abort
the campaign. Fold into the existing z3-error taxonomy
(`tsymex_phase14_c4_z3error`). S4 documents it.

## Consumer build matrix

`nelli.nimble` declares **zero** dependencies (`requires "nim >= 2.0.0"` only);
z3 + softlink arrive via `milpa.kdl` → the generated root `nim.cfg` `--path`
lines. So:

| Channel | core-only today | core-only after | +concolic |
|---|---|---|---|
| milpa | deps fetched, `--path` set, z3 compiled in | deps still fetched; win is compile time, no `--cincludes`, no runtime libz3 | unchanged |
| nimble / bare `--path` | **`import nelli` fails to compile** (the captured RED) | works | needs z3 on the path |

Two things the draft never said: the milpa manifest is expected **unchanged**
(`nelli/symex` stays in-package, so the dep stays), and the nimble/bare-path
row is a **genuinely new capability** this work creates — it should be claimed
and tested, not left implicit.

## Breaking change

Dropping `export symex` from `fuzzmacro` removes symex's **entire** surface
from `import nelli` — `z3FullVersion`, `symexFind*`, `symexForAll`,
`assertCoveredBy`, `concolicCollect`, `symexOpaque`, and the marker templates
`symexTarget`/`symexAssert`/`symexAssume` (`symex.nim:1085-1100`). Those
markers are *designed* to sit in SUTs run under plain PBT, so a consumer who
reached them via `import nelli` breaks.

In-tree blast radius is smaller than feared but non-zero: of the tests with a
bare `import nelli`, 9 use symex symbols, and every one except
`tfuzzconcolicbridge_real` also imports `nelli/symex` directly. Downstream
(chapulin on Windows, amoxtli) must be audited. S1d's DoD is full
`nimble test` green; S5 owns the version bump and migration note.

**Open question for S4/S5:** should the three marker templates move to a
Z3-free leaf so marker-bearing SUTs stay importable from `import nelli` alone?
Recommend yes — they are no-ops outside symex by construction.

## Non-goals

- No `-d:nelliConcolic` compile flag. Too coarse — whole-compilation switch,
  bifurcates macro codegen, cannot vary per call site. (Note this same
  objection indicts mechanism (C); see §Mechanism.)
- Not making Z3 optional for `nelli/symex` itself — that module *is* the
  walker; a consumer importing it is asking for Z3 by definition.
- ~~No change to `fuzz(...)`'s public signature or default runtime behavior.~~
  **Retired in round 1.** Default *runtime* behavior is preserved under all
  three mechanisms, but this work necessarily changes what `import nelli`
  exports (see §Breaking change), and mechanism (B) would add a
  `GuidanceConfig` field. The non-goal as written would have ruled out (B)
  by fiat rather than on merit.

## Alternatives considered

- **`when declared(...)` caller-scope gating** — now mechanism (A); the draft
  never enumerated it.
- **Split symex into its own package.** The only option that removes z3 at the
  *manifest* level. Rejected for now: symex is co-developed in lockstep with
  core (`symexWalkerVersion` bumps pin core tests), so a package boundary
  would add release friction for no additional runtime benefit. Worth
  revisiting if the lockstep coupling ever relaxes.
- **A `nelli/core` split** — subsumed by the inversion; the umbrella stays
  whole and only the concolic edge moves.
- **`-d:nelliConcolic`** — see Non-goals.
