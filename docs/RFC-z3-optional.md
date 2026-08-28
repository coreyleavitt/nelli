# RFC — make `import nelli` Z3-free by inverting the concolic bridge

**Issue:** #160 · **Branch:** `rfc-z3-optional` (off `main` at v0.6.0, `1f50752`)
**Status:** stage 2 (architect) — round 1 applied, mechanism resolved (design D,
spike-proven) · **READY for `/tdd`**

## §0 — Thesis

`import nelli` forces every downstream consumer to resolve Z3 at compile time,
to serve a capability that is **runtime-off by default**. A consumer using only
`property`/`StateMachine`/`forAll` — or `fuzz(...)` without concolic assist —
pays the heaviest native dependency in the tree for code it never executes.

Invert it: the core keeps a bridge that is absent by default, and the
walker-touching implementation moves to an opt-in module. `import nelli` stops
reaching Z3; `import nelli/concolic` restores today's behavior.

*(Round 1: the draft said "a nil-defaultable bridge hook … an opt-in module
that registers into that hook." That mechanism is unbuildable — `concolicFlip`
is a macro, not a proc. The thesis survives; the instrument changed. The seam
we need already exists — see §The crux and §Mechanism.)*

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
> not. All five review lenses refuted this independently against source.
> The corrected analysis follows; it is retained because it is what rules out
> the hook/registry family and motivates §Mechanism's design D.

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

- `tryConcolicBridge` really is inert by default (`fuzz.nim:1595-1596`;
  `stallRounds = 0` default at `:1009`).
- `smt/concolictaxonomy.nim` is genuinely Z3-free (its only `z3` hit is a doc
  comment at `:9`) and `fuzz.nim` really does stay Z3-free by importing it.
  This is what makes `ConcolicBridgeEntry` a Z3-free seam — the fact design D
  builds on.

### The type move the draft proposed is NOT needed

The draft would have moved four binding types (plus, per round 1, the enum
values `cbDrawLinked`/`ccoEq`… and three static defaults in the Z3-importing
`smt/runtime.nim:12763,13005,13011`) into a Z3-free leaf so **core** could keep
constructing bindings.

Under design D core constructs nothing, so none of it moves. Those symbols are
needed only where the bridge is *built* — `nelli/concolic`, which imports
symex anyway. Recorded because it is a real trap: the round-1 review correctly
found the draft's inventory incomplete, and the right response turned out to be
deleting the requirement rather than completing the list.

### Mechanism — RESOLVED: design D, "stop auto-wiring the seam"

**The reframe.** This was never a dependency-inversion problem. The correct
Z3-free seam **already exists and is already proven**:

    proc fuzz*[T](s: Strategy[T]; target: Target[T]; frontier: var CoverageFrontier;
                  settings: FuzzSettings; concolicBridge: ConcolicBridgeEntry = nil;
                  ...): FuzzReport                                  # fuzz.nim:1797

    ConcolicBridgeEntry* = proc(trace: seq[ChoiceNode];
                                targetBranchIndex: int): ConcolicBridgeResult {.closure.}

Explicit, nil-defaulted, per-call-site, expressed entirely in Z3-free types,
and exercised today with fake bridges at nine call sites in
`tfuzzconcolicbridge.nim` — with no Z3 anywhere.

So there is no missing abstraction. v0.6.0's G3 C4 introduced a **regression in
a default**: `fuzzmacro` began *auto-populating* that parameter for every
caller, and to do so had to `import ./symex`. That one convenience — wiring a
bridge nobody asked for — is the entire reason `import nelli` reaches Z3.

**The fix is to stop auto-wiring it, and move construction to the opt-in
module.**

    # core: fuzzmacro imports no symex, builds no bridge, gains a pass-through
    macro fuzz*(stratExpr, propExpr, settingsExpr, assist: typed): untyped

    # nelli/concolic — the sole walker importer
    macro concolicAssist*(prop, strat: typed): ConcolicBridgeEntry

    # caller
    import nelli
    import nelli/concolic
    fuzz(integers(0, 0xFFFFFFFF), magicGate,
         FuzzSettings(guidance: GuidanceConfig(stallRounds: 1)),
         assist = concolicAssist(magicGate, integers(0, 0xFFFFFFFF)))

plus one sugar in the opt-in module, built **on** the primitive rather than
replacing it:

    template fuzzConcolic*(s, p, settings): FuzzReport =
      fuzz(s, p, settings, assist = concolicAssist(p, s))

### Why D dominates the alternatives

| | **D** | A (`when declared`) | B (`GuidanceConfig.solver`) | C (registry) |
|---|---|---|---|---|
| New abstractions | **none** | marker symbol | solver type + frontend split | hook type + global |
| Core pulls symex | **zero** | zero | ~12k lines frontend | ~12k lines |
| Global mutable state | **no** | no | no | yes |
| Opt-in visible at call site | **yes** | no (module-granular) | yes | no |
| Forgetting the import | **compile error** | silent no-op | compile error | silent no-op |
| Varies per call site | **yes** | yes | yes | **no** |
| gcsafe / init-order / thread risk | **none** | none | none | yes |

(C) is additionally indicted by the Non-goals' own reason for rejecting
`-d:nelliConcolic`: a process-global cannot vary per call site either.

### What D deletes from this RFC

- **The type move (old S1a) is unnecessary.** The four binding types, the enum
  values (`cbDrawLinked`, `ccoEq`…), and the three static defaults are needed
  only where the bridge is *built* — now `nelli/concolic`, which imports symex
  anyway. The whole "inventory gaps" problem evaporates.
- No hook type, no registrar, no registration semantics, no `{.nimcall.}`
  /gcsafe specification, no init-order rule.
- **The entire silent-inert risk class disappears** — you cannot forget the
  import, because `concolicAssist` will not resolve.
- `tfuzzconcolicbridge.nim` passes **unchanged** — it already supplies bridges
  explicitly. Only `tfuzzconcolicbridge_real.nim` changes.

### Spike results (2026-08-28, `localhost/nelli-dev:latest`)

Both unknowns closed **green** before slicing. Isolation spike in
`scratchpad/z3spike/` (four modules mirroring the core/walker/consumer split):

| Question | Result |
|---|---|
| Does `concolicAssist(prop)` semcheck in the **caller's** scope and splice into core's `quote do`? | **Yes**, positional and named |
| Do 2-/3-/4-arg `fuzz` overloads coexist? | **Yes**, arity resolution clean |
| Core-only consumer with walker unreachable | Compiles; `assist=NONE` (default behavior preserved) |
| `fuzzConcolic` sugar over the primitive | Works |

The AST capture is *proven*, not assumed: a 2-branch property returned
`branchCount = 2` and a 1-branch property `1`, so the compile-time walk really
consumed the property body in the consumer's module.

**Implementation note (spike-discovered).** The named-argument form
`assist = ...` requires the macro parameter to be literally named `assist`;
naming it `assistExpr` fails with *"unknown named parameter: assist"*.

**Real-tree proof of half (1).** With `import ./symex`/`export symex` dropped,
both bridge arms nil'd, and `classifyStrategyExpr`/`bindingExprFor` removed,
`tests/tz3free_probe.nim` **compiles and runs Z3-free**: `z3-free probe OK`.
The patch was experimental and reverted; it establishes the property is
reachable exactly as D describes.

**Refinement the spike surfaced.** `classifyStrategyExpr` and `bindingExprFor`
(`fuzzmacro.nim:526-643`) reference `ccoEq`/`ConcolicConjunctOp` from the
**Z3-importing** `smt/runtime.nim`, and are called from exactly one site
(`:796`, the bridge build). They must move to `nelli/concolic` **with** the
bridge — which is why `concolicAssist` takes the *strategy* expression as well
as the property: binding classification needs it. Without this, the probe fails
at `fuzzmacro.nim(628): undeclared identifier: 'ccoEq'` (observed).

## Load-bearing property

> **A module that does `import nelli` compiles with no Z3 on the path, and
> adding `import nelli/concolic` restores end-to-end concolic solving.**

Both halves, or it has not landed. The first half alone is achievable by
deleting the feature; the second half is what proves the seam rather than a
removal. **S1b produces both** (S1a is a pure relocation prerequisite, and
S1b also ships the negative control that makes half (2) falsifiable).

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

The draft's single S1 was a round mislabeled as a slice — 7-8 modules across a
compile-time/runtime seam. **Design D shrinks it to three files**, because the
type move, the hook, and the registrar all evaporate. Sliced:

- **S1a — move the bridge builder to the opt-in module.** Create
  `src/nelli/concolic.nim`: `import ./symex; export symex`, plus
  `classifyStrategyExpr`/`bindingExprFor` (moved verbatim from
  `fuzzmacro.nim:526-643`) and a new `concolicAssist(prop, strat)` macro
  holding today's bridge-construction logic from `fuzzmacro.nim:797-823`.
  Core still auto-wires at this point — **pure relocation, zero behavior
  change**. **DoD:** full `nimble test` green, `tfuzzconcolicbridge_real`
  untouched and passing.

- **S1b — add the pass-through, stop auto-wiring (produces the property).**
  `fuzzmacro` gains the 4-arg overload with a parameter literally named
  `assist` (see the spike note), drops `import ./symex`/`export symex`, and
  builds no bridge. `tfuzzconcolicbridge_real.nim` adds
  `import nelli/concolic` and the `assist =` argument. **Both halves land
  here, which is the point:**
  1. `tests/tz3free_probe.nim` compiles Z3-free (spike-proven reachable);
  2. the gate test below stays green through the real entry point.

  **DoD:** the test *"stalled campaign with the real bridge wired
  (stallRounds > 0) breaks the 0xCAFEBABE gate"* passes with its
  positive-signal checks intact:

      check report.coverageHits == 2
      check report.stats.concolicYield.solvedExact +
            report.stats.concolicYield.solvedOptimistic > 0
      check report.stats.provenanceCounts[pvConcolic] > 0

  Note this test **cannot pass "unchanged"** — its header (`:9-11`) documents
  "deliberately just `import nelli` … still gets it for free" as its whole
  point. S1b inverts that contract: the import, the `assist` argument, *and*
  the docstring change.

  Plus the negative control (below) and full `nimble test` green.

- **S1c — ergonomics.** Add the `fuzzConcolic(s, p, settings)` sugar to
  `nelli/concolic`, built on `concolicAssist` rather than replacing it, so the
  common case names the property once. Spike-verified. Small and separable —
  merge into S1b only if the diff stays small.

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

No slice ships a consumer without its producer. Design D makes this nearly
automatic: S1a relocates the producer with core still wired (behavior
unchanged), and S1b flips core off and the call site on **in the same slice**,
so the property never sits half-built. There is no intermediate state where a
bridge-shaped hole exists with nothing to fill it.

## Risks

- **Macro hygiene at the splice site.** Generated code resolves identifiers in
  the *caller's* scope. `fuzzmacro.nim:53-64` records a real prior footgun.
  Largely retired by the spike (expression-level substitution across a
  `quote do` boundary is the documented-safe class, and the spike exercised
  exactly that), but S1b must still prove it with a macro-call-site test in
  the real tree, not a unit test.
- **Silent regression.** Without S2, any future `import` in the wrong module
  reintroduces the dependency invisibly. S2 is not optional polish.
- **Silent degradation on upgrade — the one risk D does *not* delete.** Today
  the macro wires the bridge *unconditionally*, so `stallRounds > 0` always
  gets a live solve (`tfuzzconcolicbridge_real` exists to prove it). After
  S1b, that user upgrades, their call site still compiles, and they get a
  silent no-op at `fuzz.nim:1595` — an explicitly requested feature doing
  nothing, indistinguishable from success. This combination **cannot occur
  today**, so it is a *new* failure mode, not "today's default behavior" as
  the draft claimed. See §Required diagnostic surface — this is the reason
  that section is mandatory rather than polish.
- **What D *does* delete.** Import-scope inertness (you cannot forget the
  import — `concolicAssist` will not resolve); registration timing;
  double-registration semantics; `{.nimcall.}`/gcsafe constraints on a global
  under `--threads:on`; and per-binary divergence under `dt-bounded.sh`'s
  per-file test binaries. None of these risks survive design D, which is most
  of the argument for it.

## Required diagnostic surface

Silence is the wrong answer for the one cohort D cannot protect at compile
time: an existing user upgrading, whose `stallRounds > 0` call site still
compiles but no longer solves. S1b must ship a loud surface for
`stallRounds > 0` ∧ frontier stalled ∧ nil bridge:

- a one-shot campaign warning naming the fix ("concolic assist requested via
  `stallRounds > 0` but no assist was supplied — pass
  `assist = concolicAssist(prop, strat)` from `nelli/concolic`"), and/or
- a distinct `ConcolicYield` arm ("no assist supplied") so a campaign can see
  the misconfiguration in `report.stats` rather than inferring it from zeros.

This touches `concolictaxonomy` enums, so it belongs in S1b's scope, not
"later." It is also what makes the negative control below assert something
positive rather than merely observing zeros.

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
`tryConcolicBridge`*. S1b must assert the behavior — recommended: catch,
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
  objection also indicted the draft's registry — see §Mechanism.)
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
