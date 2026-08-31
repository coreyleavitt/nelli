# RFC — make `import nelli` Z3-free by inverting the concolic bridge

**Issue:** #160 · **Branch:** `rfc-z3-optional` (off `main` at v0.6.0, `1f50752`)

- **Status:** Implemented — **shipped v0.7.0**, tagged `dc9e90a` 2026-08-29
  and published as a signed OCI artifact. All seven slices landed; mechanism
  resolved (design D + round-2 `ConcolicAssist` refinement); §Round-3 spike
  gate CLOSED green, adopting `assist: untyped` plus the syntactic rewrite.
  Stage-4 review ran **to its floor**: 13 findings (1 High, 7 Medium, 5 Low)
  all closed across a fix round and a re-review round, verified on Linux and
  on all three Windows legs. Ledger in the handoff.
- Category: packaging
- **Depends on:**
  - RFC-0003 (fuzzer-nextgen) — this repairs the G3 C4 auto-wiring that
    v0.6.0 introduced, which is what made `import nelli` reach Z3.

  (Refs must sit on lines *below* the "Depends on" header, not on it:
  quipu's `_extract_depends_block` starts scanning after that line, so a
  single-line `Depends on: RFC-0003` parses to an empty block and silently
  produces no graph edge.)

See `docs/rfc/0004-z3-optional.handoff.md` for build progress, the round-3
spike closure record, and the review ledger.

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

**`tests/tsmoke.nim` is RED on this tree right now** (round-2 discovery, run
and confirmed, not inferred):

    [FAILED] internal modules are not bulk-re-exported through nelli
    /work/tests/tsmoke.nim(32, 10): Check failed:
      not compiles(integerChoice(1, 0, 10, 0))   -- was true

`fuzzmacro.nim:51 export symex` → `symex.nim:25 export choice` leaks choice's
whole constructor surface into bare `import nelli`, breaking a public-surface
contract test that predates this work. It went unnoticed because **no workflow
runs `nimble test` at all** — the tree says so itself at
`symex-windows.yaml:64-68` ("this repository currently has no CI workflow that
runs the `test` task"); the fuzzer legs glob `^(tfuzz|tdb|tengine_)` and the
symex leg derives `tsymex_*` only. Three consequences:

1. A **third** independent piece of evidence for the regression framing, and
   the strongest one — a machine-checkable contract, not prose.
2. **An existing, achievable RED.** Deleted S3 was dropped for having none;
   `tsmoke` is one, and the flip slice turns it green. Claim it in the DoD.
3. Every DoD in this RFC that says "full `nimble test` green" is **currently
   unsatisfiable**. See §Slices for the corrected wording.

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

### Round-2 refinement: reify the assist, delete the second key

The pre-round-2 shape passed a bare `ConcolicBridgeEntry` and kept
`GuidanceConfig.stallRounds` as a separate intent knob. That split is a
**fossil of auto-wiring**: when the macro wired a bridge for everyone, bridge
presence carried no user intent, so a second knob had to. Under D,
`assist = ...` *is* the per-call-site request, and requiring a second nested
`GuidanceConfig(stallRounds: 1)` creates a two-key activation whose either-key
omission is a silent no-op. The RFC's own headline sugar was inert at its own
defaults: `fuzzConcolic(s, p, FuzzSettings())` would link Z3, build a bridge,
and never fire.

Verified sole-consumer chain (round 2, checked against source):
`GuidanceConfig.stallRounds` (`fuzz.nim:192`) and `concolicMaxBranchAttempts`
(`:200`) are read at exactly one place — the mapping into `OrchestratorPolicy`
at `:1868-1870` — and that policy is read at exactly one place,
`tryConcolicBridge`'s gate (`:1595-1597`). `stalled()` (`coverage.nim:764`) has
exactly one call site, `:1596`. Both fields are dead weight without a bridge,
and `INTERFACE.md:169` already documents `stallRounds` in terms of the concolic
bridge. So they belong **on the assist**, not in guidance.

    # fuzz.nim — Z3-free, replaces the bare `concolicBridge` parameter
    type ConcolicAssist* = object
      bridge*:            ConcolicBridgeEntry  ## nil ⇒ no assist (zero value)
      stallRounds*:       int                  ## activation policy travels
      maxBranchAttempts*: int                  ## WITH the assist

    proc fuzz*[T](s: Strategy[T]; target: Target[T]; frontier: var CoverageFrontier;
                  settings: FuzzSettings;
                  assist: ConcolicAssist = ConcolicAssist();
                  spawnFreshWorker: SpawnFreshWorker[T] = nil): FuzzReport

    # core: fuzzmacro imports no symex, builds no bridge, gains a pass-through
    macro fuzz*(stratExpr, propExpr, settingsExpr: typed; assist: untyped): untyped

    # nelli/concolic — the sole walker importer
    macro concolicAssist*(strat, prop: typed;
                          stallRounds = 1;
                          maxBranchAttempts = 8): ConcolicAssist

    # nelli/concolic — the HEADLINE consumer surface (see below)
    template fuzzConcolic*(s, p: untyped; settings: untyped = FuzzSettings();
                           stallRounds = 1; maxBranchAttempts = 8): FuzzReport =
      fuzz(s, p, settings,
           assist = concolicAssist(s, p, stallRounds, maxBranchAttempts))

    # caller
    import nelli
    import nelli/concolic
    fuzzConcolic(integers(0, 0xFFFFFFFF), magicGate)

**Resolution rule (must be specified, not left implicit):** a non-nil
`assist.bridge` with `stallRounds <= 0` resolves to the default `1` at the
mapping site rather than being inert. Assist present ⇒ assist active. The
no-op is unrepresentable through this path, not merely diagnosed.

**Raw-construction contract (round 3).** The rule above covers the macro
path, where `concolicAssist` always emits `stallRounds >= 1`. Direct
`ConcolicAssist(...)` literals — the advanced path, all three fields being
exported — admit two edge states the macro never sees, and each gets a
specified treatment rather than an accident:

- **`bridge: nil` with `stallRounds > 0`** — a policy with no bridge, the
  mirror image of `processIsolation: true` without `spawnFreshWorker`.
  Treated the way the tree already treats that case (`ProcessIsolationError`,
  `fuzz.nim:629-638`, raised at `:1833` before the campaign starts): raise
  `ConcolicAssistError` at campaign start, naming `concolicAssist` as the
  fix. Coercing here would silently run an assist-less campaign the caller
  explicitly configured for assist — the original bug through a different
  field.
- **non-nil `bridge` with an *explicitly written* `stallRounds: 0`** —
  coerced to `1` by the rule above. This deliberately departs from the
  raise convention because there is no failure mode to report, only intent
  inference: "bridge present but disabled" is not a state this API spells
  with a contradictory record — it is spelled by *not passing the assist*.
  A caller threading external config resolves "off" to `ConcolicAssist()`
  (the zero value), not to a bridge-bearing record with a zeroed knob.

What this buys, all verified against the tree:

- The **converse** misconfiguration (assist supplied, `stallRounds` left at 0)
  — undiagnosed anywhere in the pre-round-2 RFC, and the *easy* mistake under
  D — becomes unrepresentable on the macro path, and raises or coerces per
  the raw-construction contract above on the literal path. The one surface
  neither covers is the raw `newOrchestrator` seam, which keeps
  `concolicBridge` and `OrchestratorPolicy.stallRounds` as independent
  knobs — **deliberately**: it is the internal seam, and
  `tfuzzconcolicbridge.nim:23-32` pins "bridge configured, `stallRounds` 0 ⇒
  inert" as that seam's *contract*, not a bug.
- §Required diagnostic surface **evaporates**: no taxonomy arm, no gate split,
  no one-shot warning flag, no report plumbing. The flip slice gets smaller.
- §Risks' "the one risk D does *not* delete" — the upgrader whose
  `stallRounds: 1` call site still compiles and silently no-ops — **is
  deleted**. With the field gone, `GuidanceConfig(stallRounds: 1)` is a
  *compile error naming the missing field*, which is a strictly better
  diagnostic than any runtime warning.

Cost, stated honestly: `tfuzzconcolicbridge.nim` no longer passes wholly
unchanged. Its **seven orchestrator-level sites** (`:32,47,67,92,108,136,181`,
which use `newOrchestrator(concolicBridge = ...)` + `orchestratorPolicy(...)`)
are untouched — `OrchestratorPolicy` keeps both fields as the internal knobs.
Its **three loop-level sites** (`:227`, `:247`, plus
`tfuzzcampaignstats.nim:183`) migrate to a `ConcolicAssist` value, which is
strictly nicer than today's closure-plus-settings split. `tfuzzconfigdefaults.nim:40-41`
drops two checks (`:71-72`, the `OrchestratorPolicy` defaults, stay).
0.7.0 is already breaking, so there is no compatibility argument for keeping
the fields — and chapulin has **not yet absorbed** v0.6.0's `FuzzSettings`
regroup, so folding this in means downstream migrates **once**, not twice.

`newOrchestrator`'s low-level `concolicBridge` + `policy` pair (`fuzz.nim:1160,1194`;
`INTERFACE.md:232`) stays as-is — it is the raw seam and is already explicit
about both halves. A caller there writes
`concolicBridge = concolicAssist(s, p).bridge`.

### The coherence invariant (new failure mode — name it)

The 4-arg primitive makes `fuzz(sA, pA, settings, assist = concolicAssist(sB, pB))`
expressible for the first time, and the macro **cannot** cross-check: by the
time `assist: typed` arrives, `concolicAssist` has already expanded and the
original call node is gone. On mismatch the classifier builds bindings from
the wrong strategy chain and Z3 solves the wrong equation.

Damage is **bounded, not unsound** — the re-verification gate at
`fuzz.nim:1607-1616` rejects seeds that don't reproduce (`caoRejectedAtReplay`),
so a mismatch degrades to silent yield-poisoning rather than a false pass. But
silent yield-poisoning is exactly the ambiguity class G6 exists to kill.

*(Corrected during build, measured — not this RFC's conclusion, only its
cited mechanism: mismatched seeds are valid draws for the campaign's own
strategy, so they replay **cleanly** and `caoRejectedAtReplay` is 0. They are
turned away one layer later, by `admit`'s interestingness fold, as
`caoSupersededByRace`. "Bounded, not unsound" holds and is better supported
by the measurement — the cost is exactly the wasted solver work, not a false
pass. Pinned in `tests/tfuzzconcolicmismatch.nim`; see the handoff's §RFC
corrections for the numbers.)*

Therefore: **`fuzzConcolic` is the headline and the documented default form**,
because it enforces the invariant syntactically — `s` and `p` are named once
and generated twice. The 4-arg `fuzz` + `concolicAssist` pair is the
documented *advanced* compositional seam. This is not a style preference; it
is what makes the common path correct by construction, and it is why the sugar
ships **with** the flip rather than a slice later.

Ergonomics evidence: `tfuzzconcolicbridge_g6_affine.nim:29`'s strategy is
`integers(0, 1000).map(proc(x: int): int = x * 2 + 1)`. Under the primitive
that expression is written twice at one call site. Under the sugar, once.

**Round 3: the invariant may be enforceable at the primitive itself.** The
"cannot cross-check" above is a consequence of declaring `assist: typed` —
full semcheck expands `concolicAssist` before `fuzzMacroImpl` ever sees it.
With `assist: untyped`, the macro receives the raw call syntax and can
rewrite a syntactic `concolicAssist(...)` in place, splicing its own
already-typed `stratExpr`/`propExpr` copies into the assist call's first two
positions before final typechecking — making divergence unrepresentable for
the written-inline form, the only form the sugar doesn't already cover. This
is strictly better if it works, and it was **not** spiked: the round-2
arity-collision closure tested an all-`typed` shape, and `untyped`-bearing
overloads resolve differently. See §Round-3 spike gate; adopt on green, keep
`typed` on red. Under both outcomes a pre-built `ConcolicAssist` *variable*
passes through unchecked, so the mismatch control in S1b1's DoD is required
regardless.

**Gate outcome: GREEN, adopted.** The rewrite works, proven behaviorally
(§Round-3 spike gate's closure note): an inline assist written against a
deliberately different strategy/property pair still had its mismatch
corrected, not merely tolerated. The coherence invariant is therefore
enforced at the primitive for the written-inline form. The shipped
signature is `assist: untyped` (`src/nelli/fuzzmacro.nim:605`).

Two notes the implementer needs:

- **Argument order is `(strat, prop)` everywhere**, matching `fuzz`. The
  pre-round-2 text had `concolicAssist(prop, strat)` against
  `fuzz(strat, prop, ...)`; a transposition across the two spellings *is* the
  coherence bug above with a worse error message.
- **`s`/`p` double-substitution in the sugar is compile-time only.**
  `concolicAssist` consumes both during classification and parse; the closure
  it generates evaluates neither. There is no runtime double evaluation. The
  one open case is an inline-lambda `prop`: `fuzz` lifts one copy via
  `liftPropIfNeeded` (`fuzzmacro.nim:674`) and `concolicAssist` would lift a
  second. Sound (same AST) but must be stated — specify that `concolicAssist`
  performs its own lift, so the walker walks a distinct-but-identical symbol.

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
- **The import-scope silent-inert risk disappears** — you cannot forget the
  import, because `concolicAssist` will not resolve. (The *configuration*
  silent-inert class is closed on the macro path and specified on the raw
  paths — see the raw-construction contract. Round 3: it is narrowed, not
  deleted; the pre-round-3 "entire class disappears" was an overclaim.)
- `tfuzzconcolicbridge.nim`'s **seven orchestrator-level sites** pass
  unchanged — they already supply bridges explicitly through
  `newOrchestrator`. Its three loop-level sites migrate to `ConcolicAssist`
  (see the round-2 refinement above).

### Correction (round 2): three tests change at the flip, not one

The pre-round-2 text claimed "only `tfuzzconcolicbridge_real.nim` changes."
**False**, and the two it missed are the load-bearing ones:

| Test | Why it breaks | Why it matters |
|---|---|---|
| `tfuzzconcolicbridge_real.nim` | bare `import nelli`, `stallRounds: 1`, macro `fuzz` | the 0xCAFEBABE gate |
| `tfuzzconcolicbridge_g6_affine.nim:16,29-31` | same shape — "Deliberately just `import nelli`" | **only** end-to-end pin of `cbTransformLinked` through `.map(x*2+1)` |
| `tfuzzconcolicbridge_g6_predicated.nim:9-10,21-25` | same shape | **only** end-to-end pin of the predicated `filter/map` chain |

The two g6 suites are the sole end-to-end coverage of
`classifyStrategyExpr`/`bindingExprFor` — *precisely the code S1a relocates*.
An implementer following the old text hits two unexplained REDs and may weaken
them instead of wiring the assist. They must be named in the DoD, migrated to
`fuzzConcolic`, and — while being touched — given the same positive-signal
checks `_real` already carries, which they currently lack.

### Closed spike unknowns (round 2)

The original spike proved macro-vs-macro arity resolution using a stand-in
named `fuzzImpl`, so it never tested the collision that actually exists in the
tree: **the new 4-arg all-`typed` macro against the runtime `proc fuzz*[T]`
(`fuzz.nim:1797`), which takes exactly 4 required parameters** and is called
with 4 positional args at many sites (`tfuzzloop.nim:19,48`,
`tfuzzcovcorpus.nim:150`, `tfuzzmacro.nim:24`, `tfuzzseedcov.nim:125`, …).
This is the tree's first same-name macro/proc arity overlap.

Closed **green** in round 2, independently by two reviewers, by patching a
dummy 4-arg macro into `fuzzmacro.nim` and compiling `tests/tfuzzloop.nim` in
`localhost/nelli-dev:latest`: clean compile, exit 0 (patch reverted). Nim
prefers the concrete proc — `var CoverageFrontier` + `FuzzSettings` are
stronger matches than `typed`. **Pin:** keep `tfuzzloop` and `tfuzzmacro` in
the flip slice's DoD as the resolution guard.

### Round-3 spike gate (before S1b1; S1a is NOT gated)

Round 3 found the committed spike closures do not cover the shape S1b1
actually builds — and `scratchpad/z3spike/` has since been deleted from
disk, so the old closures cannot even be re-run. One small rebuilt spike
(`scratchpad/z3spike2/`, throwaway) must close three questions before S1b1
starts:

1. **The two-argument `concolicAssist(strat, prop: typed; stallRounds = 1;
   maxBranchAttempts = 8)` shape.** The round-2 spike's `concolicAssist`
   took a *single* `typed` parameter. Two `typed` AST captures plus two
   defaulted plain parameters in one macro is a materially different shape
   (named vs positional calls; two captures spliced into one `quote do`).
   Never exercised.
2. **`assist: untyped` vs the macro/proc arity collision.** The round-2
   closure above proved Nim prefers the concrete `proc fuzz*[T]` over an
   all-`typed` 4-arg macro. `untyped`-bearing overloads are resolved
   differently (they can be tried in an earlier, non-typechecking pass);
   re-prove the pin with `assist: untyped` against the `tfuzzloop`/
   `tfuzzmacro` call shapes.
3. **Syntactic rewrite-and-resplice.** If (2) holds, prove the outer macro
   can rewrite an inline `concolicAssist(...)` node with its own typed
   strat/prop copies across the `quote do` boundary (§The coherence
   invariant, round-3 note).

**Decision rule:** (2) and (3) green ⇒ adopt `assist: untyped` with the
rewrite, and the coherence invariant is enforced at the primitive for
inline calls; either red ⇒ `assist: typed` stands and §The coherence
invariant applies as written. (1) must be green under whichever shape wins.
S1a is shape-independent (it introduces `concolicAssist` against the
*existing* `concolicBridge` proc parameter) and may start immediately.

**Gate CLOSED 2026-08-28 — all three green, `assist: untyped` + the rewrite
adopted.** Run in `localhost/nelli-dev:latest` (Q2 measured against the real
tree via an experimental 4-arg overload, added then reverted; Q3 in
`scratchpad/z3spike2/tspike_untyped.nim`, since deleted). (3) was proven
behaviorally, not just structurally: an inline `concolicAssist(...)` written
against a deliberately different `(strat, prop)` pair still had the outer
call's gate broken, i.e. the mismatch was corrected, not merely tolerated.
Full per-question results are in `docs/rfc/0004-z3-optional.handoff.md`
§Round-3 spike gate. Unchanged by the gate: a pre-built `ConcolicAssist`
*variable* still bypasses the rewrite entirely (it is not a syntactic
`concolicAssist(...)` node), so S1b1's mismatch control remains required —
see §The coherence invariant's build-time correction on that control's
result.

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
removal. **S1b1 produces both** (S1a is a pure relocation prerequisite, and
S1b1 also ships the negative control that makes half (2) falsifiable).

Half (2) must be proven by a **positive signal through the real entry point**,
not by a green suite. The discriminating assertion already exists in-tree,
verbatim at `tests/tfuzzconcolicbridge_real.nim:30-36` —
`concolicYield.solvedExact + solvedOptimistic > 0` and
`provenanceCounts[pvConcolic] > 0`, backed by `pvConcolic` (`fuzz.nim:439`) and
`ConcolicYield` (`concolictaxonomy.nim:199`), folded from real flip results at
`fuzz.nim:1604` and provenance-tagged admits at `:1611`. So S1b1 **re-points
existing discriminating assertions** at the new seam; it does not invent them.
See S1b1's DoD. Most Track-G tests do **not**
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

**Round-2 corrections to this section.**

- The probe is **already committed** (on this branch, in `8966402`). The
  handoff's "untracked → commit in the flip slice" is stale.
- It is registered **nowhere**: not in `nelli.nimble`'s explicit `task test`
  list (which is a hardcoded ~254-name array — *nothing* in this repo is
  auto-discovered by nimble), and in no workflow. Until S2 it is a dead file
  that no DoD compiles. State where it runs locally: `scripts/dt-bounded.sh`
  is the wrong tool (it adds the z3 path); the probe's runner is the podman
  invocation above, verbatim.
- The old text asked S2 to "confirm `scripts/derive-ci-suites.ps1` does not
  auto-pick the probe." **Wrong script.** That one serves
  `symex-windows.yaml` and restricts to `tsymex_*`, so it can never pick it
  up. The real auto-discovery surfaces are `fuzzer-windows.yaml:181-186` and
  its MSVC twin, globbing `t*.nim` filtered on `^(tfuzz|tdb|tengine_)`.
  `tz3free_probe` matches neither — correct outcome, and now a stated fact
  rather than an open task.
- **Corollary with teeth:** any *new* test file this RFC adds must be named
  `tfuzz*` to ride the existing CI glob. A negative-control file named
  anything else is invisible to CI, which is the same class of hole that let
  `tsmoke` sit red since v0.6.0.

## This is a regression fix, not a new feature

`README.md:91-95` **already documents the target state**:

> | Everything except symex | Nim ≥ 2.0.0, no external dependencies |
>
> "`import nelli` never touches Z3 — symbolic execution lives behind the
> separate `import nelli/symex`."

The v0.6.0 G3 C4 wiring silently broke that documented contract;
`fuzzmacro.nim:53-72` calls it an "accepted, already-anticipated consequence."
So this work restores a promise the README still makes — and, per round 2, one
the test suite still *asserts* (`tsmoke:32`, red since v0.6.0). The release
note is **Fixed** for the import surface, **Changed** for the
`GuidanceConfig` → `ConcolicAssist` move. (There is no CHANGELOG file; see S5.)

## Slices — producer first

Ordered so the load-bearing property runs end-to-end at S1b1; later slices
harden rather than complete it.

The draft's single S1 was a round mislabeled as a slice — 7-8 modules across a
compile-time/runtime seam. Design D shrank it, because the type move, the hook,
and the registrar all evaporate.

**Round 2 found the shrink was over-claimed.** The old S1b still spanned
compile-time macro surface, runtime orchestrator logic, a taxonomy enum, and an
error-handling policy — four concerns, ~4 src modules and 6 test files. It is
split below into **S1b1** (the flip, which produces the property) and **S1b2**
(missing-libz3 degradation, a separable policy). The old S1c is **folded into
S1b1**, not deferred: `fuzzConcolic` is what enforces the coherence invariant,
so shipping the primitive without it would land the correctness-relevant sugar
a slice late. (Round 3 reuses the freed S1c label for the marker relocation —
a different, independent slice.) Sliced:

**DoD wording — read this first.** "Full `nimble test` green" appears nowhere
below, because it is not satisfiable on the dev platform and never was: six
`tsymex_r6_*` suites hang forever on Linux/podman (pre-existing, green on
Windows CI), and `tsmoke` is red on arrival (above). Every DoD names **bounded
suites run via `scripts/dt-bounded.sh`**, with the full suite deferred to
Windows CI.

- **S1a — copy the bridge builder into the opt-in module.** Create
  `src/nelli/concolic.nim`. Core still auto-wires — **zero behavior
  change.**

  **Round-3 correction: this slice is a COPY, not a move.** "Relocate" was
  buildable only as prose. If the G6 cluster is *deleted* from `fuzzmacro`
  while core still auto-wires, `fuzzmacro` must `import ./concolic` to keep
  calling `classifyStrategyExpr` — and `concolic.nim` must import
  `fuzzmacro` for the shared helpers (below). Both edges at once is a
  circular import, **empirically confirmed in this repo's own files**
  (round 3, patch reverted):

      concolic.nim(5, 3) Error: undeclared identifier: 'countFormalParams'
      This might be caused by a recursive module dependency:
        fuzzmacro.nim imports concolic.nim
        concolic.nim imports fuzzmacro.nim

  So: S1a **duplicates** the cluster into `concolic.nim` and leaves
  `fuzzmacro`'s originals untouched and auto-wiring; S1b1 deletes the
  `fuzzmacro`-side copies in the same slice that removes auto-wiring, at
  which point `fuzzmacro` no longer needs to call into `concolic` at all.
  The invariant that makes this sound: **the `fuzzmacro → concolic` edge
  never exists in any tree state** — `concolic → fuzzmacro` (shared
  helpers) is the only direction, acyclic in every slice.

  **Corrected inventory (round 2 — the old `:526-643` range does not
  compile).** What is copied in S1a and deleted from `fuzzmacro` in S1b1:

  - the whole G6 cluster `fuzzmacro.nim:382-643`, not just `:526-643`. The
    seven private helpers at `:382-526` — `unwrapValueExpr`, `procShapeOf`,
    `affineOf`, `flipPredOp`, `negatePredOp`, `predOpOf`, `predicateOf` — are
    used nowhere else in fuzzmacro (verified), and `classifyStrategyExpr`/
    `bindingExprFor` do not compile without them;
  - **both** bridge-emission arms at `:799-823`, not one: the single-param
    (classifier) arm *and* the multi-param positional arm (`cbDrawLinked` per
    param). `concolicAssist` must reproduce the `paramCount` dispatch.

  `concolic.nim`'s import list, stated so it is not rediscovered:
  `std/macros`, `./symex` (+ `export symex`), `./fuzz` (for
  `ConcolicBridgeEntry`/`ConcolicBridgeResult` at `fuzz.nim:736-754`, **not**
  in symex — plus `ConcolicAssist`, which this slice *introduces* there,
  below), `./fuzzmacro` (shared helpers, below), and `./smt/transparency`
  (for `PredOp`/`PredicateSpec`/`BranchingCase`/`compose`).

  **`ConcolicAssist` is introduced by this slice, in `fuzz.nim`** — round 3
  found the RFC citing it as if pre-existing while it exists nowhere in the
  tree (zero grep hits), leaving no slice owning the definition. S1a adds
  the type only: additive, Z3-free, no signature change. The `fuzz` proc's
  `assist` parameter and the `GuidanceConfig` field removal remain S1b1's.
  `fuzz.nim` is therefore in S1a's blast radius — one additive type.

  **Shared-helper decision (must be made, not discovered):**
  `propFormalParams`/`countFormalParams`/`liftPropIfNeeded`
  (`fuzzmacro.nim:650-690`) are needed by *both* sides — `concolicAssist`
  needs them, and fuzzmacro still needs them post-flip for the worker entry.
  **Decision:** export them from `fuzzmacro`; `concolic.nim` imports
  `fuzzmacro`. This is the *only* direction that ever exists, and it is
  acyclic in every slice state — which is exactly why S1a must be a copy
  (adding the reverse edge to keep auto-wiring is what produced the circular
  import quoted above). Round 2 asserted "no cycle" on the strength of
  symex's closure not reaching `fuzz`/`fuzzmacro`; true, but it checked the
  wrong edge — the cycle came from the shared-helper decision itself.

  **`export symex` is hygiene-forced, not an API choice.** `concolicAssist`'s
  spliced output carries free identifiers (IR constructors, `IRExprKind`
  values like `iekStrLen`, `concolicFlip`) that must resolve in the *caller's*
  module — the contract `fuzzmacro.nim:52-60` already documents. Record this:
  a future "narrow the re-export" cleanup would break every caller at a
  distance.

  **RED for S1a** (a behavior-preserving copy has none by itself): add
  `tests/tfuzzconcolicassist.nim` — `import nelli` + `import nelli/concolic`.
  Two suites, both red today (`concolicAssist` undeclared), green at S1a's
  end:

  1. build the real assist with `concolicAssist(integers(...), magicGate)`
     and pass `concolicBridge = assist.bridge` to the **existing** runtime
     `fuzz` proc parameter (`fuzz.nim:1797` — unchanged until S1b1),
     asserting `solvedExact + solvedOptimistic > 0` and
     `provenanceCounts[pvConcolic] > 0`. Proves `concolicAssist` works
     *outside* fuzzmacro's codegen, which the still-auto-wired path never
     exercises.
  2. thread the same `assist.bridge` through the **raw orchestrator seam**:
     `newOrchestrator(..., policy = orchestratorPolicy(stallRounds = 1),
     concolicBridge = assist.bridge)`, same positive-signal pair. Round 3
     found this documented combination (§Round-2 refinement's
     "`concolicBridge = concolicAssist(s, p).bridge`") was otherwise tested
     **nowhere** — all seven orchestrator-level sites use hand-written
     fakes — so the raw seam would have shipped dark.

  Note the `tfuzz*` prefix — required for CI visibility. S1b1 migrates
  suite 1 to the `assist = ...` parameter; suite 2 is untouched by design
  (the raw seam keeps its shape).

  **DoD:** `tfuzzconcolicassist` green; `tfuzzconcolicbridge{,_real,_g6_affine,_g6_predicated}`
  green and **untouched**; add the new file to `nelli.nimble`'s `task test`
  list (nothing is auto-discovered).

- **S1b1 — the flip (produces the load-bearing property, both halves).**
  `fuzzmacro` gains the 4-arg overload with a parameter literally named
  `assist` (spike note), drops `import ./symex`/`export symex`, builds no
  bridge, and collapses the now-identical `paramCount` branches.
  `nelli/concolic` gains `fuzzConcolic`. `GuidanceConfig` loses `stallRounds`
  and `concolicMaxBranchAttempts`; `fuzz`'s runtime proc takes
  `assist: ConcolicAssist`. The three real-bridge tests migrate to
  `fuzzConcolic`.

  **Blast-radius tally (round 3 — say it out loud):** three src modules
  (`fuzz.nim`, `fuzzmacro.nim`, `concolic.nim`) with interdependent
  signature changes, and eleven test files (DoD below). By this process's
  own bar that is a round, not a slice. It stays one slice anyway,
  **deliberately**: the load-bearing property cannot land half-flipped —
  any split leaves either a bridge-shaped hole or a double migration of the
  same call sites — and eight of the eleven test files are one-line
  mechanical migrations. The tally is stated so the implementer prices it
  going in, not so it gets re-split.

  **Both halves land here, which is the point:**
  1. `tests/tz3free_probe.nim` compiles Z3-free (spike-proven reachable);
  2. the gate tests stay green through the real entry point.

  **DoD:**
  - probe compiles Z3-free under the §Verification channel invocation;
  - **`tsmoke` goes green** — the pre-existing RED this slice fixes;
  - the 0xCAFEBABE gate test passes with its positive-signal checks intact:

        check report.coverageHits == 2
        check report.stats.concolicYield.solvedExact +
              report.stats.concolicYield.solvedOptimistic > 0
        check report.stats.provenanceCounts[pvConcolic] > 0

  - both g6 suites green, migrated, **and upgraded** with the same two
    positive-signal checks;
  - `tfuzzloop` + `tfuzzmacro` green (the macro/proc arity pin);
  - the negative control (below);
  - migrated: `tfuzzconcolicbridge.nim:227,247`, `tfuzzcampaignstats.nim:183`,
    `tfuzzconfigdefaults.nim:40-41`, `tfuzzconcolicassist.nim` suite 1
    (`concolicBridge = assist.bridge` → `assist = ...`; suite 2 untouched),
    and `tfuzzconcolicbridge_real.nim`'s **second** suite (R1 uint64Gate,
    `:43-66` — it also constructs `GuidanceConfig(stallRounds: 1)` at `:61`
    and breaks identically; round 3 found it unnamed);
  - **the non-concolic blast radius of the arm-collapse** (round 3): both
    `paramCount` arms carry the Track-E
    `spawnFreshWorker = processIsolationSpawnWorker(...)` wiring
    (`fuzzmacro.nim:809,823`), whose only coverage lives outside every
    concolic test. Bounded-green required: `tfuzzprocessisolation`,
    `tfuzzworkerspawnfailshm`, `tfuzzcmplogprocess`, `tfuzzcmplogshm`,
    `tfuzzcmplogshmleak` (all POSIX-runnable via `dt-bounded.sh`);
    `tfuzzwinworker`/`tfuzzwinshm` are the Windows-CI backstop — the same
    mingw/MSVC split S2 uses for the probe. Dropping `spawnFreshWorker` in
    the collapse would otherwise reproduce exactly the "nobody runs it,
    nobody notices" mode this RFC diagnosed for `tsmoke`;
  - **the mismatch control** (round 3): one test constructing
    `fuzz(sA, pA, settings, assist = <assist built from sB, pB>)` targeting
    a different branch, asserting the campaign completes with no false admit
    and that rejections are attributable to the re-verify gate
    (`caoRejectedAtReplay`, `fuzz.nim:1607-1616`). Turns §The coherence
    invariant's "bounded, not unsound" from a cited line number into a
    pinned behavior; required under **both** spike-gate outcomes, since a
    pre-built assist variable bypasses any syntactic rewrite;
    **(as measured, `tests/tfuzzconcolicmismatch.nim` pins
    `caoSupersededByRace` instead — the mismatched seeds replay cleanly and
    are caught one layer later, by `admit`'s interestingness fold; "bounded,
    not unsound" still holds, better supported. See §The coherence
    invariant's build-time correction above.)**
  - **the probe's CI step lands in this same commit/PR**, not deferred to
    S2 (round 3): between the flip and a later S2 the Z3-free property
    would have zero regression protection — the exact window that let
    `tsmoke` sit red for a release. S2 retains the tsmoke pin, the MSVC
    twin-leg work, and the named-test guards.

  Note `tfuzzconcolicbridge_real` **cannot pass "unchanged"** — its header
  (`:9-11`) documents "deliberately just `import nelli` … still gets it for
  free" as its whole point. This slice inverts that contract: the import, the
  call form, *and* the docstring change. Same for both g6 headers (`:16`,
  `:9-10`).

  **Implementation trap:** a naive 4-arg `fuzzMacroImpl` that runs
  `validateCapture` over all four arguments will reject the assist expression
  (an expanded closure block). Validate strat/prop only.

  **Second trap (round 3):** `fuzz`'s loop body has its own gate at
  `fuzz.nim:2193` (`if concolicBridge != nil:`), independent of
  `tryConcolicBridge`'s conjunction at `:1595`. Under the rename it must key
  on **`assist.bridge != nil` only** — "helpfully" mirroring the resolution
  rule there by reading `assist.stallRounds` would consult the *unresolved*
  value and short-circuit the loop before the mapping-site resolution
  applies, silently reintroducing the exact no-op the rule exists to close.

- **S1b2 — missing-libz3 degradation.** Split out because it is a distinct
  policy (see §Runtime error surface, rewritten in round 2). Not a blocker
  for the property.

  **DoD (round 3 — previously absent, which reproduced by omission the
  defined-but-never-observed-to-fire class this RFC deletes elsewhere):**
  new `tests/tfuzzconcolicdegrade.nim` (`tfuzz*` prefix, CI-visible), using
  a fake bridge closure that raises a `SoftlinkError`-shaped exception —
  Z3-free by construction, which is what makes the DoD falsifiable at all
  (both CI containers ship libz3). Asserts, positively:
  - the campaign completes (`iterations == N`), no abort;
  - the new `cfoSolverUnavailable` outcome counter is `> 0` — the arm is
    *observed to fire*, not merely defined;
  - a call-count check on the fake bridge proving the once-per-campaign
    latch suppresses re-attempts (bridge invoked once despite
    `maxBranchAttempts = 8` and multiple stall rounds).

- **S1c — marker relocation (round 3; was §Breaking change's open question,
  now resolved and specified).** Move `symexTarget`/`symexAssert`/
  `symexAssume` plus the whole capture cluster (`SymexCaptureCtx`, the
  `{.threadvar.}` `symexCapture`, `symexCaptureBegin/End/Record` —
  `symex.nim:146-166`, all Z3-free) to a new `src/nelli/engine/markers.nim`,
  exported through `engine.nim` the same way it already exports
  `frame`/`eval`/`render`/`targeting`/`phases` (`engine.nim:36-48`), and
  re-exported by name from `symex.nim` exactly as it already does for
  `engineTypes` symbols (`symex.nim:174-176`) — both wiring patterns are in
  daily use, not new mechanisms. `engine/types.nim` was considered and
  rejected as the destination: it is the semantically pure type module and
  these are procs. Zero new lines in `nelli.nim` — the `engine` export
  chain is already public. Result: marker-bearing SUTs stay importable from
  bare `import nelli` across the 0.7.0 break. **RED:** a `tfuzz*`-prefixed
  test asserting the three markers resolve under bare `import nelli` with
  the walker unreachable, and that `symexTarget` records into an
  `assertCoveredBy` capture.

- **S2 — pin it in CI.** Add the probe step with the corrected flag set. Two
  round-2 corrections:

  - **Both fuzzer legs.** `fuzzer-windows.yaml` (mingw) and
    `fuzzer-msvc.yaml` are hand-synced twins — `fuzzer-msvc.yaml:190` carries
    the "keep this pattern identical" comment. Add to both, or state in-file
    why a compile-only probe is mingw-only.
  - **The half-(2) pin is coincidental — make it explicit.** Half (2) rides
    `tfuzzconcolicbridge_real` matching the `^(tfuzz|tdb|tengine_)` glob
    (`fuzzer-windows.yaml:183`, `fuzzer-msvc.yaml:220`). Both legs throw on
    *zero* discovered tests but not on a *missing named* test, so a rename or
    glob edit silently drops the pin. Add to both legs:

        if ($tests.BaseName -notcontains 'tfuzzconcolicbridge_real') {
          throw "half-(2) pin missing" }

    **As shipped: stronger than specified above.** By the time S2 wrote this
    assertion, three more tests pinned this seam — `tfuzzconcolicassist`
    (S1a), `tfuzzconcolicmismatch` (S1b1), `tfuzzconcolicdegrade` (S1b2) —
    so S2 guards all four by name via a `foreach`, not the single check
    sketched above:

        foreach ($required in @('tfuzzconcolicbridge_real', 'tfuzzconcolicassist',
                                'tfuzzconcolicmismatch', 'tfuzzconcolicdegrade')) {
          if ($tests.BaseName -notcontains $required) {
            throw "half-(2) pin missing: $required was not discovered. ..."
          }
        }

    See `fuzzer-windows.yaml:226-230`, `fuzzer-msvc.yaml:262-266`.

  - **Pin `tsmoke` too.** S1b1 turns it green; nothing keeps it that way. It
    went red at v0.6.0 and stayed red precisely because no leg runs it, and it
    does **not** match `^(tfuzz|tdb|tengine_)`. Turning a contract test green
    without pinning it just resets the same trap. Add it as a named step in
    both legs, alongside the probe — a named step rather than a glob
    extension, for the same reason the half-(2) pin above is explicit: the
    surface contract should not depend on filename luck.

  **S2 pins only half (1)** — the probe passes identically if `nelli/concolic`
  were deleted outright, the exact scenario "Both halves, or it has not
  landed" forbids. That is why the explicit pin above is not optional.

  **Scope note.** S2 pins the three tests this RFC touches; it does *not* take
  on the broader hole that the whole non-symex half of `nimble test` runs in no
  workflow (`symex-windows.yaml:64-68`). That is a real defect and a
  pre-existing one — worth its own issue, not this RFC's scope.

- **S3 — deleted.** Pre-verified green: `fuzzmacro.nim:49/:51` is the only
  `import ./symex` in `src/` outside `symex` itself; every other umbrella
  re-export (`fuzzworker`, `parallel`, `bmc`, `symbolic`, `mining`, `bisim`,
  `mutation`, `laws`, `metamorphic`, `jsonschema`, `engine/*`) reaches neither
  z3 nor symex (`engine/types.nim:198` and `coverage.nim:95` document the
  deliberate avoidance). S3 had no achievable RED, and the probe compiles the
  entire `import nelli` closure anyway — a second route would already fail it.
  Its residual value *is* S2.

  **Round-2 amendment:** S3's premise was wrong in one respect — an achievable
  RED *did* exist all along, `tsmoke`. It is now claimed by S1b1's DoD, so S3
  stays deleted but its value is S2 **plus** the `tsmoke` pin.

- **S4 — consumer-facing docs.** `docs/fuzz/USAGE.md` + README: concolic
  assist needs one extra import, and why; `fuzzConcolic` presented as the
  default form and the 4-arg primitive as the advanced seam. Include the
  consumer build matrix and the missing-libz3 runtime behavior (below).

  **Round-2 addition: `docs/fuzz/INTERFACE.md` is normative** (its contract is
  pinned by `tests/tfuzzpackaging.nim`) and goes stale in three places —
  `:168-170` documents `stallRounds` inside `GuidanceConfig` (the field this
  RFC removes), `:221`/`:226` document `orchestratorPolicy`, and `:232`
  documents `newOrchestrator`'s bridge parameter. It must be in S4's scope or
  a pinned contract doc drifts.

  Also state (round 3): `concolicAssist`'s `strat`/`prop` are independent
  `typed` macro parameters, so they inherit the same overloaded-proc /
  generic-proc resolution constraints `fuzz(...)`'s own arguments carry
  today (a bare overloaded name with no disambiguating context can fail to
  resolve). Pre-existing, not new risk — but it must be documented as
  applying to the new entry point too.

  Also reframe the README promise honestly rather than patching it. The
  invariant it sells — "`import nelli` never touches Z3" — is exactly what D
  restores. The one-door clause becomes: *Z3 lives behind explicit opt-in
  imports — `nelli/symex` (symbolic execution) and `nelli/concolic` (concolic
  fuzzing assist, a superset that builds on symex).* Two doors where one is a
  documented superset of the other is coherent; two doors pretending to be one
  is not.

- **S5 — release mechanics (NEW).** Breaking public-surface change ⇒ 0.7.0.
  Round-2 corrections:

  - **There is no CHANGELOG file in this repo.** The 0.6.0 release
    (`1f50752`) was a one-line `nelli.nimble` bump whose *commit message*
    carried the breaking-change note; `v*` tags fire `tianguis-publish.yaml`.
    S5 is therefore: release commit message + tag + publish — or it creates a
    CHANGELOG as a deliberate new practice. Say which.
  - **Three stale version sites, not one:** `src/nelli.nim:20`
    (`nelliVersion = "0.1.0"`), `milpa.kdl:5` (`version "0.4.0"`), and
    `nelli.nimble` (the bump itself). Ordering is last-safe — `nelliVersion`'s
    only consumer is `tests/tsmoke.nim:6` (`nelliVersion.len > 0`).
  - **amoxtli's audit is already done:** grepped, **zero** nelli imports
    anywhere. Record the result instead of carrying it as an open task.
  - **chapulin** is the only real downstream. It is not local (Windows
    consumer). Carry a concrete audit spec: grep for bare `import nelli` plus
    the *transitive* surface named in §Breaking change, and for `stallRounds`
    call sites. Its migration bundles with the already-pending v0.6.0
    `FuzzSettings` regroup — one migration, which is an argument for shipping
    0.7.0 promptly rather than sitting on it.

No slice ships a consumer without its producer. Design D makes this nearly
automatic: S1a copies the producer out with core still wired (behavior
unchanged), and S1b1 flips core off, deletes the copies' originals, and turns
the call sites on **in the same slice**, so the property never sits
half-built. There is no intermediate state where a bridge-shaped hole exists
with nothing to fill it. S1b2, S1c, and S2 harden; none is on the path to
the property.

## Risks

- **Macro hygiene at the splice site.** Generated code resolves identifiers in
  the *caller's* scope. `fuzzmacro.nim:53-64` records a real prior footgun.
  Largely retired by the spike (expression-level substitution across a
  `quote do` boundary is the documented-safe class, and the spike exercised
  exactly that), but S1b1 must still prove it with a macro-call-site test in
  the real tree, not a unit test.
- **Silent regression.** Without S2, any future `import` in the wrong module
  reintroduces the dependency invisibly. S2 is not optional polish. `tsmoke`
  sitting red since v0.6.0 is the proof that this risk is not hypothetical.
- **~~Silent degradation on upgrade — the one risk D does *not* delete.~~**
  **Deleted in round 2.** The pre-round-2 shape kept
  `GuidanceConfig.stallRounds`, so an upgrader's `stallRounds: 1` call site
  still compiled and silently no-oped. With the field removed (see §Round-2
  refinement), that call site is now a **compile error naming the missing
  field** — a strictly better diagnostic than the runtime warning this RFC
  previously mandated. The cohort D could not protect at compile time no
  longer exists *on the macro path*; the raw-construction edges (literal
  `ConcolicAssist`, raw orchestrator seam) are specified by the round-3
  contract in §Round-2 refinement rather than assumed away.
- **Assist/property divergence (NEW, round 2).** The 4-arg primitive lets a
  caller build the assist from a different `(strat, prop)` than the one being
  fuzzed, and the macro cannot cross-check. Bounded, not unsound — but it
  degrades to silent yield-poisoning. Mitigated by making `fuzzConcolic` the
  documented default (it enforces the invariant syntactically); see §The
  coherence invariant, including its build-time correction of *which* gate
  bounds the damage (`caoSupersededByRace`, not the re-verify gate).
- **What D *does* delete.** Import-scope inertness (you cannot forget the
  import — `concolicAssist` will not resolve); registration timing;
  double-registration semantics; `{.nimcall.}`/gcsafe constraints on a global
  under `--threads:on`; and per-binary divergence under `dt-bounded.sh`'s
  per-file test binaries. None of these risks survive design D, which is most
  of the argument for it.

## ~~Required diagnostic surface~~ — DELETED in round 2

This section previously mandated a one-shot campaign warning and/or a new
`ConcolicYield` arm for the cohort `stallRounds > 0` ∧ stalled ∧ nil bridge.
**The `ConcolicAssist` refinement makes that state unrepresentable on the
macro path, and the round-3 raw-construction contract specifies the literal
path (raise or coerce)**, so the whole subsystem goes away: no taxonomy
change, no gate split, no one-shot flag, no report plumbing. Round 2 also established the proposed shape was wrong
anyway — every `ConcolicYield` arm (`concolictaxonomy.nim:199-209`) is a
**per-bridge-call outcome**, but in the misconfigured case the bridge is never
called (`fuzz.nim:1595` returns before any fold), so no arm could have hosted
it; it would have needed a new counter field *plus* splitting the `:1595`
conjunction so `stalled()` still evaluates. Recorded because "add an enum arm"
looked cheap and was not.

**Negative control (S1b1 DoD) — rewritten to discriminate.** The pre-round-2
control asserted only zeros, so it passed on a tree where concolic had been
deleted outright — the exact scenario "Both halves, or it has not landed"
forbids. It also used the now-removed `GuidanceConfig(stallRounds: 1)`.

The control is now simply *"plain `import nelli`, no assist"*:

    check report.iterations == 60          # campaign completes, no exception
    check report.coverageHits == 1         # gate never broken
    check report.stats.provenanceCounts[pvConcolic] == 0

and it is made discriminating **by pairing**, not by a warning: the *same
gate, same seed* under `fuzzConcolic` must reach `coverageHits == 2` with
`solvedExact + solvedOptimistic > 0`. One test file, two campaigns, one
differing input — the assist. Zeros alone prove nothing; zeros *next to* a
positive that differs only in the assist prove the seam carries the feature.
Name the file `tfuzz*` so CI sees it.

This also retires the observation that the old "negative" test
(`tfuzzconcolicbridge_real.nim:38-41`) was on the wrong axis. Under the
refinement, the honest negative axis is "no assist supplied", which is exactly
what that test becomes.

## Runtime error surface — missing libz3

**Round 2 found this section prescribed an outcome with no viable design.**
Corrected:

**Today's baseline is campaign abort, not graceful anything.**
`tryConcolicBridge` (`fuzz.nim:1597-1616`) has no `try`/`except`, and neither
does `runConcolicFlipImpl` (`smt/runtime.nim:13098` ff.). `SoftlinkError` is
`ref object of CatchableError` (`_deps/softlink/src/softlink.nim:52`) — **not**
a `Z3Error` — so the Phase-14 C4 policy (`tsymex_phase14_c4_z3error`) neither
covers it nor sits on this entry point. There is nothing to "reuse"; this is
new behavior.

**The catch cannot live in `fuzz.nim`.** Naming `SoftlinkError` there requires
importing softlink, which breaks the very property this RFC restores. Catching
bare `CatchableError` instead would contradict the tree's own standing policy —
"walker `ValueError` and `AssertionDefect` are deliberately NOT caught; those
are real bugs and must propagate" — and would have masked the R1
`materializeConcolicModel` `ValueError` class that
`tfuzzconcolicbridge_real.nim:47-66` exists to prove aborts loudly.

**Therefore:** the catch belongs in the closure `concolicAssist` generates, in
`nelli/concolic`, which legitimately reaches Z3 and can name the type. That
placement also makes it testable **Z3-free** — a fake bridge that raises is
sufficient; no libz3-less environment is needed, which is what makes the DoD
falsifiable at all (both CI containers ship libz3).

Two things that must be specified, not discovered:

- **A new `ConcolicFlipOutcome` arm** (e.g. `cfoSolverUnavailable`) — none of
  the existing five (`concolictaxonomy.nim:67-87`: SolvedExact / Optimistic /
  Unsat / Unmodelable / TimedOut) fits, and the degrade must be expressible as
  an outcome to fold into yield stats like any other.
- **A once-per-campaign latch.** The bridge fires up to
  `maxBranchAttempts` (default 8) times *per stall round, every stall round*;
  without a latch each call re-attempts the lazy load and re-raises.

This is a distinct policy with its own taxonomy change and its own test
mechanism, which is why round 2 split it into **S1b2**. It is not on the path
to the load-bearing property. S4 documents the resulting behavior.

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
`assertCoveredBy`, `concolicCollect`, `symexOpaque`, and the markers
`symexTarget`/`symexAssert`/`symexAssume` (`symex.nim:1085-1100`). Those
markers are *designed* to sit in SUTs run under plain PBT, so a consumer who
reached them via `import nelli` breaks.

**Round 2: the inventory above is the headline, not the total.** `export symex`
is transitive, and the real removed surface is much larger:

    fuzzmacro:51 export symex
      → symex:25 export choice   -- ALL choice constructors (integerChoice, …)
      → symex:27 export dsl      -- smt/dsl re-exports types, abstraction,
                                    dsl_parser, dsl_typebridge, runtime,
                                    stdlib_models
      → symex:199 export db

So bare `import nelli` currently exposes the whole walker/IR/parse surface —
`SymexProgram`, `SymexSettings`, `runConcolicFlipImpl`, IR constructors,
stdlib models — plus choice constructors well beyond `nelli.nim:37-42`'s
selective list. Verified empirically: `discard integerChoice(1,0,10,0)` and
`echo z3FullVersion()` both compile today under bare `import nelli`. This is
also precisely what `tsmoke:32` is red about. **The chapulin audit must grep
this transitive surface, not the eight named symbols.**

In-tree blast radius is smaller than feared but non-zero: of the tests with a
bare `import nelli`, 9 use symex symbols, and every one except
`tfuzzconcolicbridge_real` also imports `nelli/symex` directly (verified in
round 2: 8 symbol-users all dual-import; `tfuzzcmplog.nim` mentions
`concolicFlip`/`symexOpaque` only in comments; `tsymex_phase12_seedphase` gets
`SymexFinding` via `nelli/engine`'s `export types` — safe). Downstream:
**amoxtli audited clean in round 2 (zero nelli imports)**; chapulin remains.
S1b1's DoD covers the bounded suites; S5 owns the version bump and migration
note.

**Resolved (round 3): the markers move — destination specified, promoted to
slice S1c** (`engine/markers.nim`, exported through the already-public
`engine` chain; see §Slices). Round 2 had recommended yes without naming
the leaf, and corrected two errors in how the old text described the
markers:

- They are `proc {.inline.}`, **not templates** (`symex.nim:1085-1101`).
- `symexTarget` is **not** a no-op outside symex — it calls
  `symexCaptureRecord` (`symex.nim:166`), feeding the `{.threadvar.}`
  `symexCapture` context that backs `assertCoveredBy`.

The move is still feasible because that whole capture cluster
(`SymexCaptureCtx`, the threadvar, `symexCaptureBegin/End/Record`,
`symex.nim:146-166`) is itself Z3-free — but it must move **with** them, and
symex must re-export them. "No-ops by construction" would have misled whoever
picked this up.

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

Added in round 2:

- **Put `concolicAssist` in `nelli/symex` itself, adding zero new modules.**
  Post-flip `fuzzmacro` no longer imports symex, so symex importing `fuzz`
  creates no cycle. Tempting, because `nelli/concolic` doing `export symex`
  means two opt-in modules with near-identical exported surfaces — two names
  for one thing, forever. **Rejected**, on module-shape grounds rather than
  mechanics: symex is the *engine*; `concolicAssist` is fuzzer-side glue that
  *consumes* the engine. Folding the glue into the engine would make symex
  import `fuzz`/`fuzzmacro`, coupling symbolic execution to the fuzzer for
  every symex-only consumer — the exact dependency this RFC exists to sever,
  pointed the other way. A thin bridging module above both layers is the
  correct shape, and its interface (two macros) hiding parser/walker/classifier
  machinery is deep by Ousterhout's measure. The redundant surface is a
  hygiene-forced re-export (see S1a), not a design choice, and dual importers
  hit no ambiguity in Nim.
- **A `nelli/all` migration umbrella, or a `{.deprecated.}` re-export shim for
  0.7.0.** **Rejected**: the migration is a single added import line, and a
  shim would preserve exactly the transitive leak that `tsmoke` is red about —
  it would ship 0.7.0 with the bug still present behind a deprecation warning.
- **`bindSym`-hygienic codegen in `dsl_parser`/`concolicAssist`**, so nothing
  needs re-exporting at all and `export symex` could be dropped. This is the
  first-principles ideal and would retire the S1a hygiene constraint entirely.
  **Out of scope** — it is a walker-wide change touching every spliced
  identifier. Recorded as the ideal so the constraint is understood as a
  deliberate debt, not an oversight.
- **A curated re-export list in `nelli/concolic`**
  (`export symex.concolicFlip, symex.IRExprKind, …`) instead of the blanket
  `export symex` — the cheap intermediate between the blanket and the
  `bindSym` ideal above, plausible-looking because `fuzzmacro.nim:52-60`
  already enumerates the free-identifier classes. **Rejected (round 3),
  costed rather than assumed:** that enumeration is of *classes*, not
  names — the concrete set spans every IR constructor and `IRExprKind`
  value the parser can splice, and it grows with the walker. Every
  `symexWalkerVersion` bump that adds a spliced identifier would break
  callers at a distance, exactly the failure S1a's hygiene note warns
  about. The blanket re-export is self-maintaining; the curated list is a
  treadmill.
