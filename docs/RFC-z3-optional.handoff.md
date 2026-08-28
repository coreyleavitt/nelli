# RFC-z3-optional — handoff

- **Stage:** 3 (build) — S1a shipped, spike gate CLOSED.
- **Round:** stage 2 rounds 1–3 done (5 lenses each: depth, breadth, design,
  feasibility, liveness). Rounds 2–3 ran on fable.
- **Mechanism:** RESOLVED — **design D** ("stop auto-wiring the seam"),
  Corey-approved 2026-08-28, **plus the round-2 `ConcolicAssist` refinement**
  (reify the assist; delete `GuidanceConfig.stallRounds` /
  `concolicMaxBranchAttempts`) **plus the round-3 raw-construction contract**
  (raise on bridge-nil+stallRounds>0, coerce on bridge+0; macro path
  unrepresentable) **plus the gate outcome: `assist: untyped` + syntactic
  rewrite** (below).
- **Resume:** `/tdd docs/RFC-z3-optional.md S1b1`.

## Build progress

| Slice | State | Commit |
|---|---|---|
| S1a | **DONE** | `79651ad` |
| (gate) | **DONE — all three green, `untyped` adopted** | (scratchpad, gitignored) |
| S1b1 | next | |
| S1b2 | pending | |
| S1c | pending | |
| S2 | pending | |
| S4 | pending | |
| S5 | pending | |

### Round-3 spike gate — CLOSED 2026-08-28, all three green

Run in `localhost/nelli-dev:latest`; Q2 measured against the REAL tree (an
experimental 4-arg overload added to `fuzzmacro.nim`, then reverted — tree
verified clean), Q3 in `scratchpad/z3spike2/tspike_untyped.nim`.

1. **Two-arg `concolicAssist(strat, prop: typed; stallRounds; maxBranchAttempts)`
   — GREEN.** Not spiked separately: S1a *shipped* it, which is stronger.
   Works positionally and by name, in expression position, with a lifted
   inline-lambda property. Both defaulted params are declared `untyped` (not
   `static[int]`) so a runtime value can be threaded through `fuzzConcolic`.
2. **`assist: untyped` vs the macro/proc arity collision — GREEN.** A 4-arg
   `macro fuzz*(stratExpr, propExpr, settingsExpr: typed; assist: untyped)`
   does **not** steal 4-arg concrete-proc calls: `tfuzzloop` (4/4) and
   `tfuzzmacro` (8/8) both compiled and passed with the overload present.
   The converse also holds — a genuine `assist = concolicAssist(...)` call
   selects the macro and solves.
3. **Syntactic rewrite-and-resplice — GREEN, proven behaviorally.** The
   outer macro rewrites an inline `concolicAssist(...)`'s first two
   arguments with its own typed strat/prop copies across the `quote do`
   boundary. Test: an assist written against a **deliberately different**
   `(integers(0,100), otherGate)` pair still broke the outer call's
   `0xCAFEBABE` gate with `solvedExact + solvedOptimistic > 0` — i.e. the
   mismatch was corrected, not merely tolerated.

**Decision (per the RFC's own rule): adopt `assist: untyped` + the
rewrite.** The coherence invariant is therefore enforced *at the primitive*
for the written-inline form. Handle both positional args 1–2 and the named
`strat =`/`prop =` spellings — a rewrite that silently skipped the named
form would leave exactly the hole it exists to close.

**Unchanged by the gate:** S1b1's mismatch control is still required. A
pre-built `ConcolicAssist` *variable* passed as `assist` is not a syntactic
`concolicAssist(...)` node and bypasses the rewrite entirely; that path
must still be pinned as "bounded, not unsound" via `caoRejectedAtReplay`.

### S1a — as shipped (deltas from the RFC text)

- `concolicAssist`'s two policy params are `untyped` with defaults `1`/`8`,
  not bare `= 1`/`= 8` (macro params of an ordinary type are implicitly
  static, which would forbid threading a runtime value from `fuzzConcolic`).
- Each `paramCount` arm emits a `block:` **expression** whose value is the
  `ConcolicAssist` literal, with the bridge closure bound to a `let` first
  — the same self-contained-`quote do` discipline `fuzzMacroImpl` documents
  (splicing a multi-statement node mid-`quote do` opens a scope and hides
  the `let`s).
- `tfuzzconcolicassist.nim` carries **four** tests, not two suites of one:
  the two seams, plus a paired negative control on the `fuzz`-parameter
  seam, plus a policy-defaults check pinning `stallRounds == 1` (an assist
  that defaulted to `0` would be inert by construction).
- `fuzzmacro`'s `propFormalParams`/`countFormalParams`/`liftPropIfNeeded`
  are now exported. `concolic -> fuzzmacro` is the only edge; the reverse
  must never be added.

## Round 3 — headline outcomes

- **CRITICAL (feasibility, empirically proven in-repo): S1a "relocate" was a
  circular import.** Deleting the classifier from `fuzzmacro` while core
  still auto-wires forces `fuzzmacro → concolic` AND `concolic → fuzzmacro`
  simultaneously (compile error captured, patch reverted). **S1a is now a
  COPY**; S1b1 deletes the fuzzmacro-side originals atomically with the
  flip. Invariant: the `fuzzmacro → concolic` edge never exists.
- **S1a now introduces the `ConcolicAssist` type** (it existed in no slice's
  inventory — zero grep hits in-tree); its RED test targets the *existing*
  `concolicBridge` proc param and migrates at S1b1 (named in DoD).
- **The raw seams were overclaimed as "unrepresentable."** New
  raw-construction contract: `ConcolicAssistError` at campaign start for
  bridge-nil+stallRounds>0 (mirrors `ProcessIsolationError`,
  `fuzz.nim:629-638/1833`); coercion justified for bridge+explicit-0; raw
  orchestrator seam documented as deliberate contract
  (`tfuzzconcolicbridge.nim:23-32` pins it).
- **Orchestrator + real assist bridge would have shipped dark** — no test
  threads a `concolicAssist`-built bridge through `newOrchestrator`. Now
  suite 2 of S1a's RED test.
- **S1b1 DoD gained:** process-isolation regression suites (the arm-collapse
  touches `spawnFreshWorker` wiring at `fuzzmacro.nim:809,823`); `_real`'s
  second suite (R1 uint64Gate `:43-66`); the mismatch control
  (`caoRejectedAtReplay`); probe CI step lands in the same commit; blast
  tally stated (3 src modules, 11 test files) with atomicity defense.
- **S1b2 gained a DoD** (fake raising bridge; `cfoSolverUnavailable > 0`
  observed; latch call-count) — it previously shipped a taxonomy arm with no
  test naming it.
- **New spike gate before S1b1** (`scratchpad/z3spike/` is deleted from
  disk): (1) the two-arg `concolicAssist` shape was never spiked; (2)+(3)
  `assist: untyped` + syntactic rewrite could enforce the coherence
  invariant at the primitive — adopt on green, keep `typed` on red.
- **Marker relocation resolved and promoted to S1c**: `engine/markers.nim`,
  exported via the already-public `engine` chain; `engine/types.nim`
  rejected (procs, not types).
- Also: `fuzz.nim:2193` second-gate trap noted; curated-export alternative
  costed and rejected; `concolicAssist` typed-param constraints → S4.

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

## Slices (re-cut in round 2, corrected in round 3)

- [x] **S1a** — **COPY** the bridge builder into `src/nelli/concolic.nim`
      (round 3: "move" was a proven circular import; fuzzmacro's originals
      stay untouched and auto-wiring until S1b1 deletes them).
      Copies `fuzzmacro.nim:382-643` (the whole G6 cluster — the seven
      helpers at `:382-526` are load-bearing) **plus both** bridge arms'
      logic at `:799-823`. concolic.nim imports `std/macros`, `./symex`
      (+export), `./fuzz`, `./smt/transparency`, `./fuzzmacro` (for the
      shared `propFormalParams`/`countFormalParams`/`liftPropIfNeeded`,
      which get exported — this direction only, never the reverse).
      **Also introduces the `ConcolicAssist` type in `fuzz.nim`** (additive).
      **RED:** new `tests/tfuzzconcolicassist.nim` (`tfuzz*`-prefixed), TWO
      suites: (1) real assist → existing `concolicBridge =` proc param;
      (2) real assist → raw `newOrchestrator` seam (else it ships dark).
      DoD: bounded suites via `dt-bounded.sh`, not `nimble test`; register
      the file in `nelli.nimble`.
- [x] **(gate)** — §Round-3 spike gate: **all three green ⇒ `assist:
      untyped` + syntactic rewrite adopted.** See §Round-3 spike gate above.
- [ ] **S1b1** — **produces the load-bearing property, both halves.** 4-arg
      `fuzz` overload (param literally named `assist`; typed/untyped per
      spike gate); drop `import ./symex`/`export symex` + delete fuzzmacro's
      copied originals; `GuidanceConfig` field removal + `assist` proc param
      + raw-construction contract (`ConcolicAssistError`); `fuzzConcolic`
      (folded in from old S1c); migrate **three** real-bridge tests (incl.
      `_real`'s R1 uint64Gate suite) + 3 loop-level sites +
      `tfuzzconfigdefaults:40-41` + `tfuzzconcolicassist` suite 1.
      DoD: probe Z3-free, **`tsmoke` green**, gate + both g6 suites green
      with positive-signal checks, `tfuzzloop` + `tfuzzmacro` (arity pin),
      process-isolation suites bounded-green (arm-collapse blast radius),
      mismatch control (`caoRejectedAtReplay`), paired negative control,
      probe CI step in the SAME commit. Trap: `fuzz.nim:2193` gate keys on
      `assist.bridge` only.
- [ ] **S1b2** — missing-libz3 degradation. Catch in `concolicAssist`'s
      generated closure (NOT `fuzz.nim` — can't name `SoftlinkError` there);
      new `cfoSolverUnavailable` outcome; once-per-campaign latch.
      **DoD (round 3):** `tests/tfuzzconcolicdegrade.nim` — campaign
      completes; `cfoSolverUnavailable > 0` observed; latch call-count.
- [ ] **S1c** — marker relocation (round 3; was the §Breaking change open
      question). `symexTarget`/`symexAssert`/`symexAssume` + capture cluster
      (`symex.nim:146-166`) → new `engine/markers.nim`, exported via
      `engine.nim`, re-exported by name from symex. Markers survive the
      0.7.0 break under bare `import nelli`.
- [ ] **S2** — pin the probe in **both** fuzzer legs (windows + msvc twins),
      corrected flags, **plus an explicit half-(2) discovery assertion**, plus
      a named `tsmoke` step (it matches no existing glob, and S1b1's fix
      re-breaks silently without a pin). The probe step itself lands with
      S1b1; S2 carries the rest. Explicitly NOT taking on the broader
      "no leg runs `nimble test`" hole — separate issue.
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

Round 3 likewise applied everything under the standing bar. Two items
flagged for sanity-check, not blocking: (a) the `assist: typed` vs `untyped`
choice is deliberately left to the spike gate's decision rule rather than
picked in prose — the gate's outcome is mechanical (green ⇒ untyped);
(b) S1b1's blast tally (3 src modules, 11 test files) exceeds the normal
slice bar and is kept atomic anyway, with the defense written into the RFC.

## Spike results (2026-08-28, `localhost/nelli-dev:latest`)

Artifacts were in `scratchpad/z3spike/` — **now deleted from disk** (round-3
note: the closures below cannot be re-run as-is; the §Round-3 spike gate
rebuilds what it needs in `scratchpad/z3spike2/`).

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
  Patch reverted; the probe is **already committed** on this branch
  (`8966402`) but registered nowhere until its CI step lands with S1b1.
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
