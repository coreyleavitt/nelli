# RFC-z3-optional — handoff

- **Stage:** 3 (build) — **ALL SEVEN SLICES SHIPPED.** Next: stage 4 review
  (`/code-review`), then merge + tag.
- **Round:** stage 2 rounds 1–3 done (5 lenses each: depth, breadth, design,
  feasibility, liveness). Rounds 2–3 ran on fable.
- **Mechanism:** RESOLVED — **design D** ("stop auto-wiring the seam"),
  Corey-approved 2026-08-28, **plus the round-2 `ConcolicAssist` refinement**
  (reify the assist; delete `GuidanceConfig.stallRounds` /
  `concolicMaxBranchAttempts`) **plus the round-3 raw-construction contract**
  (raise on bridge-nil+stallRounds>0, coerce on bridge+0; macro path
  unrepresentable) **plus the gate outcome: `assist: untyped` + syntactic
  rewrite** (below).
- **Resume:** stage 4. Nothing left to implement. The `v0.7.0` tag is a
  human action — it fires `tianguis-publish.yaml` (signed OCI artifact to a
  registry) and wants main, not this branch.

## Build progress

| Slice | State | Commit |
|---|---|---|
| S1a | **DONE** | `79651ad` |
| (gate) | **DONE — all three green, `untyped` adopted** | `baeda13` (docs) |
| S1b1 | **DONE** | `2b949de` |
| S1b2 | **DONE** | `e4348ee` |
| S1c | **DONE** | `cfd1a32` |
| S2 | **DONE** | `b2f1bf5` |
| S4 | **DONE** | `2dca562` |
| S5 | **DONE** (tag not cut) | `17781cc` |

### Verification actually run (Linux/podman, `localhost/nelli-dev:latest`)

- **Load-bearing property, both halves, end to end.** Half (1):
  `tests/tz3free_probe.nim` compiles under
  `--skipProjCfg --skipParentCfg --skipUserCfg --noNimblePath --path:src`
  with no z3/softlink path, rc=0, now carrying a marker-annotated SUT too.
  Half (2): `tfuzzconcolicbridge_real` 3/3, `_g6_affine` 2/2,
  `_g6_predicated` 2/2 through `fuzzConcolic`, with the discriminating pair
  (`solvedExact + solvedOptimistic > 0`, `provenanceCounts[pvConcolic] > 0`).
- **`tsmoke` green** — the RED this RFC inherited.
- **Sweep 1 (post-S1b1):** 79 non-symex suites, **zero failures**.
- **Sweep 2 (post-S1c):** 41 symex suites (phase1/6/7, canonicalize, g\*,
  retest\*, phase15 z\*/l\*, CR2_cachekey, phase11, tot1), **zero failures**.
- **Sweep 3 (post-S5):** full non-symex list, 128 suites — two non-zero
  results, **both verified as not-ours**; see §Two findings below.
- **Not run here, by design:** the six `tsymex_r6_*` suites that hang on
  Linux/podman (pre-existing, green on Windows CI — see the
  `symex-r6-linux-hangs` memory), and the full `nimble test`, which is not
  satisfiable on this platform. Windows CI is the backstop, and this branch
  now actually triggers all three Windows legs (S2 found they did not).

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
must still be pinned as "bounded, not unsound". (It was — and the pinning
corrected the RFC's claim about *which* gate turns those seeds away; see
§RFC corrections below. It is `caoSupersededByRace`, not
`caoRejectedAtReplay`.)

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
- [x] **S1b1** — **produces the load-bearing property, both halves.** 4-arg
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
- [x] **S1b2** — missing-libz3 degradation. Catch in `concolicAssist`'s
      generated closure (NOT `fuzz.nim` — can't name `SoftlinkError` there);
      new `cfoSolverUnavailable` outcome; once-per-campaign latch.
      **DoD (round 3):** `tests/tfuzzconcolicdegrade.nim` — campaign
      completes; `cfoSolverUnavailable > 0` observed; latch call-count.
- [x] **S1c** — marker relocation (round 3; was the §Breaking change open
      question). `symexTarget`/`symexAssert`/`symexAssume` + capture cluster
      (`symex.nim:146-166`) → new `engine/markers.nim`, exported via
      `engine.nim`, re-exported by name from symex. Markers survive the
      0.7.0 break under bare `import nelli`.
- [x] **S2** — pin the probe in **both** fuzzer legs (windows + msvc twins),
      corrected flags, **plus an explicit half-(2) discovery assertion**, plus
      a named `tsmoke` step (it matches no existing glob, and S1b1's fix
      re-breaks silently without a pin). The probe step itself lands with
      S1b1; S2 carries the rest. Explicitly NOT taking on the broader
      "no leg runs `nimble test`" hole — separate issue.
- [ ] ~~**S3**~~ — deleted. (Round 2: its premise "no achievable RED" was
      wrong — `tsmoke` was one; now claimed by S1b1.)
- [x] **S4** — consumer docs + build matrix + missing-libz3 behavior +
      **`docs/fuzz/INTERFACE.md`** (normative, pinned by `tfuzzpackaging`).
- [x] **S5** — release mechanics: 0.7.0, **no CHANGELOG exists** (commit msg +
      tag + tianguis-publish), **three** stale version sites
      (`src/nelli.nim:20`, `milpa.kdl:5`, `nelli.nimble`), chapulin audit spec.
      amoxtli audited clean — zero nelli imports.

### S1b1 — as built

**Both halves of the load-bearing property are green, measured this
session:**

- **half (1):** `tests/tz3free_probe.nim` compiles under the §Verification
  channel invocation (`--skipProjCfg --skipParentCfg --skipUserCfg
  --noNimblePath --path:src`, no z3/softlink path), rc=0. `import nelli` is
  Z3-free for the first time since v0.6.0.
- **half (2):** real Z3 solves through the new opt-in door —
  `tfuzzconcolicbridge_real` (3/3), `_g6_affine` (2/2), `_g6_predicated`
  (2/2), all migrated to `fuzzConcolic` and both g6 suites **upgraded**
  with the discriminating pair (`solvedExact + solvedOptimistic > 0`,
  `provenanceCounts[pvConcolic] > 0`) they previously lacked.
- **`tsmoke` green** (3/3) — the pre-existing RED, red since v0.6.0.

Source deltas beyond the RFC text:

- `fuzzMacroImpl` gained an optional `assistExpr` parameter rather than the
  4-arg macro doing AST surgery on the 3-arg expansion's last node. The two
  entry points differ by exactly one argument and now share one emission
  site, so they cannot drift.
- `alignAssistWithCapture` (fuzzmacro) is the round-3 rewrite. It handles
  positional args 1–2 **and** the named `strat =`/`prop =` spellings.
- `fuzz`'s loop-body gate at the old `:2193` keys on `assist.bridge` only,
  with the trap written into the code comment.
- The mapping site resolves `stallRounds` three ways: `0` when there is no
  bridge, the caller's value when positive, else `1`.

Test migrations (all green):

- `tfuzzconcolicbridge.nim` — the two loop-level sites moved to
  `ConcolicAssist(...)`. **One test's premise inverted, deliberately and
  per the RFC:** "a bridge wired but stallRounds left at 0 is never
  invoked (opt-in required)" became "an assist with an explicitly zeroed
  stallRounds is COERCED active". Two tests were added alongside it — the
  zero-value assist as the real off switch, and `ConcolicAssistError` for a
  bridge-less policy.
- `tfuzzconfigdefaults.nim` — the two `GuidanceConfig` checks are replaced
  by a `ConcolicAssist()` zero-value test, so the defaults surface stays
  pinned rather than just shrinking.
- `tfuzzcampaignstats.nim`, `tfuzzconcolicassist.nim` suite 1 — migrated.
- **New `tests/tfuzzconcolicmismatch.nim`** — the mismatch control, 3
  tests: inline positional aligned, inline named aligned, pre-built
  variable bounded.
- Arity pin green: `tfuzzloop` 4/4, `tfuzzmacro` 8/8, `tfuzzmacroreject`
  10/10, `tfuzzmacro_astspike` 2/2.
- Arm-collapse blast radius green: `tfuzzprocessisolation` 6/6,
  `tfuzzworkerspawnfailshm` 2/2, `tfuzzcmplogprocess` 3/3, `tfuzzcmplogshm`
  3/3, `tfuzzcmplogshmleak` 1/1, plus `tfuzzshmhold` and `tfuzzcovshm`.
- The probe's CI step landed in `fuzzer-windows.yaml` (mingw leg), before
  the suite loop, failing the leg on its own. S2 owns the MSVC twin, the
  `tsmoke` pin, and the half-(2) discovery assertion.

### S1b2 / S2 / S4 / S5 — as built

- **S1b2.** The catch is a NAMED, EXPORTED wrapper
  (`guardSolverUnavailable`), not something buried in the macro's codegen —
  that is what lets the degrade suite drive the REAL guard around a fake
  raising bridge, which is the only way this DoD is falsifiable at all (both
  CI containers ship libz3). `concolicAssist` wraps its own closures in the
  same one; there is no test-only path. `cfoSolverUnavailable` is APPENDED
  to `ConcolicFlipOutcome` so no ordinal shifts; no exhaustive `case` over
  that enum exists in the tree (checked).
- **S1c.** No `symexWalkerVersion` bump: pure relocation, and the parser's
  own recognition tests (`tsymex_phase1_dsl`) are green unchanged. The probe
  was widened to carry a marker-annotated SUT, so "markers resolve with the
  walker unreachable" is a compile-checked fact.
- **S2 found a hole the RFC did not name: the legs did not run on this
  branch.** Both fuzzer workflows trigger on push to
  `[main, rfc-fuzzer-nextgen]` only, and `fuzzer-msvc` has no
  `pull_request` trigger — so every pin S2 adds would have been dormant
  until merge, on the branch that most needs Windows verification. Added
  `rfc-z3-optional` to both, and to `symex-windows` too (S1c touches
  symex.nim). Also fixed: a backtick inside a PowerShell double-quoted
  string is an ESCAPE, not a quote.
- **S5 decided the CHANGELOG fork: create one, deliberately.** 0.7.0 breaks
  three ways and chapulin has not absorbed 0.6.0's regroup, so it migrates
  across two releases at once and needs a document it can find. `CHANGELOG.md`
  reconstructs 0.6.0 for that reason. The three version sites had drifted to
  0.6.0 / 0.4.0 / 0.1.0 and are now pinned to agree by `tfuzzpackaging`.
  The chapulin audit is `docs/RFC-z3-optional.downstream-audit.md` — runnable
  greps, since the repo is a Windows consumer and not local.

### The one thing left, and why it is not mine to do

`git tag v0.7.0` fires `tianguis-publish.yaml`, which pushes a signed OCI
artifact to a registry — outward-facing and hard to reverse — and this
branch is not merged to main. The release is PREPARED (versions, CHANGELOG,
audit spec), not published.

## Two findings from the final sweep that are NOT this RFC's (verified)

Sweep 3 (full non-symex list, 128 suites) returned exactly two non-zero
results. Neither is a regression from this branch; both are recorded here so
the next reader does not re-diagnose them.

- **`tests/trequiresinit.nim` is RED on `main`.** It fails to compile:
  `src/nelli/optbox.nim(36,13) Error: Cannot prove that 'result.p' is
  initialized [ProveInit]`, reached through
  `dsl -> engine -> phases -> eval -> box`. **Verified at `1f52...`/`1f50752`
  (v0.6.0), which IS `main`**, in a clean worktree with the same image: same
  file, same line, same error. Pre-existing, not caused by this RFC.

  Diagnosis: `box[T]` does `new(result.p); result.p[] = x`, and `ProveInit`
  cannot follow `new` on a `result` field for a `{.requiresInit.}` `T` --
  the exact case `optbox` exists to serve. Attempted fix
  (`var p = new(T); p[] = x; Opt[T](p: p)`) compiles standalone for a
  `requiresInit` object but only pushes the same error into `system.nim`'s
  own `new(T)` body for the engine's actual type, so it was **reverted**.

  **FIXED after all** (follow-up, not part of the seven slices). The first
  attempt was reverted as too risky; the second is a real fix rather than a
  suppression, so it earned its place:

  `Opt`/`Examples` were backed by a bare `ref T`, which can only be filled
  by `new(r); r[] = x` -- allocate zeroed, then assign over it. For a
  `{.requiresInit.}` `T` that opens a genuine window in which a `T` exists
  that no constructor ever produced, and `ProveInit` is right to say so.
  Backing them with `Boxed[T] = ref object` instead lets every box be built
  by ONE object construction naming every field (`Boxed[T](v: x)`), so the
  zero-filled intermediate never exists at all. Same single allocation, same
  nil-is-empty semantics, public surface unchanged (the field was private).
  `tests/trequiresinit.nim` goes 0/0-compile-error -> **5/5 green**, and the
  fix removes the hazard the warning was pointing at rather than muting it.

  Verified against BOTH `requiresInit` shapes the test uses (plain
  all-required-fields object, and an object variant) under all three of its
  escalated warnings (`UnsafeDefault`, `UnsafeSetLen`, `ProveInit`).

  Note it is the same *class* of rot this RFC diagnosed for `tsmoke`: it is
  in `nelli.nimble`'s `task test` list, matches no CI glob, and so no
  workflow has ever run it.

- **`trequiresinit` is now pinned in CI too, as a bounded experiment.**
  Leaving it unpinned would repeat the exact mistake this RFC exists to fix.
  But `symex-windows.yaml`'s header ledgers it as "known to fail on Windows
  for environment/platform reasons" and says a future non-symex leg should
  skip-list it. That ledger predates this fix, and the Linux failure it was
  written against was this same `ProveInit` error -- so the entry may simply
  be stale. It cannot be tested from the Linux dev host, so the pin is a
  cheap way to find out on a real runner.

  **RESULT: the ledger was stale, and the pin holds.** `trequiresinit` runs
  and passes as a named step on BOTH Windows toolchains after the optbox fix
  -- mingw and MSVC, commit `da20181`, confirmed in the run logs
  (`==> trequiresinit.nim (contract test)` followed by the leg's own
  all-passed line). Its failure was never environmental; it was the same
  `ProveInit` bug, on every platform. `symex-windows.yaml`'s header has been
  corrected: the entry told a future maintainer to skip-list a suite that
  only needed a fix.

- **`tests/tparallelcheck.nim` was a load flake, not a failure.** It passed
  standalone on three subsequent runs (rc=0 each). It is a linearisability
  test over real threads and was running 5-way parallel under `podman` at the
  time. No action.

## RFC corrections found while building (measured, not argued)

- **§The coherence invariant names the wrong rejection mechanism.** The RFC
  says a mismatched assist "degrades to silent yield-poisoning" because
  "the re-verification gate at `fuzz.nim:1607-1616` rejects seeds that
  don't reproduce (`caoRejectedAtReplay`)". Measured across two mismatch
  shapes (narrow-domain and same-domain), `caoRejectedAtReplay` is **0**.
  The mismatched seeds are valid draws for the campaign's own strategy, so
  they replay **cleanly**; they are turned away one layer later by
  `admit`'s interestingness fold, as `caoSupersededByRace` (58 of them in
  a 60-iteration campaign, against 58 exact solves and 0 admits).
  **The RFC's conclusion is unchanged and better supported** — bounded, not
  unsound, and the cost is exactly the wasted solver work the phrase
  "yield-poisoning" names. Only the cited mechanism was wrong. Pinned as
  measured in `tests/tfuzzconcolicmismatch.nim`, with the correction
  written into the test.

  *Flagged for sanity-check, not blocking: the fix was to pin observed
  behavior rather than to make the observed behavior match the prose.*

- **`docs/fuzz/INTERFACE.md` is NOT pinned by `tests/tfuzzpackaging.nim`.**
  S4's round-2 addition calls it "normative (its contract is pinned by
  `tests/tfuzzpackaging.nim`)". Grepped: `tfuzzpackaging.nim` contains zero
  references to INTERFACE.md, and its own header says it pins
  **`docs/fuzz/USAGE.md`**'s surface. No test in the tree mentions
  INTERFACE.md at all — it is normative by convention only, with nothing
  catching drift.

  This matters because it is the same failure class the RFC exists to fix
  (a documented contract that quietly went stale because nothing ran).
  **Recommendation for S4, will proceed on it unless told otherwise:**
  update INTERFACE.md *and* make the claim true — extend `tfuzzpackaging`
  with a compile-level pin of the surfaces INTERFACE.md documents
  (`ConcolicAssist`'s three fields, `fuzz`'s `assist` parameter,
  `orchestratorPolicy`'s signature), so the next drift fails a test instead
  of sitting.

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

Round 1 run 2026-08-29 over `main...HEAD`. Six lenses in parallel
(correctness, security, liveness, design, test quality, spec/CI/release);
every finding below was verified against the tree before being recorded.

| id | sev | status | file | finding | verified by |
|---|---|---|---|---|---|
| R1-1 | High | **fixed** | `docs/RFC-z3-optional.downstream-audit.md:27` | The chapulin symbol grep covers 5 names and misses the **transitive** surface the RFC explicitly requires ("must grep this transitive surface, not the eight named symbols", RFC §Breaking change). Omits `z3FullVersion`, `concolicCollect`, `symexOpaque`, all choice constructors (`integerChoice`…, via `export choice`), the `smt/dsl` chain, `IRExprKind` values, `SymexSettings`, `runConcolicFlipImpl`, `export db`. | read the file; greps are runnable but narrower than the RFC's own rejected baseline |
| R1-2 | Med | **fixed** | `src/nelli/fuzzmacro.nim:517-521` | `alignAssistWithCapture` matches only `nnkIdent`/`nnkSym`/sym-choice callees, so a qualified/aliased call (`cc.concolicAssist(sB,pB)` → `nnkDotExpr`) silently skips alignment and falls to the unaligned path. Same for a template/alias spelling. Not named as accepted debt anywhere; untested. | 3 independent reviewers + direct read of the code |
| R1-3 | Med | **fixed** | `.github/workflows/fuzzer-windows.yaml:191` | Probe step omits `--cc:gcc` while both other `nim c` calls in the same leg (`:235,:274`) pin it and the file header `:31-38` documents *why* it must be explicit. The MSVC twin's probe (`fuzzer-msvc.yaml:205`) does pin `--cc:vcc`. Breaks the hand-synced-twins invariant. | grepped `--cc:` across both legs |
| R1-4 | Med | **fixed (design call, Corey 2026-08-29)** | `src/nelli/concolic.nim`, `src/nelli/fuzzmacro.nim` | The `paramCount != 1` arm was unreachable — every property passes through `inProcessTarget*[T](prop: proc(x: T))` (arity 1) at `fuzzmacro.nim:407,:469,:475`; identical signature on `main`, so it was always dead. RFC §S1a mandated reproducing it under the false premise it was live. Worse than dead: it silently ACCEPTED a shape that cannot run, deferring the failure to a `inProcessTarget(...)` type mismatch at a macro-internal line the user never wrote. **Resolution:** deleted the arm; added `requireSingleParam` in `fuzzmacro` (one shared check, called from `fuzzMacroImpl` AND `concolicAssistImpl`, since `concolicAssist` is callable standalone for the raw seam) which `error()`s at capture time naming the constraint and the tuple-strategy fix. `countFormalParams` verified correct as-is (counts NAMES: `proc(x, y: int)` → 2). Multi-value properties keep working as tuple-typed single params. | new `tfuzzmacroreject` case (`proc(x,y:int)`) 11/11; `tfuzzhavoc` 29/29 pins the tuple idiom; 16 suites green; probe rc=0 |
| R1-5 | Med | **fixed** | `src/nelli/fuzz.nim:1897`, `:1937-1939` | The one documented rule ("assist present ⇒ assist active") is implemented as two inline conditionals ~40 lines apart inside `fuzz*[T]`'s body, correlated only by comment. Decision logic interleaved with orchestrator-construction I/O. Suggested: a `resolveAssist` proc beside the type. | design lens; code read confirms the split |
| R1-6 | Med | **fixed** | `src/nelli/fuzzmacro.nim:513-532` | The rewrite silently changes user-written arguments with zero compile-time signal. A `hint(...)` emitted only when a node actually changes is pure upside — keeps auto-correction, surfaces the latent bug it papers over. | design lens |
| R1-7 | Med | **fixed** | `src/nelli/fuzzmacro.nim:497` | `alignAssistWithCapture`'s docstring cites `caoRejectedAtReplay` as the gate that turns mismatched seeds away. Measured behavior (pinned in `tfuzzconcolicmismatch.nim`) is `caoSupersededByRace`; the correction reached the handoff and the test but not this shipped docstring. | grepped `caoRejectedAtReplay` in `src/` |
| R1-8 | Low | **fixed** (rider) | `docs/fuzz/INTERFACE.md:208` | `maxBranchAttempts` documented "(0 ⇒ 8)"; code coerces any `<= 0` (`fuzz.nim:1940-1941`). Adjacent `stallRounds` line words it correctly. | read both |
| R1-9 | Low | **fixed** | `src/nelli/symex.nim:12,16` | Header still calls the body markers "templates" and `symexTarget` a "no-op" — both wrong per the RFC's own round-3 correction (`proc {.inline.}`; records into the capture). S1c moved these symbols out, so the stale prose now also points at the wrong module. | read the header |
| R1-10 | Low | **fixed** | `docs/RFC-z3-optional.md:4-7,204,294,750,826` | RFC text stale vs shipped: status header still "stage 2 … S1a READY for `/tdd`"; `:204` shows `assist: typed` though the gate adopted `untyped`; `:294`/`:750` cite `caoRejectedAtReplay`; `:826` half-(2) snippet pins one test where CI pins four. | read each line |
| R2-1 | Low | **fixed** | `src/nelli/fuzzmacro.nim:493-497` | Re-review round 2: the new `nnkDotExpr` helper's docstring claimed ignoring the qualifier means it "never mistakes an unrelated dotted call" — backwards. Ignoring the qualifier is precisely what permits an over-match. Rewritten as a stated, bounded trade-off. | introduced by the R1-2 fix; caught in re-review |
| R2-2 | Low | **fixed** | `docs/fuzz/INTERFACE.md:213-223` | Re-review round 2: interposing the `resolveAssist` snippet left `SchedulingConfig*` orphaned in a `type` block with no `type` keyword, making the illustrative snippet invalid Nim. Reopened the block. | introduced by my INTERFACE.md edit; caught in re-review |
| R1-11 | note | **wontfix (deliberate)** | `src/nelli/concolic.nim:35` | Blanket `export symex` makes the module's *effective* surface ≈ all of `nelli/symex` plus two names, not the 3 documented ones. RFC costed the alternatives (curated list = treadmill; `bindSym` = walker-wide) and accepted this deliberately. Recorded as named debt, not a defect. | design lens |
| — | — | refuted | `.github/workflows/fuzzer-msvc.yaml` | Reviewer brief premise "this branch added a `pull_request` trigger to the MSVC leg" is **false** — the leg has never had one, before or after; only the push allowlist changed. Dropped. | 2 agents diffed `on:` against `main` |
| — | — | refuted | `tests/tfuzzpackaging.nim` | The handoff's own open item "INTERFACE.md is NOT pinned by `tfuzzpackaging`" is **resolved** — `tfuzzpackaging.nim:34-70` now pins `ConcolicAssist`'s fields, `fuzz`'s `assist` param and `orchestratorPolicy`. Dropped. | read the suite |

**Verified correct (no findings):** liveness — every mechanism traces to a
live producer through a real entry point, nothing dark; security — the
`SoftlinkError` catch cannot widen to `ValueError`/`AssertionDefect`, the
latch is closure-local and bounds retries, `ConcolicAssistError` raises
before any worker/shm/orchestrator is allocated, no new `${{ }}` or action
refs in CI; the G6 cluster copy diffs byte-for-byte against
`main:fuzzmacro.nim:382-643` with no drift; `cfoSolverUnavailable` appended
with no ordinal shift and no exhaustive `case` in-tree; the arm collapse
preserves `spawnFreshWorker` by construction (one emission path, not two
kept in sync); `optbox`'s `Boxed[T]` never passes through a zero-filled
intermediate; no migrated test lost an assertion vs `main` (both g6 suites
gained the discriminating pair); all three version sites agree at 0.7.0 and
are pinned by `tfuzzpackaging`; all new suites registered in `nelli.nimble`
and CI-visible; the half-(2) discovery pin is correct PowerShell and covers
four tests, not one.
