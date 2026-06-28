# ADR-0012 — Target-vs-defect verdict semantics (status answers the query; defects are diagnostics)

> **STATUS: ACCEPTED — 2026-06-28.** Captured from a codebase-mode `/architect`
> pass on the post-R16-4 blocker. Governs the verdict-aggregation seam
> (`runSymex`/`runSymexImpl` reduction, `shouldStop`, `routeRaise` surfacing, and
> the `SymexResult[T]`/`RawResult` result types). Sits *on top of* ADR-0011: it
> keeps `arithChecks` **all-on** (ADR-0011 F2 unchanged) and resolves the
> collision that all-on created with label-reachability queries.
> Citations point-in-time at walker `v25` (after R16-4); re-verify each `/tdd` cycle.

## Context — the blocker

ADR-0011 made `arithChecks` default **all-on**, and D1a made every non-excluded
defect surface **unconditionally** (regardless of the active target). Together
these regressed **17 of 180** sweep tests: ordinary SUTs with unbounded signed
arithmetic (`x*2`, `a+b`, `t.inner.x + t.inner.y`) targeted at a **label** now
return `sxRaised(OverflowDefect)` instead of `sxSat`. Since overflow is reachable
on essentially *all* unbounded signed arithmetic, every arithmetic-bearing SUT
raises, and the raise swamps the reachability answer.

This is **not** an R16-4 bug and **not** a soundness bug — both findings are true.
For `let y = x*2; if y > 10: target` the path forks: one branch overflows
(`sxRaised`, e.g. x huge) and the other reaches the label (`sxSat`, e.g. x=6).
Both are legitimately reachable. The defect is that the engine reduces the search
to a **single scalar `status`** that conflates two different questions:

1. *"Is the queried target reachable?"* (the caller's actual query)
2. *"Is a defect reachable somewhere on the way?"* (an incidental discovery)

### Mechanics of the conflation (verified, walker v25)

- Findings accumulate in `w.found: seq[RawResult]`, flat-mixing label-reachability
  `sxSat` (added at `runtime.nim:5650-5665`) and defect/exn `sxRaised` (added via
  `routeRaise`, `runtime.nim:5926-5940`).
- The reduction (`runtime.nim:7000-7018`) returns `w.found[0]` — **first-finding-
  wins, by walk order.**
- **The load-bearing subtlety:** `shouldStop` (`runtime.nim:4117-4118`) halts on
  **any** `sxSat` *or* `sxRaised`, regardless of target. `isTargetLabel` checks
  `if w.shouldStop: return` (`runtime.nim:5653`) **before** solving the label. So
  once an incidental overflow `sxRaised` lands in `w.found`, the walk dies and the
  label's `sxSat` is **never computed**. ∴ for a label SUT with overflow-on,
  `w.found = [sxRaised(overflow)]` with no `sxSat` at all — a reduction-only fix
  cannot recover it.

## Decision

**`status` answers the target query; incidentally-discovered defects ride along as
typed `diagnostics`. Checks stay on-by-default; no true finding is dropped.**

Three changes, in dependency order:

### D1 — target-aware `shouldStop` (the mandatory core)

`shouldStop` becomes target-aware:
- `stkLabel`: halt **only on `sxSat`** — an incidental `sxRaised` must NOT stop
  label exploration (a non-raising sibling path may still reach the label).
- all raise-flavoured targets (`stkAssertionViolation`, `stkRaisedExn`,
  `stkIndexError`, `stkFieldDefect`, `stkNilAccess`): unchanged — halt on `sxSat`
  or `sxRaised` (a matching raise *is* the terminal finding).

Without this, the `sxSat` never reaches `w.found` and the rest is moot.

### D2 — target-aware reduction + `diagnostics` channel

- Add `diagnostics: seq[DefectFinding[T]]` (and internal `seq[RawDiagnostic]`) as a
  **common field placed before the `case status` discriminant** on
  `SymexResult[T]`/`RawResult`, so it is present on every status branch. The
  case-object is **otherwise unchanged** — all existing field reads
  (`.status`/`.witness`/`.raisedTypeId`/`.raisedWitness`) and the compiler's
  discriminant narrowing are preserved.
- Replace the `w.found[0]` reduction with a **unified precedence**
  `sxSat` > `sxRaised` > `sxUnsat`/`sxUnknown` over `w.found` (`partitionFindings`):
  scan for the first `sxSat`; else the first `sxRaised`; else `sxUnsat`/`sxUnknown`.
  - This is correct for *all* target kinds simultaneously: raise-flavoured targets
    only ever accumulate `sxRaised` (label `sxSat` is added solely at
    `isTargetLabel`, gated on `stkLabel`), so first-`sxRaised`-wins is preserved
    **bit-identical to today** — the 33 stay green and no type-priority matching is
    added. For `stkLabel`, the label's `sxSat` wins when the label is *cleanly*
    reachable.
  - **The all-raise label case** (label NOT cleanly reachable, a defect fires on
    every explored path → `w.found` has no `sxSat`): status = `sxRaised`, NOT
    `sxUnsat`. Returning "unsat" when the code actually *crashes* before the label
    would hide a real defect and contradict D1a's "defects always surface" + the
    tool's bug-finding purpose (ADR-0011 F2). The defect surfaces as the headline.
  - Every *non-winning* `sxRaised` goes into `diagnostics`.
- The `symexFind` macro types each `RawDiagnostic.raisedWitness` into the SUT tuple
  `T` via the existing `witnessTup` reader, producing `DefectFinding[T]`.

`DefectFinding[T]` carries: `raisedTypeId`, `defectKind`, `isDefect`, `raisedMsg`,
typed `witness`, `heapSnapshot`. When `status == sxRaised`, the winning raise lives
in the `sxRaised` branch fields (NOT duplicated into `diagnostics`); a 7-line
`allRaiseFindings(r)` helper unions them for callers who want the full set.

### D3 — `routeRaise` surfacing contract: unchanged

Non-excluded defects still always *surface* (get discovered, solved, and added to
`w.found`) regardless of target — the E6 contract holds. We change only what the
*reduction* does with a label-target's incidental raise, not whether it is found.

## Consequences

- **17 label-target tests → green** (status flips back to `sxSat`); **33 raise-
  target tests stay green** (first-raise-wins preserved). All 987 existing field
  reads compile unchanged. New capability: a label search now also reports every
  overflow/div-zero/range defect it discovered, as typed diagnostics — without a
  second `symexFind` call.
- **Verdict-semantics change → `symexWalkerVersion` 25 → 26**, and the two exact-
  equality pins (`tsymex_phase15_CR2_cachekey.nim`,
  `tsymex_phase16_R16_1_arithcheck_foundation.nim`) update + run. See
  `[[symex-version-bump-cr2]]`.
- **`diagnostics` is best-effort, not exhaustive:** `shouldStop` halts a label
  search on the first `sxSat`, so diagnostics capture raises discovered on paths
  explored *before* the label was hit — advisory, not a completeness guarantee.
  Acceptable for a diagnostic channel; documented so callers don't over-read it.
- **Rejected alternatives:**
  - *A (minimal/drop-defect):* drops the incidental defect for label targets —
    loses the diagnostics capability and throws away true findings.
  - *C (unified `seq[Finding]` + accessor procs):* replaces the case discriminant
    with computed accessors, **losing compile-time discriminant narrowing** on the
    public result type — a real safety regression for a no-false-positives engine —
    in exchange for speculative extensibility (no consumer needs it; YAGNI).
  - *Flip `arithChecks` to `{}` (the original stopgap):* retreats from the Corey-
    locked all-on default; reversible churn (two version bumps) and abandons the
    bug-finding purpose. Rejected.

## Implementation path (`/tdd`)

1. **Slice 1 — D1+D2 reduction:** target-aware `shouldStop` + `partitionFindings`,
   *without* yet exposing `diagnostics` publicly (relegated raises simply dropped
   at the macro boundary). RED: a label SUT with overflow-on currently
   `sxRaised`/`sxUnsat`; GREEN: `sxSat`. Re-run the 17 + 33 cohorts + parity.
2. **Slice 2 — diagnostics channel:** add the `diagnostics`/`RawDiagnostic`/
   `DefectFinding[T]` types + macro typing; new test asserts a label search reports
   the incidental overflow in `diagnostics`. Bump v26 + both pins. Full 180-file
   sweep, both backends.
