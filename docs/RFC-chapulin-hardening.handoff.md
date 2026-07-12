# RFC — chapulin consumer-hardening — handoff

- **Stage:** 1 DONE (RFC drafted + sliced) → entering **Stage 2 (architect)**   •   **Round:** —
- **Resume:** `/architect docs/RFC-chapulin-hardening.md round 1`  (then round 2).
  Do NOT `/tdd` before both architect rounds land. Good `/compact` point now.
- **Verified finding set:** consolidated in session scratch `verify_results.md`
  (4 agents, all findings re-checked @ 99fa2db). RFC reflects it.
- **★ Key architectural insight for the architect rounds:** hard dependency
  **SND-1 ≺ CR-1/CR-2** — the crash-degrade work must NOT ship before the
  mkUnsupported-statement soundness fix, else it trades visible crashes for silent
  false-`sxSat` (worse under Invariant 3). SND-1 amends ADR-0012 D2 precedence.
- **Biggest scope changes from verification:** #5/#11/#7-symptom/pred/succ/`..<`
  HEALED (dropped); #3/#9 narrowed; SH1 does-not-repro (deferred); **NEW CRIT
  soundness bug SND-1** found (silent mis-mutation → false sxSat, general).

## Scope decision (Corey, 2026-07-12)
**ONE mega-RFC covering ALL chapulin findings**, across every subsystem (symex
walker/parser/solver + fuzz + shrinker + coverage). Corey chose this over the
recommended "symex-RFC + route-the-rest" split. Mitigation for coherence: the
single doc is organized into **per-subsystem clusters** (Phase-15/16 cluster
style), each independently sliceable. Unifying thesis: *everything chapulin's
v1/v2 verification harness surfaced*, with the §0 "walker never crashes /
Invariant-3 totality" invariant as the marquee cross-cutting cluster.

Source findings: `/mnt/c/Users/corey/projects/chapulin/docs/proptest-findings.md`
(pinned at proptest `99fa2db` = current HEAD; `file:line` refs align).

## Prerequisite: verify-at-HEAD pass (IN PROGRESS)
Some findings are already HEALED by A7/A8/A9 (confirmed pre-fan-out: #7's
`toLowerAscii` symptom works now; #3 bitwise-plain-int doesn't repro in the
simple shape). Don't slice healed work. Four background verification agents
(sonnet, verify-only, no fixes) each re-check a cluster and return a
LIVE/HEALED/PARTIAL table with evidence + fix locus + size:
- **A** — §1 walker crashes: #3, #4, #5, #11. (Known: #4 KeyError = LIVE-CRASH.)
- **B** — §2 model gaps: #1 seq[byte] reader, #7 toLower/probeProto, #8 rfind,
  #10 string.add, parseBiggestInt, min/max.
- **C** — §3 parser (#2 tupleConstr, objConstr, seq-slice, pred) + §4 solver
  (#6 dependent loops, #9 loop+string-param, symexAssume==symexAssert).
- **D** — §5 fuzz/corpus/DB, §6 coverage, §7 shrinker Int128 compile bug.

## Confirmed-live so far (pre-verification spot-checks)
- **#4** implicit tail-return referencing a local → uncaught `KeyError` at
  `runtime.nim:2629` (`env[e.vname]`), native crash. **LIVE-CRASH.** Flagship of
  the §0 "walker never crashes" invariant.
- **#7** symptom HEALED (A9), but a real latent bug remains: `probeProto`
  (`runtime.nim:1763` `StrOpKinds - {...}` catch-all) returns `none` for the
  A7/A8/A9 string ops (`iekStrToLower/Upper`, `iekRadixFmt`, `iekRuneToStr`) —
  missing from its modeled subset. Masked by a lowering fallback today.

## Open forks (awaiting Corey)
- (none blocking — scope decided; drafting proceeds after verification)

## Key decisions (this session)
- Mega-RFC scope (above). • Verify-at-HEAD before drafting (drop healed findings).
- Non-symex findings STAY in this RFC (per mega-RFC choice) as their own clusters,
  rather than routing fuzz→FUZZ_PLAN.

## Review ledger (stage 4) — not started
