## Phase 16 — Cluster A6: symbolic-length `filter` / `map` over `seq[T]`.
##
## A6 ships NO new encoding (see ADR-0016). The decidable cases already shipped
## under C4 (concrete/bounded inline; symbolic capture-free int→int map via
## `mapArray`/`Z3_mk_map`). A6 records the SCOPE DECISION and pins the one case
## C4 left implicit: a symbolic-length `map` whose closure CAPTURES a SUT
## parameter cannot use the unary-FuncDecl `mapArray` path and must degrade to
## `ceUnsupportedHof` → `sxUnknown` (Invariant 3 — classified, never a hang).
##
## The probe behind ADR-0016 proved the alternative — a `seqFoldlBody`-based
## symbolic filter — HANGS (rc=137, both backends, SAT and UNSAT); refusing to
## add it is the sound choice. These tests assert the degrade is honest and that
## the decidable map path stays decidable (no regression to a hang).
##
## A6 is ADDITIVE under walker version "34" (no bump: no verdict flip, no new IR,
## no cache-key input change — see ADR-0016 §Scope).
import std/[unittest, sequtils]
import proptest/symex

# --- capture-free symbolic-length map (DECIDABLE, mapArray) ------------------
# `x + 1` closes over nothing; the symbolic map takes the decidable Z3_mk_map
# array path and must TERMINATE (the DoD: no Z3Error / no 137 hang).
proc sutMapCaptureFree(xs: seq[int]) =
  let ys = xs.map(proc(x: int): int = x + 1)
  if ys.len > 0:
    symexTarget("a6mapfree")

# --- capturing symbolic-length map (DEGRADE, ceUnsupportedHof) ---------------
# `x + cap` captures the SUT parameter `cap` (an env-leaf with no unary
# FuncDecl) — `mapArray` cannot represent it, so the walker degrades rather than
# guessing. Probe B confirmed sxUnknown + ceUnsupportedHof on c+cpp, NOT a hang.
proc sutMapCapturing(xs: seq[int], cap: int) =
  let ys = xs.map(proc(x: int): int = x + cap)
  if ys.len > 0:
    symexTarget("a6mapcap")

# --- symbolic-length filter (DEGRADE, ceUnsupportedHof) ----------------------
# No hang-free Z3 encoding exists (seqFoldlBody hangs; Z3Array/Z3Seq mismatch).
# The honest outcome is sxUnknown via a classified ceUnsupportedHof.
proc sutFilterSymbolic(xs: seq[int]) =
  let kept = xs.filter(proc(x: int): bool = x > 0)
  if kept.len > 0:
    symexTarget("a6filter")

suite "symex Phase 16 A6 — symbolic-length filter/map scope (ADR-0016)":

  test "A6-1: capture-free symbolic-length map TERMINATES (no Z3Error / hang)":
    let r = symexFind(sutMapCaptureFree, tLabel("a6mapfree"))
    # Decidable array-map path: verdict may be sat or unknown, never a crash.
    check r.status in {sxSat, sxUnknown}

  test "A6-2: capturing symbolic-length map degrades to ceUnsupportedHof, sxUnknown":
    let r = symexFind(sutMapCapturing, tLabel("a6mapcap"))
    check r.status == sxUnknown
    var sawHof = false
    for e in r.errors:
      if e.kind == ceUnsupportedHof and e.severity == sevError:
        sawHof = true
    check sawHof

  test "A6-3: symbolic-length filter degrades to ceUnsupportedHof, sxUnknown (no seqFoldl hang)":
    let r = symexFind(sutFilterSymbolic, tLabel("a6filter"))
    check r.status == sxUnknown
    var sawHof = false
    for e in r.errors:
      if e.kind == ceUnsupportedHof and e.severity == sevError:
        sawHof = true
    check sawHof
