## Round-6 review N9 — `isVariantConstructSym` PER-FORK field-allocation
## budget.
##
## Finding (round-6 review, Medium): the A3 (ADR-0029) fork-per-tag
## SYMBOLIC-discriminant variant CONSTRUCTOR caps only the OUTER tag-fork
## loop via `maxVariantConstructorForks` (checked against `vcsTagSet.len`).
## Inside EACH per-tag fork, field allocation walks EVERY declared arm of
## the variant type — construction has no "active arm" to narrow to (Nim
## itself only accepts a non-constant discriminant in constructor syntax
## when no arm-specific field is set), so the walker allocates FRESH
## fields for ALL arms, unconditionally, in EACH fork (`runtime.nim`'s
## `isVariantConstructSym` doc comment). The fork-count budget alone does
## nothing to bound a wide-FIELDED variant: a fork count comfortably under
## budget can still amplify allocation work by (forks x total-arm-fields),
## with zero accounting.
##
## Fix: a new `maxVariantConstructorFieldAllocs` structural budget
## (default `64`, own `ResourceBudget` field), checked STRUCTURALLY
## (before any solver work, same timing/style as the existing fork-count
## check) against `vcsTagSet.len * (sum of fieldTypes.len across every
## declared arm)`. Past it, the SAME `beBudgetExhausted` classified
## decline kind the fork-count budget already uses (SND-4 "mirror, don't
## reinvent" — not a parallel mechanism). The existing fork-count check
## runs FIRST, unchanged, so every already-pinned A3 shape resolves to the
## identical verdict as before this slice.
##
## Bumps `symexWalkerVersion` 93->94: verdict-surface change — a shape
## whose fork count is within `maxVariantConstructorForks` but whose total
## per-fork field-allocation count exceeds the new
## `maxVariantConstructorFieldAllocs` now classifies a decline where it
## previously proceeded to unaccounted-for allocation work.
##
## Honesty note on RED construction: this finding is a resource-
## exhaustion/perf concern, not a soundness bug — pre-fix, the wide-
## fielded shape below does not crash or hang, it PROCEEDS to real
## (unbudgeted) allocation work and returns a genuine verdict. There is no
## observable WRONG answer to pin as a classic RED. What IS observable and
## countable is the verdict-kind flip this slice produces: pre-fix
## `sutWideFieldsBudget` resolves to `sxSat` (confirmed by manually
## reverting `runtime.nim`/`types.nim`/`canonicalize.nim` and re-running
## this proc in isolation before writing this pin); post-fix, the SAME
## shape classifies `beBudgetExhausted` instead — the amplification is
## real (512 fresh Z3 allocations for a fork count the budget doctrine
## says should cost 8), just not observable as a crash/hang on this
## input size. Test 1 below pins the POST-fix decline; the pre-fix sxSat
## behavior is reported in the fix-slice summary, not faked as a RED here.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

# ---------------------------------------------------------------------------
# SUT — wide-FIELDED variant: fork count (8) sits AT the
# `maxVariantConstructorForks` default (8), so the PRE-EXISTING fork-count
# check alone does NOT decline this shape. But 8 declared arms x 8 fields
# each gives a per-fork field-allocation total of 8 (forks) x 64
# (fields-across-all-arms) = 512, well past the new
# `maxVariantConstructorFieldAllocs` default (64) — exactly the
# amplification this slice fixes.
# ---------------------------------------------------------------------------

type
  WFTag = enum wf0, wf1, wf2, wf3, wf4, wf5, wf6, wf7
  WideFieldsObj = object
    tag: int
    case kind: WFTag
    of wf0: a00, a01, a02, a03, a04, a05, a06, a07: int
    of wf1: a10, a11, a12, a13, a14, a15, a16, a17: int
    of wf2: a20, a21, a22, a23, a24, a25, a26, a27: int
    of wf3: a30, a31, a32, a33, a34, a35, a36, a37: int
    of wf4: a40, a41, a42, a43, a44, a45, a46, a47: int
    of wf5: a50, a51, a52, a53, a54, a55, a56, a57: int
    of wf6: a60, a61, a62, a63, a64, a65, a66, a67: int
    of wf7: a70, a71, a72, a73, a74, a75, a76, a77: int

proc sutWideFieldsBudget(b: byte, n: int) =
  let op = if b == 1'u8: wf0 else: wf1
  let p = WideFieldsObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("wide_fields_budget_reached")

# ---------------------------------------------------------------------------
# SUTs — within-budget shapes keep their EXACT prior verdicts (SAT witness
# + UNSAT companion). Mirrors A3's own tracer/companion pair (own local
# types, avoiding a cross-test-file type import); fieldAllocs = 2 forks x
# 2 fields-across-both-arms = 4, far under the new default (64) — this
# slice's new check must be a no-op for this shape.
# ---------------------------------------------------------------------------

type
  Op2 = enum op2Rrq, op2Wrq
  TwoTagPkt2 = object
    tag: int
    case opcode: Op2
    of op2Rrq: rq: int
    of op2Wrq: wq: int

proc sutWithinBudgetTracer(b: byte, n: int) =
  let op = if b == 1'u8: op2Rrq else: op2Wrq
  let p = TwoTagPkt2(opcode: op, tag: n)
  if p.opcode == op2Rrq and p.rq == 777:
    symexTarget("n9_within_budget_sat")

proc sutWithinBudgetUnsatCompanion(b: byte, n: int) =
  let op = if b == 1'u8: op2Rrq else: op2Wrq
  let p = TwoTagPkt2(opcode: op, tag: n)
  if p.opcode == op2Rrq and b != 1'u8:
    symexTarget("n9_within_budget_unsat")

# ---------------------------------------------------------------------------
# SUTs — budget-boundary: exactly AT `maxVariantConstructorFieldAllocs`
# (64) constructs (the check is strict `>`, not `>=`); one field over
# declines.
# ---------------------------------------------------------------------------

type
  BTag4 = enum bt0, bt1, bt2, bt3
  BoundaryAt64 = object
    tag: int
    case kind: BTag4
    of bt0: c00, c01, c02, c03: int
    of bt1: c10, c11, c12, c13: int
    of bt2: c20, c21, c22, c23: int
    of bt3: c30, c31, c32, c33: int

proc sutBoundaryAtBudget(b: byte, n: int) =
  let op = if b == 1'u8: bt0 else: bt1
  let p = BoundaryAt64(kind: op, tag: n)
  if p.tag == 9:
    symexTarget("n9_boundary_at_budget")

type
  BTag4b = enum bu0, bu1, bu2, bu3
  BoundaryOver64 = object
    tag: int
    case kind: BTag4b
    of bu0: d00, d01, d02, d03, d04: int
    of bu1: d10, d11, d12, d13, d14: int
    of bu2: d20, d21, d22, d23, d24: int
    of bu3: d30, d31, d32, d33, d34: int

proc sutBoundaryOverBudget(b: byte, n: int) =
  let op = if b == 1'u8: bu0 else: bu1
  let p = BoundaryOver64(kind: op, tag: n)
  if p.tag == 9:
    symexTarget("n9_boundary_over_budget")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex round-6 N9 — variant constructor field-allocation budget":

  test "N9-1: wide-fielded variant (forks=8 <= fork budget, fields=512 > field budget) declines honestly":
    let res = symexFind(sutWideFieldsBudget, tLabel("wide_fields_budget_reached"))
    check res.status == sxUnknown
    check res.status != sxSat
    var hasClassified = false
    var msg = ""
    for e in res.errors:
      if e.kind == beBudgetExhausted and e.severity == sevError:
        hasClassified = true
        msg = e.msg
    check hasClassified
    check "tsymex_r6_n9_variant_budget.nim" in msg
    check "WideFieldsObj" in msg
    check "maxVariantConstructorFieldAllocs" in msg

suite "symex round-6 N9 — within-budget variants keep exact prior verdicts":

  test "N9-2a: SAT witness unchanged — b==1 is still the only driving value":
    let res = symexFind(sutWithinBudgetTracer, tLabel("n9_within_budget_sat"))
    check res.status == sxSat
    check res.witness[0] == 1'u8

  test "N9-2b: UNSAT companion unchanged — op==op2Rrq still forces b==1'u8":
    let res = symexFind(sutWithinBudgetUnsatCompanion, tLabel("n9_within_budget_unsat"))
    check res.status == sxUnsat

suite "symex round-6 N9 — budget-boundary":

  test "N9-3a: exactly AT the field-allocation budget (4 forks x 16 fields = 64) constructs":
    let res = symexFind(sutBoundaryAtBudget, tLabel("n9_boundary_at_budget"))
    check res.status == sxSat
    check res.witness[1] == 9

  test "N9-3b: one field over the budget (4 forks x 20 fields = 80) declines":
    let res = symexFind(sutBoundaryOverBudget, tLabel("n9_boundary_over_budget"))
    check res.status == sxUnknown
    check res.status != sxSat
    var hasClassified = false
    for e in res.errors:
      if e.kind == beBudgetExhausted and e.severity == sevError:
        hasClassified = true
    check hasClassified

suite "symex round-6 N9 — cache-key wiring":

  test "maxVariantConstructorFieldAllocs participates in the settings cache key":
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxVariantConstructorFieldAllocs = s0.budget.maxVariantConstructorFieldAllocs + 1
    check canonicalize(s0) != canonicalize(s1)

suite "symex round-6 N9 — walker version pin":

  test "walker version floor >= 94 (isVariantConstructSym per-fork field-allocation budget)":
    check parseInt(symexWalkerVersion) >= 94
