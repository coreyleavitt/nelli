## Round-6 A3 — `isVariantConstructSym`: fork-per-tag SYMBOLIC-discriminant
## variant construction.
##
## ADR-0029 (`docs/SYMEX_PLAN.md`). A1 (walker v75) landed `iekVariantLit`
## (literal-discriminant construction, a value-producing expression); A2
## (walker v76) wired `retBindEq`'s general svVariant encoding. A3 is the
## remaining Track-A construction gap ADR-0029 named up front: a SYMBOLIC
## discriminant (the consumer corpus's `protocol.nim:166` shape —
## `TftpPacket(opcode: op, ...)` with `op` branch-bounded to a small tag
## set) forks ONE PATH PER FEASIBLE TAG, cloning the LANDED
## `isVariantReassignSymbolic` fork-per-tag precedent (`runtime.nim`
## ~6379 pre-round-6) with one deliberate divergence: construction has no
## "active arm" data to preserve (Nim itself only accepts a non-constant
## discriminant in constructor syntax when NO arm-specific field is set),
## so EVERY declared arm's fields allocate FRESH, independently, IN EACH
## FORK.
##
## New capability: `maxVariantConstructorForks` (default 8, own
## `ResourceBudget` field) — a STRUCTURAL cap on the feasible tag-set size,
## checked BEFORE any solver work; past it, a classified `beBudgetExhausted`
## decline (never a crash, never an unbounded fork explosion for a wide
## unconstrained enum). Parse-time `case`-branch tag-set NARROWING (lexical,
## per-proc-body, never crossing a call boundary — a helper-proc-per-arm
## refactor gets the full declared-arm-count fork cost) lets a wide enum
## narrowed to <= budget construct instead of declining.
##
## Bumps `symexWalkerVersion` 76->77: verdict-surface change (previously
## `sxUnknown` symbolic-disc constructions now resolve to real `sxSat`/
## `sxUnsat` below budget, or a classified decline at/above it).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

# ---------------------------------------------------------------------------
# SUTs — two-tag shape (protocol.nim:166 replica: a two-tag variant built
# from a symbolic byte's comparison)
# ---------------------------------------------------------------------------

type
  Op = enum opRrq, opWrq
  TwoTagPkt = object
    tag: int                       ## plain field, shared across arms — the
                                    ## ONLY kind of field Nim itself accepts
                                    ## alongside a non-constant discriminant
    case opcode: Op
    of opRrq: rq: int
    of opWrq: wq: int

# --- Test 1: tracer — symbolic disc built from a byte comparison;
# constraint picks ONE tag's arm-field -> sxSat with witness including the
# driving discriminant value (b==1, the only byte value that selects
# opRrq). --------------------------------------------------------------
proc sutTracer(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = TwoTagPkt(opcode: op, tag: n)
  if p.opcode == opRrq and p.rq == 777:
    symexTarget("tracer_rrq_rq777")

# --- Test 2: UNSAT companion — soundness, not a free/unconstrained fork.
# `op == opRrq` can ONLY hold when `b == 1'u8` (the if-expr that built it);
# asserting BOTH is a contradiction the fork's own `disc == tag` path
# constraint must catch. -------------------------------------------------
proc sutUnsatCompanion(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = TwoTagPkt(opcode: op, tag: n)
  if p.opcode == opRrq and b != 1'u8:
    symexTarget("unsat_rrq_but_b_not_1")

# --- Test 3: fork-per-tag observable — constraints distinguishing the two
# forks are BOTH independently reachable. --------------------------------
proc sutForkRrqObservable(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = TwoTagPkt(opcode: op, tag: n)
  if p.opcode == opRrq and p.tag == 10:
    symexTarget("fork_rrq_tag10")

proc sutForkWrqObservable(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = TwoTagPkt(opcode: op, tag: n)
  if p.opcode == opWrq and p.tag == 20:
    symexTarget("fork_wrq_tag20")

# --- Test 4: fresh inactive-arm fields PER FORK — the dedicated divergence
# from `isVariantReassignSymbolic` (which PRESERVES fields; construction has
# nothing to preserve, so every arm's field is a fresh, independent free
# variable per fork). A field reachable at 777 AND, independently, at 0
# proves it is genuinely FREE — neither zero-forced (the static-tag
# `isVariantReassign` precedent) nor pinned to any single carried value.
# The OTHER fork's own arm field is independently free too. --------------
proc sutFreshFieldNonzero(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = TwoTagPkt(opcode: op, tag: n)
  if p.opcode == opRrq and p.rq == 777:
    symexTarget("fresh_rq_777")

proc sutFreshFieldZero(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = TwoTagPkt(opcode: op, tag: n)
  if p.opcode == opRrq and p.rq == 0:
    symexTarget("fresh_rq_zero")

proc sutFreshFieldOtherFork(b: byte, n: int) =
  let op = if b == 1'u8: opRrq else: opWrq
  let p = TwoTagPkt(opcode: op, tag: n)
  if p.opcode == opWrq and p.wq == 555:
    symexTarget("fresh_wq_555")

# ---------------------------------------------------------------------------
# SUTs — wide (10-tag) shape: exceeds the default budget (8) unless
# parse-time `case`-branch narrowing brings the feasible set under it.
# ---------------------------------------------------------------------------

type
  WideTag = enum wt0, wt1, wt2, wt3, wt4, wt5, wt6, wt7, wt8, wt9
  WideObj = object
    tag: int
    case kind: WideTag
    of wt0: f0: int
    of wt1: f1: int
    of wt2: f2: int
    of wt3: f3: int
    of wt4: f4: int
    of wt5: f5: int
    of wt6: f6: int
    of wt7: f7: int
    of wt8: f8: int
    of wt9: f9: int

# --- Test 5: parse-time tag-set narrowing — the constructor sits inside a
# `case op of wt0, wt1:` branch. WITHOUT narrowing the declared arm count
# (10) exceeds the default budget (8) and this would classify-decline; WITH
# narrowing the feasible set is {wt0, wt1} (size 2), well under budget, so
# construction proceeds to a real verdict. ------------------------------
proc sutNarrowedWt0Hit(b: byte, n: int) =
  let op = if b == 1'u8: wt0 else: wt1
  case op
  of wt0, wt1:
    let p = WideObj(kind: op, tag: n)
    if p.kind == wt0 and p.tag == 5:
      symexTarget("narrowed_wt0_hit")
  else:
    discard

proc sutNarrowedWt1Hit(b: byte, n: int) =
  let op = if b == 1'u8: wt0 else: wt1
  case op
  of wt0, wt1:
    let p = WideObj(kind: op, tag: n)
    if p.kind == wt1 and p.tag == 6:
      symexTarget("narrowed_wt1_hit")
  else:
    discard

# --- Test 6: budget-exceeded decline — the SAME wide enum, constructed at
# TOP LEVEL (no enclosing `case` to narrow it), so the full declared arm
# count (10) applies and exceeds the default budget (8). Must classify
# `sxUnknown` (never a crash), and the decline message must carry
# file:line:col + the construct's `n.repr` (the parse-time `vcsLoc`
# rendered verbatim at walk time — no `NimNode` exists at the walk-time
# budget check). ----------------------------------------------------------
proc sutBudgetExceeded(b: byte, n: int) =
  let op = if b == 1'u8: wt0 else: wt1
  let p = WideObj(kind: op, tag: n)
  if p.tag == 5:
    symexTarget("budget_exceeded_reached")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex round-6 A3 — isVariantConstructSym tracer + soundness":

  test "A3-1: tracer — symbolic-disc construction, one tag's arm-field constrained -> sxSat, witness b==1":
    let res = symexFind(sutTracer, tLabel("tracer_rrq_rq777"))
    check res.status == sxSat
    check res.witness[0] == 1'u8

  test "A3-2: UNSAT companion — op==opRrq forces b==1'u8, so b!=1'u8 in the same conjunction is impossible":
    let res = symexFind(sutUnsatCompanion, tLabel("unsat_rrq_but_b_not_1"))
    check res.status == sxUnsat

suite "symex round-6 A3 — fork-per-tag observable":

  test "A3-3a: the opRrq fork is independently reachable":
    let res = symexFind(sutForkRrqObservable, tLabel("fork_rrq_tag10"))
    check res.status == sxSat
    check res.witness[1] == 10

  test "A3-3b: the opWrq fork is ALSO independently reachable":
    let res = symexFind(sutForkWrqObservable, tLabel("fork_wrq_tag20"))
    check res.status == sxSat
    check res.witness[1] == 20

suite "symex round-6 A3 — fresh inactive-arm fields PER FORK (dedicated divergence pin)":

  test "A3-4a: the active fork's arm field reaches a nonzero value — not zero-forced":
    let res = symexFind(sutFreshFieldNonzero, tLabel("fresh_rq_777"))
    check res.status == sxSat

  test "A3-4b: the SAME fork's arm field independently reaches zero too — genuinely free, not pinned":
    let res = symexFind(sutFreshFieldZero, tLabel("fresh_rq_zero"))
    check res.status == sxSat

  test "A3-4c: the OTHER fork's own arm field is independently fresh too":
    let res = symexFind(sutFreshFieldOtherFork, tLabel("fresh_wq_555"))
    check res.status == sxSat

suite "symex round-6 A3 — parse-time case-branch tag-set narrowing":

  test "A3-5a: a 10-tag enum narrowed under `case op of wt0, wt1:` constructs (not a budget decline) — wt0 arm reachable":
    let res = symexFind(sutNarrowedWt0Hit, tLabel("narrowed_wt0_hit"))
    check res.status == sxSat
    check res.witness[1] == 5

  test "A3-5b: the OTHER narrowed tag (wt1) is independently reachable too":
    let res = symexFind(sutNarrowedWt1Hit, tLabel("narrowed_wt1_hit"))
    check res.status == sxSat
    check res.witness[1] == 6

suite "symex round-6 A3 — maxVariantConstructorForks budget-exceeded decline":

  test "A3-6: the SAME 10-tag enum, UNNARROWED (top-level construction) -> classified sxUnknown, never sxSat/crash":
    let res = symexFind(sutBudgetExceeded, tLabel("budget_exceeded_reached"))
    check res.status == sxUnknown
    check res.status != sxSat
    var hasClassified = false
    var msg = ""
    for e in res.errors:
      if e.kind == beBudgetExhausted and e.severity == sevError:
        hasClassified = true
        msg = e.msg
    check hasClassified
    # Walk-time loc discipline: file:line:col + n.repr, carried verbatim
    # from the parse-time `vcsLoc` field (no NimNode exists at walk time).
    check "tsymex_r6_a3_variantconstruct_sym.nim" in msg
    check "WideObj" in msg
    check "maxVariantConstructorForks" in msg

suite "symex round-6 A3 — cache-key wiring":

  test "maxVariantConstructorForks participates in the settings cache key":
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxVariantConstructorForks = s0.budget.maxVariantConstructorForks + 1
    check canonicalize(s0) != canonicalize(s1)

suite "symex round-6 A3 — walker version pin":

  test "walker version floor >= 77 (isVariantConstructSym fork-per-tag construction with budget)":
    check parseInt(symexWalkerVersion) >= 77
