## Round-6 N16 — closure/lambda zero-default result binding, walker v96.
##
## ---- Root cause ------------------------------------------------------
## R2 (walker v90, `tests/tsymex_r6_r2_zerodefault_result.nim`) fixed the
## `isCall` arm's implicit-fallthrough binding: a NAMED-proc callee path that
## never touches `result` at all (legal Nim -- `result` starts life
## zero-initialized) is bound to `defaultZero(stmt.retTy, ...)` instead of
## being left totally free.
##
## `applyClosureGround` (the SHARED implementation for direct closure/lambda
## calls -- `lowerClosureCall` -- AND the C4 HOF inline path, map/filter/fold)
## has the EXACT SAME shape of gap, and was never given R2's fix. Its
## fallThrough loop (runtime.nim, "(b) implicit result") only asserts a
## ground axiom binding `funcApp` when the sub-path's env contains "result":
##
##   for cp in fallThrough:
##     if cp.env.hasKey("result"):
##       assertArm(cp.pc, retBindEq(funcApp, cp.env["result"]))
##
## There was no `else` twin -- a fall-through closure-body path that never
## assigns `result` leaves `funcApp` COMPLETELY UNCONSTRAINED on that path,
## so the solver is free to pick ANY value there: a false `sxSat` with a
## non-replaying witness (the same v86-reintroduction shape R2 killed for
## the named-call boundary). The A6-rider commit's comment claiming
## `applyClosureGround` "already handles this exact shape correctly" was
## FALSE -- it never had an else-twin at all.
##
## ---- Fix ---------------------------------------------------------------
## Mirror R2's `isCall`-arm else-twin exactly inside `applyClosureGround`'s
## fallThrough loop: when `cp.env` lacks "result", bind `funcApp` to
## `defaultZero(cb.retTy, ...)` via the same `retBindEq`/`assertArm`
## machinery, under that path's own `cp.pc`. Reuses the module-level
## `defaultZero` (no parallel constructor). A closure retTy that hits one of
## `defaultZero`'s unsupported kinds (float, nested variant, distinct,
## ref/ptr, ...) classified-declines (`sxUnknown`), exactly like R2's
## `isCall` twin -- never binds a wrong value, never crashes.
##
## ---- Version discipline --------------------------------------------------
## Verdict-affecting (a previously-false `sxSat` now correctly reports
## `sxUnsat`/`sxUnknown`): `symexWalkerVersion` bumps 95->96.
## `renderAsChoicesVersion` stays UNCHANGED (11) -- no new witness-rendering
## shape.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# 1. Direct closure call, int retTy -- the S3 shape through `applyClosureGround`
#    instead of the named-call `isCall` arm. `f`'s `y <= 0` path never touches
#    `result` at all.
# =============================================================================

proc zeroIfNonPositiveInt(y: int): int =
  ## Real-semantics twin of the lambda body below, used for witness replay
  ## (the lambda itself is only reachable inside the SUT closures).
  if y > 0:
    result = y

proc sutClosureIntZeroSat(x: int) =
  let f = proc(y: int): int =
    if y > 0:
      result = y
  let r = f(x)
  if x <= 0 and r == 0:
    symexTarget("closure_int_zero_sat")

proc sutClosureIntFalseSat42(x: int) =
  ## Pre-fix: `r` is free on the `x <= 0` path -> Z3 satisfies `r == 42`
  ## trivially -> FALSE sxSat, witness does not replay. Post-fix: sxUnsat.
  let f = proc(y: int): int =
    if y > 0:
      result = y
  let r = f(x)
  if x <= 0 and r == 42:
    symexTarget("closure_int_false_sat_42")

proc sutClosureIntAssignedSat(x: int) =
  ## Regression companion: the ASSIGNED branch (x > 0) is unaffected.
  let f = proc(y: int): int =
    if y > 0:
      result = y
  let r = f(x)
  if x > 0 and r == x:
    symexTarget("closure_int_assigned_sat")

suite "symex round-6 N16 — direct closure call: untouched-result path binds to zero (int)":

  test "N16-1a: r == 0 on the untouched (x <= 0) path is reachable (sxSat), witness replays":
    let r = symexFind(sutClosureIntZeroSat, tLabel("closure_int_zero_sat"))
    check r.status == sxSat
    check r.witness[0] <= 0
    check zeroIfNonPositiveInt(r.witness[0]) == 0

  test "N16-1b: r == 42 on the untouched path is UNREACHABLE (sxUnsat), not a false sxSat":
    let r = symexFind(sutClosureIntFalseSat42, tLabel("closure_int_false_sat_42"))
    check r.status == sxUnsat

  test "N16-1c: regression -- the assigned branch (x > 0, r == x) still proves sxSat":
    let r = symexFind(sutClosureIntAssignedSat, tLabel("closure_int_assigned_sat"))
    check r.status == sxSat
    check r.witness[0] > 0
    check zeroIfNonPositiveInt(r.witness[0]) == r.witness[0]

# =============================================================================
# 2. C4 HOF inline path (map over a concrete-length seq) -- the SAME
#    `applyClosureGround` implementation, reached through the HOF dispatch
#    instead of `lowerClosureCall`.
#
#    HONEST DECLINE, NOT THIS SLICE'S BUG: applying a CONDITIONAL-body
#    closure through the inline map path hits a PRE-EXISTING, UNRELATED
#    defect -- confirmed via `tests/tsymex_phase15_C4_hof.nim`'s own C4-1
#    (filter)/C4-1b (map), which fail IDENTICALLY at this exact pre-fix HEAD
#    (stash-verified: same failures present with none of this slice's
#    changes applied). The inline map/filter construction raises a Z3
#    sort-mismatch exception ("domain sort (_ BitVec 64) and parameter sort
#    Bool do not match"), classified to sxUnknown (`ekZ3Error`) BEFORE
#    `applyClosureGround`'s fallThrough loop (this slice's fix target) can
#    even be exercised for a conditional body. Pinned honestly as a
#    classified decline, not chased -- out of scope for N16.
# =============================================================================

proc sutHofMapIntZeroSat(a: int) =
  var xs: seq[int] = @[]
  xs.add a
  let ys = xs.map(proc(x: int): int =
    if x > 0:
      result = x)
  if a <= 0 and ys.len == 1 and ys[0] == 0:
    symexTarget("hof_map_int_zero_sat")

suite "symex round-6 N16 — C4 HOF inline path (map): pre-existing orthogonal decline, honestly pinned":

  test "N16-2: conditional-body closure through inline map classified-declines (sxUnknown, ekZ3Error) -- PRE-EXISTING (matches C4-1/C4-1b), not this slice's bug":
    let r = symexFind(sutHofMapIntZeroSat, tLabel("hof_map_int_zero_sat"))
    check r.status == sxUnknown
    var sawZ3Err = false
    for e in r.errors:
      if e.kind == ekZ3Error and e.severity == sevError:
        sawZ3Err = true
    check sawZ3Err

# =============================================================================
# 3. bool retTy variant (direct closure call).
# =============================================================================

proc trueIfPositiveBool(y: int): bool =
  if y > 0:
    result = true

proc sutClosureBoolZeroSat(x: int) =
  let f = proc(y: int): bool =
    if y > 0:
      result = true
  let r = f(x)
  if x <= 0 and r == false:
    symexTarget("closure_bool_zero_sat")

proc sutClosureBoolFalseSatTrue(x: int) =
  ## Pre-fix: `r` free on x <= 0 -> Z3 picks `true` -> FALSE sxSat.
  let f = proc(y: int): bool =
    if y > 0:
      result = true
  let r = f(x)
  if x <= 0 and r == true:
    symexTarget("closure_bool_false_sat_true")

suite "symex round-6 N16 — direct closure call: bool retTy zero-default (false)":

  test "N16-3a: r == false on the untouched path is reachable (sxSat)":
    let r = symexFind(sutClosureBoolZeroSat, tLabel("closure_bool_zero_sat"))
    check r.status == sxSat
    check r.witness[0] <= 0
    check trueIfPositiveBool(r.witness[0]) == false

  test "N16-3b: r == true on the untouched path is UNREACHABLE (sxUnsat)":
    let r = symexFind(sutClosureBoolFalseSatTrue, tLabel("closure_bool_false_sat_true"))
    check r.status == sxUnsat

# =============================================================================
# 4. string retTy variant (direct closure call).
#
#    HONEST DECLINE, NOT THIS SLICE'S BUG: `symValFromRawAst` (runtime.nim,
#    ~8213-8239 -- the funcApp CONSTRUCTION step, reached at line ~8321
#    BEFORE the fallThrough loop this slice fixes) only wraps a closure's
#    ground application for `itInt`/`itBool`/`itFloat32`/`itFloat64` --
#    ANY string (or other unlisted) closure retTy raises `ValueError`
#    unconditionally, for BOTH the assigned and untouched paths alike. This
#    is a strictly PRE-EXISTING, orthogonal gap (closures cannot return
#    `string` AT ALL today, regardless of whether `result` was ever
#    touched) -- confirmed by direct probe against this exact pre-fix HEAD.
#    Out of scope for N16 (which only concerns the fallThrough loop's
#    missing else-twin); pinned here as an honest classified decline so a
#    future slice widening `symValFromRawAst` has a regression guard, and
#    so this slice's own honesty about R2's "bool/string" red set is not
#    silently swept under an untested gap.
# =============================================================================

proc sutClosureStringZeroSat(x: int) =
  let f = proc(y: int): string =
    if y > 0:
      result = "hit"
  let r = f(x)
  if x <= 0 and r == "":
    symexTarget("closure_string_zero_sat")

suite "symex round-6 N16 — direct closure call: string retTy, pre-existing orthogonal decline honestly pinned":

  test "N16-4: string-returning closure classified-declines (sxUnknown, weInternalWalkerFault) -- PRE-EXISTING (symValFromRawAst has no itString arm), not this slice's bug":
    let r = symexFind(sutClosureStringZeroSat, tLabel("closure_string_zero_sat"))
    check r.status == sxUnknown
    var sawFault = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault and e.severity == sevError:
        sawFault = true
    check sawFault

# =============================================================================
# 5. Soundness: multi-arm closure body, union of {1, -1, 0} exhaustive --
#    no spurious value reachable at all (stronger UNSAT companion than a
#    single impossible-literal check).
# =============================================================================

proc sutClosureExhaustive(x: int) =
  symexAssume(x >= -1000 and x <= 1000)
  let f = proc(y: int): int =
    if y > 0:
      result = 1
    elif y < 0:
      result = -1
    # y == 0: untouched -> implicit zero default.
  let r = f(x)
  if r != 1 and r != -1 and r != 0:
    symexTarget("closure_exhaustive_impossible")

suite "symex round-6 N16 — soundness: closure result union {1, -1, 0} is exhaustive":

  test "N16-5: no value outside {1, -1, 0} is ever reachable (sxUnsat)":
    let r = symexFind(sutClosureExhaustive, tLabel("closure_exhaustive_impossible"))
    check r.status == sxUnsat

# =============================================================================
# Version pins
# =============================================================================

suite "symex round-6 N16 — version pins":

  test "walker version floor >= 96 (soundness fix -- closure zero-default result binding)":
    check parseInt(symexWalkerVersion) >= 96

  test "renderAsChoicesVersion floor >= 11 (no new witness shape this slice)":
    check parseInt(renderAsChoicesVersion) >= 11
