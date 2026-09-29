## R2 (post-0.4.0 remediation slice) — zero-default result binding, S3,
## walker v90.
##
## ---- Root cause ------------------------------------------------------
## Round-6 A6-rider (walker v86, `tests/tsymex_r6_a6r_callwitness.nim`) fixed
## a false-`sxSat` generator: a callee reaching an IMPLICIT fallthrough (no
## explicit `return`) after CONDITIONALLY assigning `result` left the
## caller-side `retSym` totally unconstrained. The fix (`runtime.nim`'s
## `isCall` arm) binds `retSym` via `retBindEq` — but ONLY when
## `cp.env.hasKey("result")`, i.e. only when the path actually ASSIGNED
## `result` somewhere along the way. A callee path that never touches
## `result` AT ALL is equally legal Nim: `result` starts life
## zero-initialized (Nim zero-inits every `result` slot before the body
## runs — `0`, `""`, `false`, a zero-tuple, …) and stays that way if the
## path's own branch never assigns it. Example: `proc f(x: int): int = (if
## x > 0: result = x)` — the `x <= 0` path returns `0`, never touching
## `result` at all. Pre-fix, v86's `cp.env.hasKey("result")` guard routed
## such a path straight to the UNCHANGED `else: fallThrough.add cp` —
## `retSym` stayed exactly as free as it was before v86 existed,
## reintroducing v86's own false-`sxSat` shape for the never-touched case.
##
## ---- Fix ---------------------------------------------------------------
## `runtime.nim`'s `isCall` arm gains the `else` twin of v86's `if
## cp.env.hasKey("result")` branch: bind `retSym` to
## `defaultZero(stmt.retTy, ...)` — Phase 14 A5's (ADR-0003 D5) recursive
## type-driven zero-init, hoisted this slice from its former
## `isVariantReassign`-local scope to module scope so both call sites share
## the ONE constructor — via the same `retBindEq` the assigned branch
## already uses. Composite/unsupported return types `defaultZero`/
## `retBindEq` cannot zero-bind soundly (float, nested variant, distinct,
## ref/ptr, a genuinely-backed top-level `itSeq`, …) fall through to the
## SAME classified `sxUnknown` decline the assigned branch's
## `retVal.kind notin {...}` check already uses — never a bound wrong
## value, never a crash.
##
## ---- Version discipline --------------------------------------------------
## Verdict-affecting (a previously-false `sxSat` now correctly reports
## `sxUnsat`): `symexWalkerVersion` bumps 89→90. `renderAsChoicesVersion`
## stays UNCHANGED (11) — no new witness-rendering shape.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime

# =============================================================================
# 1. Tracer (the S3 shape). `maybeSetResult`'s `x <= 0` path never touches
#    `result` at all.
# =============================================================================

proc maybeSetResult(x: int): int =
  if x > 0:
    result = x

proc sutTracerZeroUntouchedUnreachable(x: int) =
  ## On the `x <= 0` path `result` is never assigned -> must be exactly 0.
  ## `r != 0 and x <= 0` is therefore UNREACHABLE under real semantics.
  ## Pre-fix: `retSym` free on this path -> Z3 satisfies `r != 0` trivially
  ## -> FALSE `sxSat`. Post-fix: `sxUnsat`.
  let r = maybeSetResult(x)
  if r != 0 and x <= 0:
    symexTarget("tracer_zero_untouched_unreachable")

suite "symex round-6 R2 — tracer: untouched-result path must bind to zero":

  test "T1: r != 0 on the untouched (x <= 0) path is UNREACHABLE (sxUnsat, not a false sxSat)":
    let r = symexFind(sutTracerZeroUntouchedUnreachable,
                       tLabel("tracer_zero_untouched_unreachable"))
    check r.status == sxUnsat

# =============================================================================
# 2. SAT companion: the ASSIGNED path (x > 0) still binds correctly (v86,
#    unaffected by this slice) -- regression guard + witness cross-check.
# =============================================================================

proc sutTracerAssignedSat(x: int) =
  let r = maybeSetResult(x)
  if x > 0 and r == x:
    symexTarget("tracer_assigned_sat")

suite "symex round-6 R2 — SAT companion: the assigned path":

  test "T2: the assigned path (x > 0, result == x) is reachable (sxSat), witness cross-checked":
    let r = symexFind(sutTracerAssignedSat, tLabel("tracer_assigned_sat"))
    check r.status == sxSat
    let x = r.witness[0]
    check x > 0
    check maybeSetResult(x) == x

# =============================================================================
# 3. Zero-path SAT: the query is satisfied EXACTLY by the zero default.
# =============================================================================

proc sutTracerZeroSat(x: int) =
  let r = maybeSetResult(x)
  if x <= 0 and r == 0:
    symexTarget("tracer_zero_sat")

suite "symex round-6 R2 — zero-path SAT":

  test "T3: the untouched path's implicit zero (x <= 0, result == 0) is reachable (sxSat)":
    let r = symexFind(sutTracerZeroSat, tLabel("tracer_zero_sat"))
    check r.status == sxSat
    check r.witness[0] <= 0
    check maybeSetResult(r.witness[0]) == 0

# =============================================================================
# 4. Multi-path: if/elif assigning result to different exprs + an implicit
#    untouched else. All three paths must bind correctly, and the union of
#    {assigned exprs, 0} must be exhaustive (at least one UNSAT pin).
# =============================================================================

proc triPathSign(x: int): int =
  if x > 0:
    result = 1
  elif x < 0:
    result = -1
  # x == 0: untouched -> implicit zero default.

proc sutTriPathPositive(x: int) =
  symexAssume(x >= -1000 and x <= 1000)
  let r = triPathSign(x)
  if x > 0 and r == 1:
    symexTarget("tripath_positive")

proc sutTriPathNegative(x: int) =
  symexAssume(x >= -1000 and x <= 1000)
  let r = triPathSign(x)
  if x < 0 and r == -1:
    symexTarget("tripath_negative")

proc sutTriPathZero(x: int) =
  symexAssume(x >= -1000 and x <= 1000)
  let r = triPathSign(x)
  if x == 0 and r == 0:
    symexTarget("tripath_zero")

proc sutTriPathExhaustive(x: int) =
  ## Soundness pin: `r` can ONLY ever be 1, -1, or 0 — if ANY of the three
  ## paths above left `retSym` free, Z3 could pick e.g. 999 here instead.
  symexAssume(x >= -1000 and x <= 1000)
  let r = triPathSign(x)
  if r != 1 and r != -1 and r != 0:
    symexTarget("tripath_exhaustive_impossible")

suite "symex round-6 R2 — multi-path: assigned arms + implicit untouched else":

  test "T4a: the x > 0 arm (assigned result = 1) is reachable (sxSat)":
    let r = symexFind(sutTriPathPositive, tLabel("tripath_positive"))
    check r.status == sxSat

  test "T4b: the x < 0 arm (assigned result = -1) is reachable (sxSat)":
    let r = symexFind(sutTriPathNegative, tLabel("tripath_negative"))
    check r.status == sxSat

  test "T4c: the x == 0 arm (untouched -> implicit result = 0) is reachable (sxSat)":
    let r = symexFind(sutTriPathZero, tLabel("tripath_zero"))
    check r.status == sxSat

  test "T4d: soundness -- the union {1, -1, 0} is exhaustive, no other value is reachable (sxUnsat)":
    let r = symexFind(sutTriPathExhaustive, tLabel("tripath_exhaustive_impossible"))
    check r.status == sxUnsat

# =============================================================================
# 5. String / bool / tuple return types the zero machinery DOES support --
#    pinned honest: both the zero-path SAT and the soundness (non-zero
#    unreachable on the untouched path) direction.
# =============================================================================

proc maybeSetBool(x: int): bool =
  if x > 0:
    result = true

proc sutBoolZeroSat(x: int) =
  let r = maybeSetBool(x)
  if x <= 0 and r == false:
    symexTarget("bool_zero_sat")

proc sutBoolZeroUnreachable(x: int) =
  let r = maybeSetBool(x)
  if x <= 0 and r == true:
    symexTarget("bool_zero_unreachable")

proc maybeSetString(x: int): string =
  if x > 0:
    result = "hit"

proc sutStringZeroSat(x: int) =
  let r = maybeSetString(x)
  if x <= 0 and r == "":
    symexTarget("string_zero_sat")

proc sutStringZeroUnreachable(x: int) =
  let r = maybeSetString(x)
  if x <= 0 and r == "hit":
    symexTarget("string_zero_unreachable")

proc maybeSetTuple(x: int): tuple[a: int, b: bool] =
  if x > 0:
    result = (a: x, b: true)

proc sutTupleZeroSat(x: int) =
  let r = maybeSetTuple(x)
  if x <= 0 and r.a == 0 and r.b == false:
    symexTarget("tuple_zero_sat")

proc sutTupleZeroUnreachable(x: int) =
  let r = maybeSetTuple(x)
  if x <= 0 and r.a == 999:
    symexTarget("tuple_zero_unreachable")

suite "symex round-6 R2 — supported zero-default return types (bool / string / tuple)":

  test "T5a: bool -- untouched path's implicit `false` is reachable (sxSat)":
    let r = symexFind(sutBoolZeroSat, tLabel("bool_zero_sat"))
    check r.status == sxSat

  test "T5b: bool -- `true` on the untouched path is UNREACHABLE (sxUnsat)":
    let r = symexFind(sutBoolZeroUnreachable, tLabel("bool_zero_unreachable"))
    check r.status == sxUnsat

  test "T5c: string -- untouched path's implicit \"\" is reachable (sxSat)":
    let r = symexFind(sutStringZeroSat, tLabel("string_zero_sat"))
    check r.status == sxSat

  test "T5d: string -- \"hit\" on the untouched path is UNREACHABLE (sxUnsat)":
    let r = symexFind(sutStringZeroUnreachable, tLabel("string_zero_unreachable"))
    check r.status == sxUnsat

  test "T5e: tuple -- untouched path's implicit (0, false) is reachable (sxSat)":
    let r = symexFind(sutTupleZeroSat, tLabel("tuple_zero_sat"))
    check r.status == sxSat

  test "T5f: tuple -- field a == 999 on the untouched path is UNREACHABLE (sxUnsat)":
    let r = symexFind(sutTupleZeroUnreachable, tLabel("tuple_zero_unreachable"))
    check r.status == sxUnsat

# -----------------------------------------------------------------------------
# 5b. A return type the zero machinery genuinely CANNOT back soundly (a
# variant object; float was the example until RFC-0005 S8f gave `defaultZero`
# its float arm) must
# classified-decline, never crash and never bind a wrong value. Assert
# kind + severity, the `bug2_scopeddecline` idiom.
# -----------------------------------------------------------------------------

proc maybeSetFloat(x: int): float64 =
  if x > 0:
    result = 1.5

proc sutFloatAssignedSat(x: int) =
  ## Regression: the ASSIGNED path (v86, unaffected by this slice) is
  ## unaffected by the untouched path's inability to zero-bind.
  let r = maybeSetFloat(x)
  if x > 0 and r == 1.5:
    symexTarget("float_assigned_sat")

proc sutFloatZeroDeclines(x: int) =
  let r = maybeSetFloat(x)
  discard r
  if x <= 0:
    symexTarget("float_zero_declines")

proc sutFloatZeroNonzero(x: int) =
  let r = maybeSetFloat(x)
  if x <= 0 and r != 0.0:
    symexTarget("float_zero_nonzero")

type
  R2VK = enum r2A, r2B
  R2V = object
    case k: R2VK
    of r2A: a: int
    of r2B: b: int

proc maybeSetVariant(x: int): R2V =
  if x > 0:
    result = R2V(k: r2B, b: 3)

proc sutVariantZeroDeclines(x: int) =
  let r = maybeSetVariant(x)
  discard r
  if x <= 0:
    symexTarget("variant_zero_declines")

proc sutVariantZeroNonzero(x: int) =
  ## Real Nim: the untouched variant result is zero-initialised, `k == r2A`
  ## (ordinal 0) and `a == 0`.
  let r = maybeSetVariant(x)
  if x <= 0 and (r.k != r2A or r.a != 0):
    symexTarget("variant_zero_nonzero")

type
  R2MV = object
    ## Two `case` sections: a multi-variant. RFC-0005 S8p gives it a zero
    ## value (each axis's ordinal-0 arm, every field zero).
    case k: R2VK
    of r2A: a: int
    of r2B: b: int
    case j: R2VK
    of r2A: c: int
    of r2B: d: int
  R2MVE = object
    ## A multi-variant whose first axis's ordinal 0 falls in an `else` arm:
    ## Nim's zero value is legal, but `multiVariantZeroTotal` requires an
    ## explicit ordinal-0 arm on every axis, so it has no modelled zero.
    case k: R2VK
    of r2B: b: int
    else: a: int
    case j: R2VK
    of r2A: c: int
    of r2B: d: int

proc maybeSetMultiVariant(x: int): R2MV =
  ## Never assigned: this pin is about the untouched path alone.
  discard x

proc sutMultiVariantZero(x: int) =
  let r = maybeSetMultiVariant(x)
  discard r
  if x <= 0:
    symexTarget("multivariant_zero")

proc sutMultiVariantZeroNonzero(x: int) =
  ## Real Nim: k == r2A, a == 0, j == r2A, c == 0.
  let r = maybeSetMultiVariant(x)
  if r.k != r2A or r.a != 0 or r.j != r2A or r.c != 0:
    symexTarget("multivariant_zero_nonzero")

proc maybeSetMultiVariantElse(x: int): R2MVE =
  discard x

proc sutMultiVariantZeroDeclines(x: int) =
  let r = maybeSetMultiVariantElse(x)
  discard r
  if x <= 0:
    symexTarget("multivariant_zero_declines")

suite "symex round-6 R2 — honest decline: a return type defaultZero cannot back (float)":

  test "T5g: the assigned float path still proves sxSat (unaffected regression)":
    let r = symexFind(sutFloatAssignedSat, tLabel("float_assigned_sat"))
    check r.status == sxSat

  test "T5h: the untouched float path binds 0.0 (RFC-0005 S8f; was a classified decline)":
    ## Walker 154 gives `defaultZero` its float arm (Nim's `default(float)`
    ## is 0.0), so the untouched path is modelled, not havocked: a clean
    ## sxSat with no decline, and `r != 0.0` there is unreachable.
    let r = symexFind(sutFloatZeroDeclines, tLabel("float_zero_declines"))
    check r.status == sxSat
    check rfc0005RawStatus == sxSat
    check r.errors.len == 0
    let z = symexFind(sutFloatZeroNonzero, tLabel("float_zero_nonzero"))
    check z.status == sxUnsat

  test "T5h-2: an untouched variant result is its zero value (RFC-0005 S8n; was a classified decline)":
    ## Walker 162 gives `defaultZero` the single-case variant's zero value
    ## (discriminator ordinal 0, every field zero), so the untouched path is
    ## modelled: a clean sxSat, and a non-zero value there is unreachable.
    let r = symexFind(sutVariantZeroDeclines, tLabel("variant_zero_declines"))
    check r.status == sxSat
    check rfc0005RawStatus == sxSat
    check r.errors.len == 0
    let z = symexFind(sutVariantZeroNonzero, tLabel("variant_zero_nonzero"))
    check z.status == sxUnsat

  test "T5h-3: an untouched multi-variant result is its zero value (RFC-0005 S8p; was a classified decline)":
    let r = symexFind(sutMultiVariantZero, tLabel("multivariant_zero"))
    check r.status == sxSat
    check rfc0005RawStatus == sxSat
    check r.errors.len == 0
    let z = symexFind(sutMultiVariantZeroNonzero,
                      tLabel("multivariant_zero_nonzero"))
    check z.status == sxUnsat

  test "T5h-4: a result type with no modelled zero (a multi-variant with an else arm at ordinal 0) still declines, never a bound wrong value":
    let r = symexFind(sutMultiVariantZeroDeclines,
                      tLabel("multivariant_zero_declines"))
    check r.status == sxSat
    check rfc0005RawStatus == sxUnknown
    var sawKind = false
    for e in r.errors:
      # RFC-0005 S6b: the untouched result's per-call retSym is free and
      # nothing is dropped -- the `feUnsupportedOpHavoc` split.
      if e.kind == feUnsupportedOpHavoc and e.severity == sevError:
        sawKind = true
    check sawKind

# -----------------------------------------------------------------------------
# 5c. `defaultZero`'s `itSeq` arm, hoisted this slice: an unbacked-element
# seq field NESTED inside an otherwise zero-bindable tuple return must route
# through the v88 placeholder machinery (never call `allocateSeqDataRaw`
# directly) -- else the untouched path's mere zero-value CONSTRUCTION would
# crash the whole run via an uncaught `SymexNestedSeqUnsupportedError`, even
# though nothing ever reads the poisoned field.
# -----------------------------------------------------------------------------

proc maybeSetTupleWithUnbackedSeq(x: int): tuple[a: int, opts: seq[(string, string)]] =
  if x > 0:
    result = (a: x, opts: @[])

proc sutTupleUnbackedSeqZeroFieldNoCrash(x: int) =
  ## `opts` is never read -- only `a` is queried. Must not crash merely
  ## because the untouched path's zero-default construction touches the
  ## unbacked-element seq field.
  let r = maybeSetTupleWithUnbackedSeq(x)
  if x <= 0 and r.a == 0:
    symexTarget("tuple_unbackedseq_zero_field_sat")

suite "symex round-6 R2 — nested unbacked-elem seq field zero-inits without crashing":

  test "T5i: the untouched path's sibling scalar field still proves sxSat, no crash":
    let r = symexFind(sutTupleUnbackedSeqZeroFieldNoCrash,
                       tLabel("tuple_unbackedseq_zero_field_sat"))
    check r.status == sxSat

# =============================================================================
# 6. Regression: an explicit-`return` callee and a v86-style
#    ALWAYS-assigned-fallthrough callee (every arm assigns `result`, so
#    `cp.env.hasKey("result")` is true on every path -- v86's own branch,
#    never reaching this slice's new `else` twin) still bind correctly.
# =============================================================================

proc explicitReturnCallee(x: int): int =
  if x > 0:
    return x
  return -x

proc sutExplicitReturnSat(x: int) =
  if x > 0:
    let r = explicitReturnCallee(x)
    if r == x:
      symexTarget("explicit_return_sat")

proc sutExplicitReturnUnsat(x: int) =
  symexAssume(x > 0)
  let r = explicitReturnCallee(x)
  if r != x:
    symexTarget("explicit_return_impossible")

proc alwaysAssignFallthrough(x: int): int =
  if x > 0:
    result = x
  else:
    result = -x

proc sutAlwaysAssignSat(x: int) =
  if x < 0:
    let r = alwaysAssignFallthrough(x)
    if r == -x:
      symexTarget("always_assign_sat")

proc sutAlwaysAssignNeverNegative(x: int) =
  ## Bounded away from `low(int)` so `-x` cannot itself overflow (a genuine,
  ## unrelated arithmetic-overflow edge case, not what this pin targets).
  symexAssume(x > low(int) div 2 and x < high(int) div 2)
  let r = alwaysAssignFallthrough(x)
  if r < 0:
    symexTarget("always_assign_never_negative")

suite "symex round-6 R2 — regression: explicit return still binds correctly":

  test "T6a: explicit-return callee, reachable arm (sxSat)":
    let r = symexFind(sutExplicitReturnSat, tLabel("explicit_return_sat"))
    check r.status == sxSat

  test "T6b: explicit-return callee, soundness -- r != x is impossible for x > 0 (sxUnsat)":
    let r = symexFind(sutExplicitReturnUnsat, tLabel("explicit_return_impossible"))
    check r.status == sxUnsat

suite "symex round-6 R2 — regression: v86 always-assigned fallthrough still binds correctly":

  test "T6c: always-assigned fallthrough callee, reachable arm (sxSat)":
    let r = symexFind(sutAlwaysAssignSat, tLabel("always_assign_sat"))
    check r.status == sxSat

  test "T6d: always-assigned fallthrough callee, soundness -- result is never negative (sxUnsat)":
    let r = symexFind(sutAlwaysAssignNeverNegative, tLabel("always_assign_never_negative"))
    check r.status == sxUnsat

# =============================================================================
# Version pins
# =============================================================================

suite "symex round-6 R2 — version pins":

  test "walker version floor >= 90 (soundness fix -- zero-default result binding)":
    check parseInt(symexWalkerVersion) >= 90

  test "renderAsChoicesVersion floor >= 11 (no new witness shape this slice)":
    check parseInt(renderAsChoicesVersion) >= 11
