# runtime_floats.nim — Cluster F include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_floats.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents (CR-7-deeper Stage 8+):
#   mkFloatLitSym, toBv64ForFp, lowerMathCall — Cluster F float helpers
#   (moved from runtime.nim; only used by lowerFloatArm or each other).
#   `lowerFloatArm(env, e)` — the `lower()` dispatch arm for
#   `iekFloatLit`, `iekConvIntToFloat`, `iekConvFloatToInt`, `iekMathCall`
#   (Cluster F, Stage 7 / Stage 8, CR-7).
# Placement in runtime.nim: immediately after `include "runtime_strings.nim"`
# and immediately before `lowerExnArm`, between `lower`'s forward-decl
# and `lower`'s body.

proc mkFloatLitSym(v: float64, width: int): SymVal =
  ## Phase 15 F2: lower a float literal to a Z3 FP numeral, honoring
  ## NaN / ±Inf / -0.0 (ADR-0005) via Nim's `classify`.
  let cls = classify(v)
  if width == 32:
    SymVal(kind: svFloat32, fp32:
      (case cls
       of fcNan:     mkFpNaN[8, 24]()
       of fcInf:     mkFpInf[8, 24](false)
       of fcNegInf:  mkFpInf[8, 24](true)
       of fcNegZero: mkFpZero[8, 24](true)
       else:         mkFloat32(float32(v))))
  else:
    SymVal(kind: svFloat64, fp64:
      (case cls
       of fcNan:     mkFpNaN[11, 53]()
       of fcInf:     mkFpInf[11, 53](false)
       of fcNegInf:  mkFpInf[11, 53](true)
       of fcNegZero: mkFpZero[11, 53](true)
       else:         mkFloat64(v)))

proc toBv64ForFp(sv: SymVal): Z3BitVec[64] =
  ## Phase 15 F5: obtain the 64-bit bit pattern of an integer SymVal
  ## directly for an int->float conversion, WITHOUT round-tripping
  ## through the Z3 mathematical-Int sort.
  ##
  ## The earlier form `intToBv[64](toZ3Int(sv), ...)` emitted
  ## `int2bv(bv2int(x))` for a BV operand. That sandwich mixes the
  ## Int + BV + FP theories in one query: trivial for an equality
  ## goal (Z3 guesses a model), but pathological for an ordering goal
  ## (e.g. `float(x) > 1.5`), where Z3 never terminates. Operating on
  ## the bitvector directly keeps the query in QF_BVFP, which Z3 solves
  ## by bit-blasting. Narrower ints are sign-/zero-extended per signedness.
  case sv.kind
  of svBV64: sv.bv64
  of svBV32: (if sv.signed: signExtend(sv.bv32, 32) else: zeroExtend(sv.bv32, 32))
  of svBV16: (if sv.signed: signExtend(sv.bv16, 48) else: zeroExtend(sv.bv16, 48))
  of svBV8:  (if sv.signed: signExtend(sv.bv8, 56)  else: zeroExtend(sv.bv8, 56))
  of svInt:  intToBv[64](sv.zi, Z3BitVec[64])   # genuine unbounded Int: last resort
  else:
    raise newException(ValueError,
      "float(): operand is not an integer — got " & $sv.kind)

proc lowerMathCall(env: Env, e: IRExpr): SymVal =
  ## Phase 15 F6. Lower a std/math float op or FP predicate to its
  ## Z3-FP-native ast. Symmetric over svFloat32 / svFloat64. Deferred and
  ## unmodeled ops raise `SymexUnsupportedOpError` (caught at the runSymex
  ## boundary -> sxUnknown + feUnsupportedOp; never a silent UNSAT).
  let op = e.mathOp
  if e.mathArgs.len == 0:
    raise (ref SymexUnsupportedOpError)(op: "math." & op,
      msg: "math." & op & ": zero-arg float op is unsupported")
  let a = lower(env, e.mathArgs[0])
  doAssert a.kind in {svFloat32, svFloat64},
    "lowerMathCall: first arg is not a float — got " & $a.kind

  # ----- predicates (return svBool), width-symmetric -----
  template pred(call: untyped): SymVal =
    if a.kind == svFloat32: ofBool(call(a.fp32)) else: ofBool(call(a.fp64))
  case op
  of "signbit": return pred(isNegative)
  of "isNaN":   return pred(isNaN)
  of "isInf":   return pred(isInf)
  of "isFinite":return pred(isFinite)
  of "isNormal":return pred(isNormal)
  else: discard

  # ----- unary float -> float ops -----
  template f32(v: untyped): SymVal = SymVal(kind: svFloat32, fp32: v)
  template f64(v: untyped): SymVal = SymVal(kind: svFloat64, fp64: v)
  case op
  of "abs":
    return (if a.kind == svFloat32: f32(abs(a.fp32)) else: f64(abs(a.fp64)))
  of "sqrt":
    return (if a.kind == svFloat32: f32(sqrt(rmRNE(), a.fp32))
            else: f64(sqrt(rmRNE(), a.fp64)))
  of "floor":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRTN(), a.fp32))
            else: f64(roundToIntegral(rmRTN(), a.fp64)))
  of "ceil":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRTP(), a.fp32))
            else: f64(roundToIntegral(rmRTP(), a.fp64)))
  of "round":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRNE(), a.fp32))
            else: f64(roundToIntegral(rmRNE(), a.fp64)))
  of "trunc":
    return (if a.kind == svFloat32: f32(roundToIntegral(rmRTZ(), a.fp32))
            else: f64(roundToIntegral(rmRTZ(), a.fp64)))
  of "min", "max":
    doAssert e.mathArgs.len == 2, "math." & op & " expects two args"
    let b = lower(env, e.mathArgs[1])
    doAssert b.kind == a.kind, "math." & op & ": float-width mismatch"
    if op == "min":
      return (if a.kind == svFloat32: f32(min(a.fp32, b.fp32))
              else: f64(min(a.fp64, b.fp64)))
    else:
      return (if a.kind == svFloat32: f32(max(a.fp32, b.fp32))
              else: f64(max(a.fp64, b.fp64)))
  else:
    # Deferred (classify/copySign/nextafter) or any unmodeled math.<name>.
    raise (ref SymexUnsupportedOpError)(op: "math." & op,
      msg: "math." & op & " is not modeled by the symex engine (Phase 16 backlog)")

proc lowerFloatArm(env: Env, e: IRExpr): SymVal =
  ## Stage 7 (CR-7) Cluster F extraction. Called from `lower`'s case arm for
  ## `iekFloatLit`, `iekConvIntToFloat`, `iekConvFloatToInt`, `iekMathCall`.
  ## `proto` is NOT used by any float arm. `cmpFloat`/`arithFloat`/
  ## `reconcileFloat` are already named procs and are NOT moved here.
  ##
  ## Shared-symbol dependencies for Stage 8 include-ordering:
  ##   mkFloatLitSym, toBv64ForFp, toFpFromSigned, rmRNE, rmRTZ,
  ##   Z3Float32, Z3Float64, toSbv, mkFloat32, mkFloat64,
  ##   convFloatToIntBoundConds, syncConvFloatToIntBoundCond,
  ##   convFloatToIntDomainHints, syncConvFloatToIntDomainHint,
  ##   SymexErrorInfo, feConvDomainExcluded, sevHint, lowerMathCall
  case e.kind
  of iekFloatLit:
    mkFloatLitSym(e.fval, e.fwidth)
  of iekConvIntToFloat:
    # Phase 15 F5: int -> float. signed-bv -> fp (rmRNE, OQ2). The operand
    # is already a bitvector; `toBv64ForFp` takes its 64-bit pattern directly
    # rather than via `int2bv(bv2int(x))` (which hangs Z3 on ordering goals).
    let sv = lower(env, e.convOperand)
    let bv64 = toBv64ForFp(sv)
    if e.convWidth == 32:
      SymVal(kind: svFloat32, fp32: toFpFromSigned(rmRNE(), bv64, Z3Float32))
    else:
      SymVal(kind: svFloat64, fp64: toFpFromSigned(rmRNE(), bv64, Z3Float64))
  of iekConvFloatToInt:
    # Phase 15 CR-3/CR-4: float -> int(W), rmRTZ truncation (OQ2).
    #
    # CR-3 (domain bounding): Add a path constraint bounding the float operand
    # to the in-range window for the target integer width, so any witness Z3
    # produces is guaranteed to round-trip through Nim's int()/int32() without
    # raising RangeDefect.  IEEE semantics:
    #   • `f >= lo` is false for NaN (NaN compares false), true for +Inf (if lo<∞)
    #   • `f < hi` is false for NaN and +Inf/−Inf (Inf is not less than any finite)
    # So `f >= lo and f < hi` correctly excludes NaN, ±Inf and all out-of-range
    # finite floats with no explicit isFinite test.  The constraint is deposited
    # in the `convFloatToIntBoundConds` threadvar; the walker drains it into p.pc
    # immediately after lower() returns (mirroring the parseIntRaiseConds idiom).
    # RangeDefect raise-path modeling is Phase-16.
    #
    # CR-4 (width correctness): read `e.convWidth`; use toSbv[..,32] for width 32
    # and return svBV32 so downstream comparisons see the correct 32-bit result.
    #
    # Domain hint: emit feConvDomainExcluded (sevHint) into convFloatToIntDomainHints
    # (drained dedup'd into RawResult.errors on every verdict branch — never changes
    # the verdict, Invariant 7).  One hint per lowering site; messages identify the
    # target width for diagnostics.
    let sv = lower(env, e.convOperand)
    if e.convWidth == 32:
      # float → int32: bound to [-2^31, 2^31) in the operand's FP sort.
      # float32 range: lo32 = -2147483648.0'f32 (exact = -2^31),
      #                hi32 = 2147483648.0'f32 (= 2^31, excluded by strict <).
      # float64 range: same values but as float64.
      let bv32 =
        case sv.kind
        of svFloat32:
          let lo = mkFloat32(-2147483648.0'f32)
          let hi = mkFloat32(2147483648.0'f32)
          let domainCond = (sv.fp32 >= lo) and (sv.fp32 < hi)
          convFloatToIntBoundConds.add domainCond          # threadvar fallback
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          toSbv[8, 24, 32](rmRTZ(), sv.fp32)
        of svFloat64:
          let lo = mkFloat64(-2147483648.0)
          let hi = mkFloat64(2147483648.0)
          let domainCond = (sv.fp64 >= lo) and (sv.fp64 < hi)
          convFloatToIntBoundConds.add domainCond          # threadvar fallback
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          toSbv[11, 53, 32](rmRTZ(), sv.fp64)
        else: raise newException(ValueError, "int32(): operand is not a float")
      let domHint32 = SymexErrorInfo(
        kind: feConvDomainExcluded, severity: sevHint,
        msg: "int32(float): conversion domain bounded to [-2^31, 2^31); " &
             "floats outside this range (NaN/Inf/too-large) excluded from " &
             "path condition (honest-incomplete). RangeDefect modeling is Phase-16.")
      convFloatToIntDomainHints.add domHint32          # threadvar: fallback
      syncConvFloatToIntDomainHint(domHint32)          # CR-9 Stage 5: WalkCtx
      SymVal(kind: svBV32, bv32: bv32, signed: true)
    else:
      # float → int64 (default): bound to [-2^63, 2^63) in the operand's FP sort.
      # float64 range: lo64 = -9.223372036854776e18 (= -2^63, exact in float64),
      #                hi64 = +9.223372036854776e18 (= +2^63, excluded by strict <).
      # Note: high(int64) = 2^63-1 is NOT exactly representable as float64 (rounds
      # up to 2^63); using strict < against 2^63 correctly excludes all
      # out-of-range values including the float64 that would represent 2^63.
      let bv64 =
        case sv.kind
        of svFloat64:
          let lo = mkFloat64(-9.223372036854776e18)
          let hi = mkFloat64(9.223372036854776e18)
          let domainCond = (sv.fp64 >= lo) and (sv.fp64 < hi)
          convFloatToIntBoundConds.add domainCond          # threadvar fallback
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          toSbv[11, 53, 64](rmRTZ(), sv.fp64)
        of svFloat32:
          # float32 → int64: same int64 bounds but expressed in float32.
          # -2^63 and +2^63 are exactly representable as float32 (powers of 2).
          let lo = mkFloat32(-9.223372036854776e18.float32)
          let hi = mkFloat32(9.223372036854776e18.float32)
          let domainCond = (sv.fp32 >= lo) and (sv.fp32 < hi)
          convFloatToIntBoundConds.add domainCond          # threadvar fallback
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          toSbv[8, 24, 64](rmRTZ(), sv.fp32)
        else: raise newException(ValueError, "int(): operand is not a float")
      let domHint64 = SymexErrorInfo(
        kind: feConvDomainExcluded, severity: sevHint,
        msg: "int(float): conversion domain bounded to [-2^63, 2^63); " &
             "floats outside this range (NaN/Inf/too-large) excluded from " &
             "path condition (honest-incomplete). RangeDefect modeling is Phase-16.")
      convFloatToIntDomainHints.add domHint64          # threadvar: fallback
      syncConvFloatToIntDomainHint(domHint64)          # CR-9 Stage 5: WalkCtx
      SymVal(kind: svBV64, bv64: bv64, signed: true)
  of iekMathCall:
    lowerMathCall(env, e)
  else:
    raise newException(ValueError,
      "lowerFloatArm: unexpected e.kind=" & $e.kind &
      " (not iekFloatLit/iekConvIntToFloat/iekConvFloatToInt/iekMathCall)")
