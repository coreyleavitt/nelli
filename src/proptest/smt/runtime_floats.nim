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
  of svInt:
    # CR-17(b) DEFENSIVE: a genuine Z3 unbounded Int feeding a float conversion
    # would produce `int2bv(zi)` here, then `toFpFromSigned(int2bv(zi))`.
    # If that FP value is later ordered (e.g. `float(x) > 1.5`), the query
    # becomes `fp.to.sbv(int2bv(zi))` in an ordering goal — the F5 pathology
    # (Int+BV+FP round-trip). This arm is a "last resort" that no current
    # parser arm should ever reach (all integer types lower to BV variants via
    # their abstraction layer). Classify sxUnknown (honest) rather than risking
    # the F5 hang shape.
    raise (ref SymexUnsupportedOpError)(op: "float(svInt)",
      msg: "float() of an unbounded-Int operand (svInt) is not modeled " &
           "(CR-17: emitting int2bv(Z3Int)→FP risks the F5 ordering pathology; " &
           "the integer abstraction layer should lower integer params to BV, not svInt)")
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
  of "classify":
    # Phase 16 A5: classify(f) → svBV64 (signed) ordinal matching Nim's FloatClass:
    #   fcNormal=0, fcSubnormal=1, fcZero=2, fcNegZero=3, fcNan=4, fcInf=5, fcNegInf=6
    # Priority order matches Nim's std/math classify: NaN first, then Inf (signed),
    # then zero (signed — isZero is true for ±0.0; isNegative splits them), then
    # subnormal, then normal. Built as a Z3 ite-chain over FP predicates
    # (width-symmetric) so the result stays in QF_BVFP.
    # probeProto returns svBV64 for "classify", keeping enum-ordinal comparisons
    # single-theory (BV) — no Int+BV+FP round-trip (F5 safety).
    template bv64(n: int64): Z3BitVec[64] = mkBitVec[64](n)
    if a.kind == svFloat32:
      let f = a.fp32
      let v = ite(isNaN(f), bv64(4),
                ite(isInf(f) and isNegative(f), bv64(6),
                  ite(isInf(f), bv64(5),
                    ite(isZero(f) and isNegative(f), bv64(3),
                      ite(isZero(f), bv64(2),
                        ite(isSubnormal(f), bv64(1), bv64(0)))))))
      return SymVal(kind: svBV64, bv64: v, signed: true)
    else:
      let f = a.fp64
      let v = ite(isNaN(f), bv64(4),
                ite(isInf(f) and isNegative(f), bv64(6),
                  ite(isInf(f), bv64(5),
                    ite(isZero(f) and isNegative(f), bv64(3),
                      ite(isZero(f), bv64(2),
                        ite(isSubnormal(f), bv64(1), bv64(0)))))))
      return SymVal(kind: svBV64, bv64: v, signed: true)
  of "copySign":
    # Phase 16 A5: copySign(x, y) = ite(isNegative(y), -abs(x), abs(x)).
    # abs clears the sign bit (exact, no rounding); unary `-` flips it (exact).
    # Returns a float of x's width; sign comes entirely from y (2nd arg).
    doAssert e.mathArgs.len == 2, "math.copySign expects two args"
    let b = lower(env, e.mathArgs[1])
    doAssert b.kind == a.kind, "math.copySign: float-width mismatch"
    if a.kind == svFloat32:
      return f32(ite(isNegative(b.fp32), -abs(a.fp32), abs(a.fp32)))
    else:
      return f64(ite(isNegative(b.fp64), -abs(a.fp64), abs(a.fp64)))
  of "nextafter":
    # nextafter has no Z3 FP-theory primitive (SMT-LIB FP has no fp.nextUp/nextDown);
    # this is a documented bound — remains feUnsupportedOp (Invariant 3: never fake).
    raise (ref SymexUnsupportedOpError)(op: "math.nextafter",
      msg: "math.nextafter is not modeled: no SMT-LIB FP-theory primitive for " &
           "next-representable value (documented Z3 bound; Invariant 3)")
  else:
    raise (ref SymexUnsupportedOpError)(op: "math." & op,
      msg: "math." & op & " is not modeled by the symex engine")

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
  ##   convFloatToIntDomainConds, syncConvFloatToIntDomainCond,
  ##   lowerMathCall
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
    # Phase 15 CR-3/CR-4 + Phase 16 R16-2: float -> int(W), rmRTZ truncation (OQ2).
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
    #
    # R16-2 (RangeDefect fork): the SAME `domainCond` is ALSO pushed to the
    # parallel `convFloatToIntDomainConds` sink. The walker's
    # `drainConvFloatToIntRaises` (called from the PRE-narrowing path) forks
    # `not(domainCond)` as a RangeDefect raise. Dual-drain: bounds drain on the
    # normal path (narrowing), raise drain on the error path (fork).
    #
    # CR-4 (width correctness): read `e.convWidth`; use toSbv[..,32] for width 32
    # and return svBV32 so downstream comparisons see the correct 32-bit result.
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
          convFloatToIntBoundConds.add domainCond          # threadvar fallback (bounds drain)
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          convFloatToIntDomainConds.add domainCond         # R16-2: parallel raise-fork sink
          syncConvFloatToIntDomainCond(domainCond)         # R16-2: WalkCtx live store
          toSbv[8, 24, 32](rmRTZ(), sv.fp32)
        of svFloat64:
          let lo = mkFloat64(-2147483648.0)
          let hi = mkFloat64(2147483648.0)
          let domainCond = (sv.fp64 >= lo) and (sv.fp64 < hi)
          convFloatToIntBoundConds.add domainCond          # threadvar fallback (bounds drain)
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          convFloatToIntDomainConds.add domainCond         # R16-2: parallel raise-fork sink
          syncConvFloatToIntDomainCond(domainCond)         # R16-2: WalkCtx live store
          toSbv[11, 53, 32](rmRTZ(), sv.fp64)
        else: raise newException(ValueError, "int32(): operand is not a float")
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
          convFloatToIntBoundConds.add domainCond          # threadvar fallback (bounds drain)
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          convFloatToIntDomainConds.add domainCond         # R16-2: parallel raise-fork sink
          syncConvFloatToIntDomainCond(domainCond)         # R16-2: WalkCtx live store
          toSbv[11, 53, 64](rmRTZ(), sv.fp64)
        of svFloat32:
          # float32 → int64: same int64 bounds but expressed in float32.
          # -2^63 and +2^63 are exactly representable as float32 (powers of 2).
          let lo = mkFloat32(-9.223372036854776e18.float32)
          let hi = mkFloat32(9.223372036854776e18.float32)
          let domainCond = (sv.fp32 >= lo) and (sv.fp32 < hi)
          convFloatToIntBoundConds.add domainCond          # threadvar fallback (bounds drain)
          syncConvFloatToIntBoundCond(domainCond)          # CR-9 Stage 6 Group-1
          convFloatToIntDomainConds.add domainCond         # R16-2: parallel raise-fork sink
          syncConvFloatToIntDomainCond(domainCond)         # R16-2: WalkCtx live store
          toSbv[8, 24, 64](rmRTZ(), sv.fp32)
        else: raise newException(ValueError, "int(): operand is not a float")
      SymVal(kind: svBV64, bv64: bv64, signed: true)
  of iekMathCall:
    lowerMathCall(env, e)
  else:
    raise newException(ValueError,
      "lowerFloatArm: unexpected e.kind=" & $e.kind &
      " (not iekFloatLit/iekConvIntToFloat/iekConvFloatToInt/iekMathCall)")
