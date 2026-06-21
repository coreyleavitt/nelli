# runtime_exceptions.nim — Cluster E include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_exceptions.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents: `lowerExnArm(env, e)` — the `lower()` dispatch arm for
# `iekGetCurrentExnMsg` and `iekGetCurrentExn` (Cluster E, Stage 7 / Stage 8,
# CR-7). `routeRaise`, raise-walker, and try/finally arms are already named
# procs in `walk` and are NOT moved here.
# Placement in runtime.nim: immediately after `include "runtime_floats.nim"`
# and immediately before `lowerClosureArm`, between `lower`'s forward-decl
# and `lower`'s body.

proc lowerExnArm(env: Env, e: IRExpr): SymVal =
  ## Stage 7 (CR-7) Cluster E extraction. Called from `lower`'s case arm for
  ## `iekGetCurrentExnMsg` and `iekGetCurrentExn`. `proto` is NOT used.
  ## `routeRaise`, raise-walker, try/finally arms are already named procs in
  ## `walk` — only the `lower`-level expression arms are moved here.
  ##
  ## Shared-symbol dependencies for Stage 8 include-ordering:
  ##   currentInFlightTypeId, currentInFlightMsg, currentExnRefCounter,
  ##   lastGetCurrentExnRef, requireCurrentContext, mkUninterpretedSort,
  ##   Z3_mk_string_symbol, Z3_mk_const, wrap, mkString,
  ##   SymexNotInHandlerError, svUninterpRef
  case e.kind
  of iekGetCurrentExnMsg:
    # Phase 15 E8. `getCurrentExceptionMsg()`. Valid only inside an `except`
    # handler body (in-flight exn present). The in-flight msg is mirrored into
    # `currentInFlightMsg` by the handler-body walk; a `none` typeId means we
    # are outside any handler → classified `eeNotInHandler` (Invariant 3).
    if currentInFlightTypeId.isNone:
      raise (ref SymexNotInHandlerError)(
        msg: "getCurrentExceptionMsg")
    SymVal(kind: svString, str: mkString(currentInFlightMsg.get("")))
  of iekGetCurrentExn:
    # Phase 15 E8. `getCurrentException()`. Returns an opaque `svUninterpRef`
    # keyed by the in-flight type: a FRESH uninterpreted-sort constant whose
    # sort is `Exn_<typeId>`. Fields are not modeled (extraction emits an
    # `eeUninterpRefExtraction` sevHint). Out of a handler → `eeNotInHandler`.
    if currentInFlightTypeId.isNone:
      raise (ref SymexNotInHandlerError)(
        msg: "getCurrentException")
    let typeId  = currentInFlightTypeId.get
    let srtName = "Exn_" & typeId
    inc currentExnRefCounter
    let constName = srtName & "#" & $currentExnRefCounter
    # Fresh constant of the (per-type) uninterpreted sort, erased to Z3AnyAst.
    let ctx = requireCurrentContext()
    let srt = mkUninterpretedSort(ctx, srtName)
    let sym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, constName.cstring)
    let rawConst = ctx.checkErr Z3_mk_const(ctx.raw, sym, srt.raw)
    let anyAst = wrap[Z3AnyAst](ctx, rawConst)
    lastGetCurrentExnRef = (sortName: srtName, typeTag: typeId)  ## E8 test hook
    SymVal(kind: svUninterpRef, uninterpAst: anyAst,
           sortName: srtName, typeTag: typeId)
  else:
    raise newException(ValueError,
      "lowerExnArm: unexpected e.kind=" & $e.kind &
      " (not iekGetCurrentExnMsg/iekGetCurrentExn)")
