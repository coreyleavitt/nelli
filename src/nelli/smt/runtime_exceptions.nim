# runtime_exceptions.nim -- Cluster E: the `lower()` dispatch arm for
# `iekGetCurrentExnMsg` and `iekGetCurrentExn` (Cluster E, Stage 7 / Stage 8,
# CR-7). A real module (RFC-0016 review D3c-3): it imports `./symval` and
# `./walk_state` and names no `runtime.nim` symbol. `runtime.nim` imports it
# before `lower`'s body. `routeRaise`, raise-walker, and try/finally arms are
# named procs in `walk` and are NOT moved here.
import std/options
import z3
import ./types
import ./symval
import ./walk_state

proc lowerExnArm*(env: Env, e: IRExpr): SymVal =
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
    # `currentInFlightMsg` by the handler-body walk; a `none` inFlightId means we
    # are outside any handler → classified `eeNotInHandler` (Invariant 3).
    if currentInFlightTypeId.isNone:
      raise (ref SymexNotInHandlerError)(  # [raise-audited: boundary-abort -- caught by runSymexCaught -> sxUnknown + eeNotInHandler, never a silent UNSAT; reached outside a handler from nested frames by tsymex_phase15_E8 (D3-fix-c)]
        msg: "getCurrentExceptionMsg")
    SymVal(kind: svString, str: mkString(currentInFlightMsg.get("")))
  of iekGetCurrentExn:
    # Phase 15 E8. `getCurrentException()`. Returns an opaque `svUninterpRef`
    # keyed by the in-flight type: a FRESH uninterpreted-sort constant whose
    # sort is `Exn_<inFlightId>`. Fields are not modeled (extraction emits an
    # `eeUninterpRefExtraction` sevHint). Out of a handler → `eeNotInHandler`.
    if currentInFlightTypeId.isNone:
      raise (ref SymexNotInHandlerError)(  # [raise-audited: boundary-abort -- caught by runSymexCaught -> sxUnknown + eeNotInHandler, never a silent UNSAT; reached outside a handler from nested frames by tsymex_phase15_E8 (D3-fix-c)]
        msg: "getCurrentException")
    let inFlightId  = currentInFlightTypeId.get
    let srtName = "Exn_" & inFlightId
    inc currentExnRefCounter
    let constName = srtName & "#" & $currentExnRefCounter
    # Fresh constant of the (per-type) uninterpreted sort, erased to Z3AnyAst.
    let z3c = requireCurrentContext()
    let srt = mkUninterpretedSort(z3c, srtName)
    let sym = z3c.checkErr Z3_mk_string_symbol(z3c.raw, constName.cstring)
    let rawConst = z3c.checkErr Z3_mk_const(z3c.raw, sym, srt.raw)
    let anyAst = wrap[Z3AnyAst](z3c, rawConst)
    lastGetCurrentExnRef = (sortName: srtName, typeTag: inFlightId)  ## E8 test hook
    SymVal(kind: svUninterpRef, uninterpAst: anyAst,
           sortName: srtName, typeTag: inFlightId)
  else:
    raise newException(ValueError,  # [raise-audited: category-c: `lower` dispatches only iekGetCurrentExnMsg/iekGetCurrentExn to lowerExnArm (runtime.nim, the single call site), both handled above]
      "lowerExnArm: unexpected e.kind=" & $e.kind &
      " (not iekGetCurrentExnMsg/iekGetCurrentExn)")
