## Phase 15 — Cluster E, cycle E1: exception IR (`isRaise`/`isTry`) + walker
## handler-stack scaffolding. PURELY STRUCTURAL — the parser recognises
## `nnkRaiseStmt`/`nnkTryStmt`/`nnkExceptBranch`/`nnkFinally` and emits the new
## IR kinds; the walker STUBS both with a deterministic classified error
## (`eeRaiseUnimplemented`/`eeTryUnimplemented`, sevError) → `sxUnknown`
## (Invariant 3 — never silent, never a crash). No exception semantics yet
## (those land E2b+).
import std/[unittest, macros, strutils]
import proptest/smt/types
import proptest/smt/dsl_parser
import proptest/symex

# --- a typed SUT containing `raise newException(ValueError, "x")` ------------
proc raiseSut() =
  raise newException(ValueError, "x")
  symexTarget("after")

# Render the parsed body of a typed proc.
macro renderProcBody(p: typed): string =
  let impl = p.getImpl
  newLit(render(parseProc(impl).body))

suite "symex Phase 15 E1 — exception IR (raise/try) + handler scaffolding":
  test "parser emits isRaise for nnkRaiseStmt; render is canonical":
    let r = renderProcBody(raiseSut)
    # The parsed body must contain an isRaise node rendered canonically.
    check r.contains("raise(ValueError,\"x\")")

  test "render of a hand-constructed minimal isTry is canonical":
    let body = mkBlock(@[mkAssert(mkBoolLit(true))])
    let handler = ExceptHandler(typeIds: @["ValueError"],
                                body: mkBlock(@[mkReturn()]))
    let fin = mkBlock(@[mkReturn()])
    let t = mkTry(body, @[handler], fin)
    check render(t) ==
      "try{" & render(body) & "}except[ValueError=>" & render(handler.body) &
      "][finally=>" & render(fin) & "]"

  test "render of a bare raise (re-raise) is canonical":
    check render(mkReraise()) == "raise()"

  test "walker stubs isRaise → sxUnknown + eeRaiseUnimplemented (classified)":
    let res = symexFind(raiseSut, tLabel("after"))
    check res.status == sxUnknown
    check res.errors.len >= 1
    check res.errors[0].kind == eeRaiseUnimplemented
    check res.errors[0].severity == sevError
