## RFC-0016 K7b (section 8.4, K7): `walkUnsupported` returns `Survivors`;
## `feUnadmitted` moves to `dcOmitted`; W-11 and W-16.
##
## What K7b makes true:
##   (a) a kind of class `dcOmitted` never carries a path past the cell that
##       raised it: the `isUnsupported` arm and the walker's missing-callee arm
##       drop the path (`halted`), so a target reachable only past an
##       unadmitted cell is never claimed `sxSat`, and a sibling path that
##       does not reach the cell still answers cleanly;
##   (b) W-16: a `Defect` suppressed by `defectExclusions` on a feasible path
##       records `feDefectExcluded` (`dcOmitted`), so a search the excluded
##       raise could have answered is `sxUnknown`, never a trusted `sxUnsat`;
##   (c) W-11: `svWithRaw` on a composite value no longer returns the stale
##       value silently (no SUT reaches it today: its one caller hands it a
##       scalar or string, so the pin is a unit one);
##   (d) the walker version is at least 290 (the class of `feUnadmitted`
##       moved, which changes taint).
import std/[unittest, strutils, os]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import z3

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc k7bAssertF(x: int) =
  assert x > 0, "must be positive"

proc k7bOom(x: int) =
  if x > 0: raise newException(OutOfMemDefect, "k7b")

proc k7bDeadDefect(x: int) =
  if x > 5 and x < 3: raise newException(AssertionDefect, "k7b dead")

const excludeAssert = block:
  var s = defaultSymexSettings()
  s.defectExclusions.incl dkAssertionDefect
  s

let unadmittedKey = unregisteredCalleeKey(feUnadmitted, "magic:NoSuchMagic")

proc unadmittedProg(): SymexProgram =
  ## `if x > 0: <call a callee declined feUnadmitted>; target "past"
  ##  else: target "other"`
  let t = tInt(64, true)
  SymexProgram(params: @[IRParam(name: "x", ty: t)],
    body: mkBlock(@[
      mkIf(@[mkBranch(mkBinop(bGt, mkVar("x"), mkIntLit(0)),
                      mkBlock(@[mkCall(unadmittedKey, "", @[], tBool()),
                                mkTargetLabel("past")]))],
           mkBlock(@[mkTargetLabel("other")]))]))

suite "RFC-0016 K7b (a) -- feUnadmitted is dcOmitted and drops the path":

  test "the class of feUnadmitted and feDefectExcluded is dcOmitted":
    check classOf(feUnadmitted) == dcOmitted
    check classOf(feDefectExcluded) == dcOmitted

  test "a target past an unadmitted cell is never claimed sxSat":
    let raw = runSymex(unadmittedProg(),
                       SymexTarget(kind: stkLabel, label: "past"))
    checkpoint($raw.status)
    check raw.status != sxSat
    check raw.status == sxUnknown
    check raw.errors.hasKind(feUnadmitted)

  test "a sibling path that does not reach the cell still answers":
    let raw = runSymex(unadmittedProg(),
                       SymexTarget(kind: stkLabel, label: "other"))
    check raw.status == sxSat

  test "an unreachable target is not a trusted sxUnsat across the cell":
    let raw = runSymex(unadmittedProg(),
                       SymexTarget(kind: stkLabel, label: "nowhere"))
    check raw.status == sxUnknown

  test "the isUnsupported arm drops a dcOmitted marker and taints the rest":
    let t = tInt(64, true)
    let prog = SymexProgram(params: @[IRParam(name: "x", ty: t)],
      body: mkBlock(@[
        mkIf(@[mkBranch(mkBinop(bGt, mkVar("x"), mkIntLit(0)),
                        mkBlock(@[mkUnsupported(feUnadmitted, "k7b probe", 0),
                                  mkTargetLabel("past")]))],
             mkBlock(@[mkTargetLabel("other")]))]))
    check runSymex(prog, SymexTarget(kind: stkLabel, label: "past")).status ==
      sxUnknown
    check runSymex(prog, SymexTarget(kind: stkLabel, label: "other")).status ==
      sxSat

  test "walkUnsupported is the arm's body":
    let src = readFile(currentSourcePath().parentDir() / ".." / "src" /
                       "nelli" / "smt" / "runtime.nim")
    check "proc walkUnsupported(" in src
    check "walkUnsupported(stmt, paths, w).live" in src

suite "RFC-0016 K7b (b) -- W-16: an excluded Defect is recorded, not silent":

  test "an AssertionDefect excluded under a label search is sxUnknown":
    let r = symexFind(k7bAssertF, tLabel("never_reached"), excludeAssert)
    checkpoint($r.status)
    check r.status == sxUnknown
    check r.errors.hasKind(feDefectExcluded)

  test "the same search without the exclusion still surfaces the defect":
    let r = symexFind(k7bAssertF, tLabel("never_reached"))
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"

  test "the default exclusion of OutOfMemDefect is recorded too":
    let r = symexFind(k7bOom, tLabel("never_reached"))
    checkpoint($r.status)
    check r.status == sxUnknown
    check r.errors.hasKind(feDefectExcluded)

  test "an excluded defect on an infeasible path records nothing":
    let r = symexFind(k7bDeadDefect, tLabel("never_reached"), excludeAssert)
    check r.status == sxUnsat
    check not r.errors.hasKind(feDefectExcluded)

suite "RFC-0016 K7b (c) -- W-11: svWithRaw on a composite":

  test "a scalar takes the new term":
    let ctx = newContext()
    let sv = ofBool(ctx.mkTrue())
    let r = svWithRaw(ctx, sv, ctx.mkFalse().toAnyAst)
    check r.kind == svBool

  test "a composite is refused, not returned stale":
    let ctx = newContext()
    let sv = SymVal(kind: svTuple, fields: @[])
    expect AssertionDefect:
      discard svWithRaw(ctx, sv, ctx.mkFalse().toAnyAst)

suite "RFC-0016 K7b (d) -- the walker version":

  test "the version floor":
    check parseInt(symexWalkerVersion) >= 290
