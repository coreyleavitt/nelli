## RFC-0016 PRC-08. This file builds with `-d:danger` (its `.nim.cfg`, with
## `--opt:none` as `tsymex_rfc0005_s8cu_cl_danger` has). `-d:danger` turns
## every runtime check off: the field, range, bound, object and overflow
## checks and the assertions; the float checks stay at their default, off.
## The build is walked as compiled, one SUT per kind of unchecked operation:
##   range         a narrowing conversion is the plain C cast (exact)
##   bound         an access outside the array is undefined (`index/unchecked`)
##   field         a read outside the variant's branch: the union's bytes on
##                 c (exact), the inactive member on cpp (undefined)
##   object        a down-conversion of the wrong dynamic type is undefined
##   indeterminate a `{.noinit.}` read of an unwritten slot (the convention
##                 every build shares)
##   float         no float operation is checked unless a routine pushes it
##                 on, and a push still turns it on
## Each option the build profile and `check_options` read is checked off.
import std/[unittest, options, macros]
import nelli
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/buildprofile
import nelli/smt/check_options
import ./s8cu_helpers

static:
  doAssert defined(danger), "tsymex_0016_danger builds with -d:danger"

const
  rk = cellKey(axBuild, "rangeChecks=off")
  ik = cellKey(axDefinedness, "index/unchecked")
  bk = cellKey(axBuild, "boundChecks=off")
  ok = cellKey(axBuild, "objChecks=off")
  fk = cellKey(axBuild, "fieldChecks=off")
  uk = cellKey(axDefinedness, "field/inactiveBranch")
  ck = cellKey(axDefinedness, "conv/objDowncast")
  nanK = cellKey(axPragma, "routine/nanChecks")
  floats = sampled([0.0, 1.0, -1.0, 2.0, Inf, NegInf, NaN])

type
  K = enum ka, kb
  V = object
    case k: K
    of ka: a: int
    of kb: b: int
  Base = ref object of RootObj
    x: int
  Der = ref object of Base
    y: int

proc sutNarrow(v: int) =
  if v > 127 and int8(v) == 44'i8: symexTarget("hit")

proc sutRangeKept(v: int) =
  let n = Natural(v)
  if int(n) == -3: symexTarget("hit")

proc sutArrOob(v: int) =
  var a: array[5, int]
  a[v] = 1
  if v < 0 or v > 4: symexTarget("hit")

proc sutArrIn(v: int) =
  var a: array[5, int]
  a[v] = 1
  if a[2] == 1: symexTarget("hit")

proc sutWrongRead(v: int) =
  let x = V(k: ka, a: v)
  if x.b == 3: symexTarget("hit")

proc sutObjBad(v: int) =
  let b: Base = Base(x: v)
  let d = Der(b)
  if v == 3: symexTarget("hit")

proc sutObjGood(v: int) =
  let b: Base = Der(x: v, y: 5)
  let d = Der(b)
  if d.y == 5 and d.x == 7: symexTarget("hit")

proc sutNoinit() =
  var x {.noinit.}: int
  if x == 0: symexTarget("z")

proc sutFloatPlain(a: float) =
  let r = a / 0.0
  if r != r: symexTarget("hit")

{.push nanChecks: on.}
proc sutFloatPushed(a: float) =
  let r = a / 0.0
  if r != r: symexTarget("hit")
{.pop.}

macro readChecks(fn: typed): untyped =
  ## `check_options.routineChecks` of `fn`, read at compile time.
  let c = routineChecks(fn.getImpl)
  newLit((checks: c.checks, why: c.why, rangeOn: c.rangeOn,
          boundOn: c.boundOn, fieldOn: c.fieldOn, objOn: c.objOn,
          nanOn: c.nanOn, infOn: c.infOn, overflowOn: c.overflowOn))

template decided(body: untyped) =
  ## A verdict is decided only on a verified build row; cpp under Z3 4.13.4
  ## has none by design (`feHostUnadmitted`).
  if hostAdmission().isSome:
    skipUnadmitted()
  else:
    body

suite "PRC-08: -d:danger reads every check off":
  test "the build profile":
    check buildSemantics.danger
    check buildSemantics.checks == {}

  test "check_options: no routine is checked, none deviates":
    for c in [readChecks(sutNarrow), readChecks(sutArrOob),
              readChecks(sutWrongRead), readChecks(sutObjBad),
              readChecks(sutFloatPlain)]:
      checkpoint $c
      check c.why.len == 0
      check c.checks * {coRange, coBound, coField, coObj, coNan, coInf} == {}
      check not (c.rangeOn or c.boundOn or c.fieldOn or c.objOn or
                 c.nanOn or c.infOn or c.overflowOn)
    let p = readChecks(sutFloatPushed)
    check p.nanOn
    check not p.infOn

suite "PRC-08: -d:danger, one SUT per unchecked kind":
  test "range: a narrowing conversion is the plain cast":
    decided:
      check native(sutNarrow(300)) == "hit"
      check native(sutRangeKept(-3)) == "hit"
      check pinExact(sutNarrow, rk, domain = sampled([300, 0, 127])).status == sxSat
      check pinExact(sutRangeKept, rk, domain = sampled([-3, 0, 1])).status == sxSat

  test "bound: an access outside the array is undefined":
    decided:
      check native(sutArrIn(2)) == "hit"
      check pinExact(sutArrIn, bk, domain = sampled([2, 0, 4])).status == sxSat
      pinDecline(sutArrOob, ik, ubArrayOutOfBounds, excluding = {feCheckOption})

  test "field: a read outside the branch":
    decided:
      when defined(cpp):
        pinDecline(sutWrongRead, uk, ubInactiveVariantField,
                   excluding = {feCheckOption})
      else:
        check native(sutWrongRead(3)) == "hit"
        let r = pinExact(sutWrongRead, fk, domain = sampled([3, 0, 1]))
        check r.status == sxSat
        check r.witness[0] == 3

  test "object: a down-conversion of the wrong type is undefined":
    decided:
      check native(sutObjGood(7)) == "hit"
      check pinExact(sutObjGood, ok, domain = sampled([7, 0, 1])).status == sxSat
      pinDecline(sutObjBad, ck, ubInvalidObjConversion,
                 excluding = {feCheckOption})

  test "indeterminate: a noinit read of an unwritten slot":
    decided:
      let r = symexFind(sutNoinit, tLabel("z"), settings = pinSettingsConst)
      checkpoint show(r.errors) & " " & $r.soundness
      check not r.trusted
      check not r.errors.named(feCheckOption)
      check r.status in {sxSat, sxUnknown}
      if r.status == sxSat:
        check r.soundness.undefinedKinds == {UbKind(ubIndeterminateRead)}

  test "float: unchecked by default, a push still checks":
    decided:
      check native(sutFloatPlain(0.0)) == "hit"
      check pinExact(sutFloatPlain, nanK, domain = floats).status == sxSat
      check pinExact(sutFloatPlain, nanK, target = tRaisedExn(),
                     domain = floats).status == sxUnsat
      check native(sutFloatPushed(0.0)) == "FloatInvalidOpDefect"
      let p = pinExact(sutFloatPushed, nanK, target = tRaisedExn(),
                       domain = floats)
      check p.status == sxRaised
      check p.raisedTypeId == "FloatInvalidOpDefect"
