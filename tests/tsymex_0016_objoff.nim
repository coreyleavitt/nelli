## RFC-0016 PRC-07 (object-conversion half). This file builds with
## `--objChecks:off` (its `.nim.cfg`). Nim then emits no `isObjDisplayCheck`
## for `Derived(b)` of a `ref`: the conversion always succeeds, so a `b`
## whose dynamic type is not a `Derived` is used as one. That is type
## confusion: field reads and writes go through an incompatible type, and past
## the allocation when `Derived` is the larger. The walker answers it on the
## definedness axis (row `conv/objDowncast`, `ubInvalidObjConversion`): the
## subtype side stays exact and trusted, the failing side halts at the
## conversion and is an `UndefinedFinding` with its site. It is not an
## `ObjectConversionDefect` (a checked build's answer) and not a
## `feCheckOption` decline of every routine (what an objChecks-off build used
## to do).
##
## Native, read from the generated C of the pinned toolchain (`--objChecks:off`
## against the default build): `isObjDisplayCheck` is absent from the cast, so
## `Der(b)` on a `Base` succeeds and `d.y` reads another object's bytes (a
## probe printed 0 and 2 for two bases). AddressSanitizer over `-d:useMalloc`
## sees the read past the allocation when the derived type is larger
## (`ubsan_support.objProbeSrc`); a derived type no larger would read inside
## the allocation, which no sanitizer calls out.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/definedness
import nelli/smt/errorkind
import ./s8cu_helpers
import ./ubsan_support

type
  Base = ref object of RootObj
    x: int
  Der = ref object of Base
    y: int

const ok = cellKey(axBuild, "objChecks=off")
const ck = cellKey(axDefinedness, "conv/objDowncast")

proc sutSub(v: int) =
  let b: Base = Der(x: v, y: 5)
  let d = Der(b)
  if d.y == 5 and d.x == 7: symexTarget("hit")

proc sutNil(v: int) =
  var b: Base = nil
  let d = Der(b)
  if d == nil and v == 1: symexTarget("hit")

# The label is past the conversion and reachable by either dynamic type: the
# `Base` side is undefined, so the conversion halts it.
proc sutBase(v: int) =
  let b: Base = Base(x: v)
  let d = Der(b)
  if v == 3: symexTarget("hit")

proc sutPick(v: int) =
  let b: Base = if v > 0: Der(x: v, y: 5) else: Base(x: v)
  let d = Der(b)
  if v > 0 and d.y == 5: symexTarget("hit")

proc sutPickBad(v: int) =
  let b: Base = if v > 0: Der(x: v, y: 5) else: Base(x: v)
  let d = Der(b)
  if v <= 0: symexTarget("hit")

{.push objChecks: on.}
proc sutPushedOn(v: int) =
  let b: Base = Base(x: v)
  let d = Der(b)
  if v == 3: symexTarget("hit")
{.pop.}

suite "PRC-07: --objChecks:off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 309

  test "the build has the object check off and the others on":
    check coObj notin buildSemantics.checks
    check coField in buildSemantics.checks
    check coRange in buildSemantics.checks

  test "a conversion to the dynamic type is exact and trusted":
    let r = pinExact(sutSub, ok, domain = sampled([7, 0, 1]))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 7

  test "a nil converts, exact":
    let r = pinExact(sutNil, ok, domain = sampled([1, 0]))
    check r.status == sxSat
    check r.trusted

  test "the subtype side of a pick is exact, the Base side is a finding":
    let r = symexFind(sutPick, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] > 0
    check r.trusted
    check not r.errors.named(feCheckOption)
    check r.undefined.len == 1
    check r.undefined[0].kind == UbKind(ubInvalidObjConversion)
    check "tsymex_0016_objoff" in r.undefined[0].site
    check r.undefined[0].witness[0] <= 0

  test "a Base converted to a Der halts as undefined":
    pinDecline(sutBase, ck, ubInvalidObjConversion,
               excluding = {feCheckOption})

  test "a label reachable only through the failing side halts as undefined":
    pinDecline(sutPickBad, ck, ubInvalidObjConversion,
               excluding = {feCheckOption})

  test "no ObjectConversionDefect is reachable":
    let r = symexFind(sutBase, tRaisedExn("ObjectConversionDefect"))
    checkpoint show(r.errors)
    check r.status != sxRaised
    check not r.errors.named(feCheckOption)

  test "tUndefined asks for the failing input":
    let r = symexFind(sutPick, tUndefined({UbKind(ubInvalidObjConversion)}))
    check r.status == sxSat
    check r.witness[0] <= 0
    check not r.trusted
    check r.soundness.undefinedKinds == {UbKind(ubInvalidObjConversion)}

  test "a routine pushed back to objChecks: on is walked checked (its own options)":
    ## its down-conversion raises natively, so the build's unchecked model must not apply
    let r = symexFind(sutPushedOn, tRaisedExn("ObjectConversionDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    check not r.errors.named(feCheckOption)
    check r.undefined.len == 0

suite "PRC-07: conv/objDowncast against C (objChecks:off)":
  when defined(windows):
    test "no AddressSanitizer on this toolchain: the cell is declared, not run":
      skipCell(ck, "AddressSanitizer does not exist for mingw gcc or MSVC; " &
        "the cell is pinned by the walker half and by the Linux legs' " &
        "-fsanitize=address run")
  else:
    test "a down-conversion of a smaller object against -fsanitize=address":
      let p = buildObjProbe("objoff-asan",
                            objAsanFlags(["--objChecks:off"]))
      defer: dispose(p)
      var cases: seq[UbCase]
      for (ty, outside) in [("base", true), ("der", false), ("nil", false)]:
        let expect =
          if outside and admitDefined(aoConv, ocObjDowncast, dsConv).payload[
               dpChecked].kind == dkUndefined: ueTrip
          else: ueClean
        cases.add UbCase(ty: ty, op: "rd", a: 0, b: 0, expect: expect,
                         cond: outside)
      pinUbsanCell(ck, p, cases)
