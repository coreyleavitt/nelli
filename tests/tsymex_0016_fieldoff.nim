## RFC-0016 PRC-07 (variant-field half). This file builds with
## `--fieldChecks:off` (its `.nim.cfg`), on the c backend and on cpp. Nim then
## emits no `FieldDefect` check on a variant field: `v.b` is a plain union
## member access, and a write to the discriminator no longer checks that it
## stays in its branch.
##
## Native, read from the generated C of the pinned toolchain (c backend,
## `--fieldChecks:off`): `v.b` of a `ka` object is a read of the union member
## `b`, which overlaps the active `a`; a probe read the same bytes back.
##   * c backend: C11 6.5.2.3 note 95 DEFINES that read as the object
##     representation of the active member reinterpreted. The walker keeps one
##     slot per field and has no per-target byte layout of a variant, so it
##     does not model the value: the wrong-branch side is declined on its own
##     path (`fieldChecksOffLayout`, `feUnsupportedOp`), the right-branch side
##     is exact and trusted, and nothing taints the routine.
##   * cpp backend: reading a union member that is not the active one is
##     undefined in C++: that side halts as `ubInactiveVariantField` (row
##     `field/inactiveBranch`) and is an `UndefinedFinding`. A write to the
##     inactive branch halts too: C++ defines the assignment, but the walker
##     cannot hold a branch whose active member is not its discriminator's, so
##     halting (an omission) is the sound answer.
##   * either: an assignment to the discriminator that changes branch leaves
##     the new branch holding the old bytes, the `dwmHavoc` model
##     (`feUncheckedDiscBytes`, replay-confirmed).
## No sanitizer reports an inactive union member read and gcc documents it as
## type punning, so the `field/inactiveBranch` cell has no native pin; the
## native half here is that the in-branch witnesses reproduce.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

type
  K = enum ka, kb
  V = object
    case k: K
    of ka: a: int
    of kb: b: int
  RV = ref object
    case k: K
    of ka: a: int
    of kb: b: int

const fk = cellKey(axBuild, "fieldChecks=off")
const uk = cellKey(axDefinedness, "field/inactiveBranch")
const bk = cellKey(axDefinedness, "field/inactiveBytes")

proc sutIn(v: int) =
  let x = V(k: ka, a: v)
  if x.a == 7: symexTarget("hit")

proc sutWrite(v: int) =
  var x = V(k: ka, a: v)
  x.a = 9
  if x.a == 9 and v == 3: symexTarget("hit")

proc sutDiscSame(v: int) =
  var x = V(k: ka, a: v)
  x.k = ka
  if x.a == 7: symexTarget("hit")

proc sutPick(v: int) =
  let x = if v > 0: V(k: ka, a: v) else: V(k: kb, b: v)
  if x.a == 5: symexTarget("hit")

proc sutWrongRead(v: int) =
  let x = V(k: ka, a: v)
  if x.b == x.b and v == 3: symexTarget("hit")

proc sutWrongWrite(v: int) =
  var x = V(k: ka, a: v)
  x.b = 5
  if v == 3: symexTarget("hit")

proc sutDiscChange(v: int) =
  var x = V(k: ka, a: v)
  x.k = kb
  if v == 3: symexTarget("hit")

proc sutRefIn(v: int) =
  let x = RV(k: ka, a: v)
  if x.a == 7: symexTarget("hit")

proc sutRefWrongRead(v: int) =
  let x = RV(k: ka, a: v)
  if x.b == x.b and v == 3: symexTarget("hit")

proc sutRefWrongWrite(v: int) =
  let x = RV(k: ka, a: v)
  x.b = 5
  if v == 3: symexTarget("hit")

proc sutRefDiscChange(v: int) =
  let x = RV(k: ka, a: v)
  x.k = kb
  if v == 3: symexTarget("hit")

when defined(cpp):
  const wrongKind = ubInactiveVariantField
  const wrongKey = uk
else:
  const wrongKind = feUnsupportedOp
  const wrongKey = bk

suite "PRC-07: --fieldChecks:off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 306

  test "the build has the field check off and the others on":
    check coField notin buildSemantics.checks
    check coObj in buildSemantics.checks
    check coBound in buildSemantics.checks

  test "an in-branch read is exact and trusted":
    let r = pinExact(sutIn, fk, domain = sampled([7, 0, 1]))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 7
    check not r.errors.named(feCheckOption)

  test "an in-branch write is exact and trusted":
    let r = pinExact(sutWrite, fk, domain = sampled([3, 0, 1]))
    check r.status == sxSat
    check r.trusted

  test "a discriminator write inside its branch is exact":
    let r = pinExact(sutDiscSame, fk, domain = sampled([7, 0, 1]))
    check r.status == sxSat
    check r.trusted

  test "no FieldDefect is reachable":
    for r in [symexFind(sutWrongRead, tRaisedExn("FieldDefect")),
              symexFind(sutWrongWrite, tRaisedExn("FieldDefect")),
              symexFind(sutDiscChange, tRaisedExn("FieldDefect")),
              symexFind(sutRefWrongRead, tRaisedExn("FieldDefect")),
              symexFind(sutRefDiscChange, tRaisedExn("FieldDefect"))]:
      checkpoint show(r.errors)
      check r.status != sxRaised
      check not r.errors.named(feCheckOption)

  test "the in-branch side of a pick is exact, the other side is its own":
    let r = symexFind(sutPick, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 5
    check not r.errors.named(feCheckOption)
    when defined(cpp):
      check r.trusted
      check r.undefined.len == 1
      check r.undefined[0].kind == UbKind(ubInactiveVariantField)
      check "outside its branch" in r.undefined[0].site
      check "tsymex_0016_fieldoff" in r.undefined[0].site
      check r.undefined[0].witness[0] <= 0
    else:
      check r.errors.named(feUnsupportedOp)
      check "fieldChecksOffLayout" in show(r.errors)

  test "a read outside its branch":
    when defined(cpp):
      pinDecline(sutWrongRead, wrongKey, ubInactiveVariantField,
                 excluding = {feCheckOption})
    else:
      pinDecline(sutWrongRead, wrongKey, feUnsupportedOp, tLabel("hit"),
                 "fieldChecksOffLayout", excluding = {feCheckOption})

  test "a write outside its branch":
    when defined(cpp):
      pinDecline(sutWrongWrite, wrongKey, ubInactiveVariantField,
                 excluding = {feCheckOption})
    else:
      pinDecline(sutWrongWrite, wrongKey, feUnsupportedOp, tLabel("hit"),
                 "fieldChecksOffLayout", excluding = {feCheckOption})

  test "a ref variant read outside its branch":
    when defined(cpp):
      pinDecline(sutRefWrongRead, wrongKey, ubInactiveVariantField,
                 excluding = {feCheckOption})
    else:
      pinDecline(sutRefWrongRead, wrongKey, feUnsupportedOp, tLabel("hit"),
                 "fieldChecksOffLayout", excluding = {feCheckOption})

  test "a ref variant write outside its branch":
    when defined(cpp):
      pinDecline(sutRefWrongWrite, wrongKey, ubInactiveVariantField,
                 excluding = {feCheckOption})
    else:
      pinDecline(sutRefWrongWrite, wrongKey, feUnsupportedOp, tLabel("hit"),
                 "fieldChecksOffLayout", excluding = {feCheckOption})

  test "a ref variant in-branch read is exact":
    let r = pinExact(sutRefIn, fk, domain = sampled([7, 0, 1]))
    check r.status == sxSat
    check r.trusted

  test "tUndefined asks for the wrong-branch input (cpp), nothing on c":
    let r = symexFind(sutPick, tUndefined({UbKind(ubInactiveVariantField)}))
    when defined(cpp):
      check r.status == sxSat
      check r.witness[0] <= 0
      check r.soundness.undefinedKinds == {UbKind(ubInactiveVariantField)}
    else:
      check r.status != sxSat

  test "a branch-changing discriminator write holds the old bytes (havoc)":
    let r = symexFind(sutDiscChange, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.witness[0] == 3
    check r.errors.named(feUncheckedDiscBytes)
    check not r.errors.named(feCheckOption)

  test "a branch-changing discriminator write through a ref is declined, on its own path":
    let r = symexFind(sutRefDiscChange, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feUnsupportedOp)
    check "fieldChecksOffLayout" in show(r.errors)
    check not r.errors.named(feCheckOption)
