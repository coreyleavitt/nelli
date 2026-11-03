## RFC-0005 S8cp, item 2, continued (`tsymex_rfc0005_s8cp_unchecked` has the plain
## object; split for the Windows per-file budget). An object with a destructor zeroes
## the case's memory when its discriminator takes another value under
## `{.cast(uncheckedAssign).}`; a hook on the object itself does too, which no macro
## can see; and the shapes that decline.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if e.severity != sevHint: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(sut: untyped; target: SymexTarget; want: SymexStatusKind) =
  let r = symexFind(sut, target)
  checkpoint $r.status & " " & show(r.errors)
  check r.status == want

type
  K = enum kA, kB, kC, kD
  Plain = object
    h: int
    case k: K
    of kA, kB: x: int
    of kC: y: int
    else: discard
  Managed = object
    h: int
    case k: K
    of kA, kB: x, x2: int
    of kC: y: int
    of kD: s: string
  Hooked = object
    case k: K
    of kA, kB: x: int
    of kC: y: int
    else: discard
  K2 = enum m1, m2
  Axes = object
    case a: K
    of kA, kB: ax: int
    of kC: ay: string
    else: discard
    case b: K2
    of m1: bx: int
    of m2: by: int
  Holder = object
    w: Managed

  TwoPlain = object
    case a: K
    of kA, kB: ax: int
    of kC: ay: int
    else: discard
    case b: K2
    of m1: bx: int
    of m2: by: int
  BoolTag = object
    case k: bool
    of true: a: int
    of false: b: int

proc `=copy`(a: var Hooked; b: Hooked) {.error.}

# ---- an object with a destructor --------------------------------------------

proc zeroesInBranch(v: int) =
  symexAssume(v != 0)
  var o = Managed(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kB
  if o.x == 0: symexTarget("zero")
  if o.x == v: symexTarget("kept")

proc zeroesAcross(v: int) =
  symexAssume(v != 0)
  var o = Managed(h: v, k: kA, x: v, x2: v)
  {.cast(uncheckedAssign).}:
    o.k = kC
  if o.y == 0 and o.h == v: symexTarget("zero")
  if o.y != 0: symexTarget("kept")
  if o.h != v: symexTarget("plainGone")

proc roundTrip(v: int) =
  symexAssume(v != 0)
  var o = Managed(k: kA, x: v, x2: v)
  {.cast(uncheckedAssign).}:
    o.k = kC
    o.k = kA
  if o.x == 0 and o.x2 == 0: symexTarget("zero")
  if o.x == v: symexTarget("kept")

proc sameValueKeeps(v: int) =
  var o = Managed(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kA
  if o.x == v: symexTarget("kept")
  if o.x != v: symexTarget("gone")

proc freeManaged(v: int; t: K) =
  symexAssume(v != 0)
  var o = Managed(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = t
  if t == kA and o.x == v: symexTarget("kept")
  if t == kB and o.x == v: symexTarget("keptOther")
  if t == kB and o.x == 0: symexTarget("zeroOther")

proc stringArm(v: int) =
  var o = Managed(k: kD, s: "abc")
  {.cast(uncheckedAssign).}:
    o.k = kA
    o.k = kD
  if o.s.len == 0: symexTarget("empty")
  if o.s.len != 0: symexTarget("full")

proc axesManaged(v: int) =
  symexAssume(v != 0)
  var o = Axes(a: kA, ax: v, b: m1, bx: v)
  {.cast(uncheckedAssign).}:
    o.b = m2
  if o.by == 0 and o.ax == v: symexTarget("zero")
  if o.by != 0 or o.ax != v: symexTarget("other")

proc fieldChain(v: int) =
  symexAssume(v != 0)
  var o = Holder(w: Managed(k: kA, x: v))
  {.cast(uncheckedAssign).}:
    o.w.k = kB
  if o.w.x == 0: symexTarget("zero")
  if o.w.x == v: symexTarget("kept")

# ---- a hook the walker cannot see, and what declines ------------------------

proc hookedZeroes(v: int) =
  symexAssume(v != 0)
  var o: Hooked
  o.x = v
  {.cast(uncheckedAssign).}:
    o.k = kB
  if o.x == 0: symexTarget("zero")
  if o.x == v: symexTarget("kept")

proc passK(t: var K) = t = kC

proc viaVarArg(v: int) =
  var o = Plain(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    passK(o.k)
  if o.k == kC: symexTarget("live")
  if o.k != kC: symexTarget("dead")

proc viaAddr(v: int) =
  var o = Plain(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    let p = addr o.k
    p[] = kC
  if o.k == kC: symexTarget("live")
  if o.k != kC: symexTarget("dead")

proc viaRef(v: int) =
  var o = new Plain
  o[] = Plain(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kC
  if o.k == kC: symexTarget("live")
  if o.k != kC: symexTarget("dead")

proc pointerIntoArm(v: int) =
  var o = Plain(k: kA, x: v)
  let p = addr o.x
  {.cast(uncheckedAssign).}:
    o.k = kC
  p[] = v + 1
  if o.y == v + 1: symexTarget("live")
  if o.y == v: symexTarget("dead")

proc raises(body: proc ()): bool =
  try:
    body()
  except FieldDefect:
    result = true

suite "RFC-0005 S8cp (2): the compiled program, zeroing and declined shapes":
  test "no raise under the pragma":
    check not raises(proc () = viaVarArg(3))
    check not raises(proc () = viaAddr(3))
    check not raises(proc () = viaRef(3))
    check not raises(proc () = pointerIntoArm(3))
  test "the labels each shape reaches":
    template hits(call: untyped): HashSet[string] =
      symexCaptureBegin()
      call
      symexCaptureEnd()
    check hits(zeroesInBranch(3)) == ["zero"].toHashSet
    check hits(zeroesAcross(3)) == ["zero"].toHashSet
    check hits(roundTrip(3)) == ["zero"].toHashSet
    check hits(sameValueKeeps(3)) == ["kept"].toHashSet
    check hits(freeManaged(3, kA)) == ["kept"].toHashSet
    check hits(freeManaged(3, kB)) == ["zeroOther"].toHashSet
    check hits(stringArm(3)) == ["empty"].toHashSet
    check hits(axesManaged(3)) == ["zero"].toHashSet
    check hits(fieldChain(3)) == ["zero"].toHashSet
    check hits(hookedZeroes(3)) == ["zero"].toHashSet
    check hits(viaVarArg(3)) == ["live"].toHashSet
    check hits(viaAddr(3)) == ["live"].toHashSet
    check hits(viaRef(3)) == ["live"].toHashSet
    check hits(pointerIntoArm(3)) == ["live"].toHashSet

suite "RFC-0005 S8cp (2): an object with a destructor":
  test "a new value in the branch zeroes it (kept was a false sxUnsat of the live label)":
    verdict(zeroesInBranch, tLabel("zero"), sxSat)
    verdict(zeroesInBranch, tLabel("kept"), sxUnsat)
    verdict(zeroesInBranch, tFieldDefect(), sxUnsat)
  test "across branches, keeping the plain field":
    verdict(zeroesAcross, tLabel("zero"), sxSat)
    verdict(zeroesAcross, tLabel("kept"), sxUnsat)
    verdict(zeroesAcross, tLabel("plainGone"), sxUnsat)
  test "there and back":
    verdict(roundTrip, tLabel("zero"), sxSat)
    verdict(roundTrip, tLabel("kept"), sxUnsat)
  test "the same value changes nothing":
    verdict(sameValueKeeps, tLabel("kept"), sxSat)
    verdict(sameValueKeeps, tLabel("gone"), sxUnsat)
  test "a symbolic tag decides by value":
    verdict(freeManaged, tLabel("kept"), sxSat)
    verdict(freeManaged, tLabel("keptOther"), sxUnsat)
    verdict(freeManaged, tLabel("zeroOther"), sxSat)
  test "a string arm":
    verdict(stringArm, tLabel("empty"), sxSat)
    verdict(stringArm, tLabel("full"), sxUnsat)
  test "one axis of two":
    verdict(axesManaged, tLabel("zero"), sxSat)
    verdict(axesManaged, tLabel("other"), sxUnsat)
  test "a field chain":
    verdict(fieldChain, tLabel("zero"), sxSat)
    verdict(fieldChain, tLabel("kept"), sxUnsat)

suite "RFC-0005 S8cp (2): a hook, and the shapes that decline":
  test "a hook on the object: a plain-looking object zeroes, and no label is wrong":
    verdict(hookedZeroes, tLabel("zero"), sxSat)
    let r = symexFind(hookedZeroes, tLabel("kept"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
  test "a var argument":
    verdict(viaVarArg, tLabel("live"), sxUnknown)
    verdict(viaVarArg, tLabel("dead"), sxUnknown)
  test "addr":
    verdict(viaAddr, tLabel("live"), sxUnknown)
    verdict(viaAddr, tLabel("dead"), sxUnknown)
  test "through a ref":
    verdict(viaRef, tLabel("live"), sxUnknown)
    verdict(viaRef, tLabel("dead"), sxUnknown)
  test "a pointer into the old arm":
    verdict(pointerIntoArm, tLabel("live"), sxUnknown)
    verdict(pointerIntoArm, tLabel("dead"), sxUnknown)

suite "RFC-0005 S8cp: walker version":
  test "symexWalkerVersion is at least 253":
    check parseInt(symexWalkerVersion) >= 253
