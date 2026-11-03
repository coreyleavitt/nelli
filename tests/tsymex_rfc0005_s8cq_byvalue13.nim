## RFC-0005 slice S8cq, item 1 -- a by-value formal and the memory Nim shares.
##
## Nim passes a formal by address when its type is over three words, a seq, a
## string, a set or an inheritable or `{.byref.}` object, and the walk binds it to
## a copy, so a write the callee makes through another name is read back through
## the formal natively and not in the walk: a false `sxUnsat` on the value it
## wrote and a false `sxSat` on the old one. The rule is inverted: a call is
## decided only when the type is on the allowlist (`typeCopiedByValue`, pinned on
## nine settings in `tsymex_rfc0005_s8cq_native`), or the callee with everything
## it reaches is proved to write nothing the actual could be (`byValueWritten`).
## Everything else declines; the exact model belongs to RFC-0016.
##
## A local's memory has no other name but a pointer to it, and S8bs keeps that cell
## and the formal one location, so a local actual stays decided; a formal whose
## address the callee takes, a routine actual, and a `var` of the same local decline.
import std/[unittest, strutils, sets]
import nelli
import nelli/symex

var natHits: HashSet[string]

template nat(call: untyped) =
  block:
    symexCaptureBegin()
    try:
      call
    except CatchableError:
      discard
    for h in symexCaptureEnd(): natHits.incl h

template pin(fn: typed; lbl: static string; nativeHit: bool;
             want: SymexStatusKind) =
  ## Nim's own answer on the input loop above, then the walker's. Neither may
  ## contradict the other: `sxUnknown` is the decline RFC-0016 inherits.
  block:
    let r = symexFind(fn, tLabel(lbl))
    var parts: seq[string]
    for e in r.errors: parts.add $e.kind & ": " & e.msg
    checkpoint lbl & " " & $r.status & " [" & parts.join(", ") & "]"
    check (lbl in natHits) == nativeHit
    check r.status == want
    check not (nativeHit and r.status == sxUnsat)
    check not (not nativeHit and r.status == sxSat)

template pinFree(fn: typed; lbl: static string; want: SymexStatusKind) =
  ## As `pin`, for a shape Nim gives no one answer on: only the decline holds.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status
    check r.status == want
type
  O4 = object
    x, b, c, d: int
var gs: seq[int]
var gO4: O4
var gPi: ptr int
var gPs: ptr seq[int]
var gR: ref seq[int]
proc pa(a: O4): ptr int = unsafeAddr a.x
proc keepP(a: O4) = gPi = unsafeAddr a.x
proc wg(a: seq[int]): int = (gs[0] = 50; a[0])
proc wvia(a: seq[int]): int = (gPs[][0] = 50; a[0])
proc wcell(a: seq[int]): int = (gPi[] = 50; a[0])
proc wcb(cb: proc (); a: seq[int]): int = (cb(); a[0])
proc wv(v: var seq[int]; a: seq[int]): int = (v[0] = 50; a[0])
proc wp(p: ptr seq[int]; a: seq[int]): int = (p[][0] = 50; a[0])
proc inner(a: seq[int]): int = (gPi[] = 50; a[0])
proc mid(a: seq[int]): int = inner(a)
proc wrR(a: seq[int]): int = (gR[][0] = 50; a[0])
proc l10(x: int) =
  if x == 50: return
  var s = @[x]
  gPi = addr s[0]
  let r = mid(s)
  if r == 50: symexTarget("l10_50")
  else: symexTarget("l10_n")
proc l11(x: int) =   # a local seq the local ref holds a copy of
  if x == 50: return
  new gR
  gR[] = @[x]
  var s = gR[]
  let r = wrR(s)
  if r == x: symexTarget("l11_x")
  else: symexTarget("l11_n")
proc l12(a0: seq[int]) =   # a by-value formal handed on
  if a0.len != 1 or a0[0] == 50: return
  gs = @[1]
  let r = wg(a0)
  if r == a0[0]: symexTarget("l12_x")
  else: symexTarget("l12_n")
proc l13(x: int) =   # a local object's seq field
  if x == 50: return
  type H = object
    s: seq[int]
  var h = H(s: @[x])
  gPi = addr h.s[0]
  let r = wcell(h.s)
  if r == 50: symexTarget("l13_50")
  else: symexTarget("l13_n")
proc l14(x: int) =   # a local's element seq
  if x == 50: return
  var ss = @[@[x]]
  gPs = addr ss[0]
  let r = wvia(ss[0])
  if r == 50: symexTarget("l14_50")
  else: symexTarget("l14_n")
proc l15(x: int) =   # a pointer to a pointer
  if x == 50: return
  var s = @[x]
  var q = addr s
  gPs = q
  let r = wvia(s)
  if r == 50: symexTarget("l15_50")
  else: symexTarget("l15_n")
var gPR: ptr ref int
proc wPR(a: ref int): int =
  new gPR[]
  gPR[][] = 50
  a[]
proc l16(x: int) =   # a local ref, overwritten through a global pointer to it
  if x == 50: return
  var r: ref int
  new r
  r[] = x
  gPR = addr r
  let v = wPR(r)
  if v == x: symexTarget("l16_x")
  if v != x: symexTarget("l16_n")

for x in [1, 2]:
  nat(l10(x))
  nat(l11(x))
  nat(l12(@[x]))
  nat(l13(x))
  nat(l14(x))
  nat(l15(x))
  nat(l16(x))

suite "tsymex_rfc0005_s8cq_byvalue13":
  test "verdicts against Nim":
    pin(l10, "l10_50", true, sxSat)
    pin(l10, "l10_n", false, sxUnsat)
    pin(l11, "l11_x", true, sxSat)
    pin(l11, "l11_n", false, sxUnsat)
    pin(l12, "l12_x", true, sxSat)
    pin(l12, "l12_n", false, sxUnsat)
    pin(l13, "l13_50", true, sxUnknown)
    pin(l13, "l13_n", false, sxUnknown)
    pin(l14, "l14_50", true, sxUnknown)
    pin(l14, "l14_n", false, sxUnknown)
    pin(l15, "l15_50", true, sxSat)
    pin(l15, "l15_n", false, sxUnsat)
    pinFree(l16, "l16_x", sxUnknown)
    pinFree(l16, "l16_n", sxUnknown)
