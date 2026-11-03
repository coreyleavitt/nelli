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
proc l01(x: int) =
  if x == 50: return
  var o = O4(x: x)
  pa(o)[] = 50
  if o.x == 50: symexTarget("l01_w")
  else: symexTarget("l01_n")
proc l02(x: int) =
  if x == 50: return
  var o = O4(x: x)
  keepP(o)
  o.x = 50
  if gPi[] == 50: symexTarget("l02_w")
  else: symexTarget("l02_n")
proc l03(x: int) =
  if x == 50: return
  var s = @[x]
  gs = @[1]
  let r = wg(s)
  if r == x: symexTarget("l03_x")
  else: symexTarget("l03_n")
proc l04(x: int) =
  if x == 50: return
  var s = @[x]
  gPs = addr s
  let r = wvia(s)
  if r == 50: symexTarget("l04_50")
  else: symexTarget("l04_n")
proc l05(x: int) =
  if x == 50: return
  var s = @[x]
  gPi = addr s[0]
  let r = wcell(s)
  if r == 50: symexTarget("l05_50")
  else: symexTarget("l05_n")
proc l06(x: int) =
  if x == 50: return
  var s = @[x]
  let c = proc () = s[0] = 50
  let r = wcb(c, s)
  if r == 50: symexTarget("l06_50")
  else: symexTarget("l06_n")
proc l07(x: int) =
  if x == 50: return
  var s = @[x]
  let r = wv(s, s)
  if r == 50: symexTarget("l07_50")
  else: symexTarget("l07_n")
proc l08(x: int) =
  if x == 50: return
  var s = @[x]
  let r = wp(addr s, s)
  if r == 50: symexTarget("l08_50")
  else: symexTarget("l08_n")
proc l09(x: int) =
  if x == 50: return
  var s = @[x]
  let p = addr s
  let r = wp(p, s)
  if r == 50: symexTarget("l09_50")
  else: symexTarget("l09_n")
var gPR: ptr ref int
proc wPR(a: ref int): int =
  new gPR[]
  gPR[][] = 50
  a[]

for x in [1, 2]:
  nat(l01(x))
  nat(l02(x))
  nat(l03(x))
  nat(l04(x))
  nat(l05(x))
  nat(l06(x))
  nat(l07(x))
  nat(l08(x))
  nat(l09(x))

suite "tsymex_rfc0005_s8cq_byvalue12":
  test "verdicts against Nim":
    pin(l01, "l01_w", true, sxUnknown)
    pin(l01, "l01_n", false, sxUnknown)
    pin(l02, "l02_w", true, sxUnknown)
    pin(l02, "l02_n", false, sxUnknown)
    pin(l03, "l03_x", true, sxSat)
    pin(l03, "l03_n", false, sxUnsat)
    pin(l04, "l04_50", true, sxSat)
    pin(l04, "l04_n", false, sxUnsat)
    pin(l05, "l05_50", true, sxSat)
    pin(l05, "l05_n", false, sxUnsat)
    pin(l06, "l06_50", true, sxUnknown)
    pin(l06, "l06_n", false, sxUnknown)
    pin(l07, "l07_50", true, sxUnknown)
    pin(l07, "l07_n", false, sxUnknown)
    pin(l08, "l08_50", true, sxUnknown)
    pin(l08, "l08_n", false, sxUnknown)
    pin(l09, "l09_50", true, sxUnknown)
    pin(l09, "l09_n", false, sxUnknown)
