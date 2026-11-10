## RFC-0016 E3b -- the read-only table is the decision, not a ledger beside it.
##
## `mayWrite` (and the two hook routes behind `routeStoresThroughDeref` /
## `routeHookCopies`) classify each node into a `WriteShape` and ask
## `admitShape`; the decline message carries the row's reason, which names its
## cell (`readonly:<route>/<shape>`). No hook can swap the `const` table under
## the macro, so the behavioural check is the message: a verdict decided by a
## private allowlist would not name the row. The structural half pins that
## every shape of every route reads a row or the absent `<route>/unlisted`
## key (the default is a decline).
import std/[unittest, strutils, options]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/readonlyaxes
import nelli/smt/admission
import nelli/smt/errorkind
import ./s8cu_helpers

var gs: seq[int]
var gpq: ptr seq[int]

proc bump() = inc(gpq[][0])
proc pongW(k: int)
proc pingW(k: int) =
  if k > 0: pongW(k - 1) else: inc(gpq[][0])
proc pongW(k: int) = pingW(k)
proc pongP(k: int): int
proc pingP(k: int): int =
  if k > 0: pongP(k - 1) else: 0
proc pongP(k: int): int = pingP(k)
proc cMemset(s: pointer; c: cint; n: csize_t): pointer
  {.importc: "memset", header: "<string.h>", discardable.}

template shape(name: untyped; lNew: static string; newV: untyped;
               body: untyped) {.dirty.} =
  proc name(n: int) =
    if n > 1000 or n < -1000 or n == 99 or n == 0: return
    gs = @[n]
    gpq = addr gs
    for x in gs:
      body
      if x == newV: symexTarget(lNew)

shape(wDeref, "wDeref_new", 99): gpq[][0] = 99
shape(wWalked, "wWalked_new", n + 1): bump()
shape(wRecPair, "wRecPair_new", n + 1): pingW(2)
shape(wRecPure, "wRecPure_new", 99): discard pingP(2)
shape(wOpaque, "wOpaque_new", 0): cMemset(addr gpq[][0], 0, 8)
shape(wCast, "wCast_new", n + 1):
  inc(cast[ptr int](cast[pointer](addr gpq[][0]))[])

template declinesAt(fn: typed; lbl: static string; cell: static string) =
  pinDecline(fn, cellKey(axReadOnly, cell), feUnsupportedOp, tLabel(lbl),
             needle = "readonly:" & cell & ": ")

# ---- hooks ------------------------------------------------------------------
type
  RCell = ref object
    v: int
  StoreC = object
    v: int
    r: RCell
  CallC = object
    v: int
    r: RCell
  ZapC = object
    v: int
  CondC = object
    v: int

proc bumpR(c: RCell) = c.v = 5
proc zap(x: var ZapC) = x.v = 0
proc `=copy`(a: var StoreC; b: StoreC) =
  a.v = b.v
  a.r = b.r
  b.r.v = 5
proc `=copy`(a: var CallC; b: CallC) =
  a.v = b.v
  a.r = b.r
  bumpR(b.r)
proc `=copy`(a: var ZapC; b: ZapC) =
  a.v = b.v
  zap(a)
proc `=copy`(a: var CondC; b: CondC) =
  if b.v > 0: a.v = b.v

template storeShape(name: untyped; T: typedesc; lbl: static string) =
  proc name(k: int) =
    var c = RCell(v: 0)
    var x = T(v: k, r: c)
    var y = x
    x.v = 0
    if c.v != 0 and y.v == k: symexTarget(lbl & "_stored")
template copyShape(name: untyped; T: typedesc; lbl: static string) =
  proc name(k: int) =
    var x = T(v: k)
    var y = x
    x.v = 0
    y.v = y.v
    if y.v != k: symexTarget(lbl & "_changed")
storeShape(store1, StoreC, "store1")
storeShape(call1, CallC, "call1")
copyShape(zap1, ZapC, "zap1")
copyShape(cond1, CondC, "cond1")

suite "E3b: the decline names the table's row":
  test "lent: a direct store":
    declinesAt(wDeref, "wDeref_new", "lent/deref-store")
  test "lent: a walked callee that writes":
    declinesAt(wWalked, "wWalked_new", "lent/walked-write")
  test "lent: a recursive pair that writes":
    declinesAt(wRecPair, "wRecPair_new", "lent/recursive-write")
  test "lent: a recursive pair that does not":
    declinesAt(wRecPure, "wRecPure_new", "lent/recursive-pure")
  test "lent: an opaque callee":
    declinesAt(wOpaque, "wOpaque_new", "lent/opaque-callee")
  test "lent: a cast":
    declinesAt(wCast, "wCast_new", "lent/cast-emit")
  test "hookstore: a direct store, a walked one":
    pinDecline(store1, cellKey(axReadOnly, "hookstore/direct-store"),
               feGlobalRouteUnproved, tLabel("store1_stored"),
               needle = "readonly:hookstore/direct-store: ")
    pinDecline(call1, cellKey(axReadOnly, "hookstore/walked-store"),
               feGlobalRouteUnproved, tLabel("call1_stored"),
               needle = "readonly:hookstore/walked-store: ")
  test "hookcopy: a callee after the copy, a conditional copy":
    pinDecline(zap1, cellKey(axReadOnly, "hookcopy/callee-write"),
               feGlobalRouteUnproved, tLabel("zap1_changed"),
               needle = "readonly:hookcopy/callee-write: ")
    pinDecline(cond1, cellKey(axReadOnly, "hookcopy/conditional"),
               feGlobalRouteUnproved, tLabel("cond1_changed"),
               needle = "readonly:hookcopy/conditional: ")

suite "E3b: every shape reads the table":
  const routes = [rrLent, rrHookCopy, rrHookStore]
  test "a shape reads a row or the absent unlisted key":
    for r in routes:
      for s in WriteShape:
        let k = shapeKey(r, s)
        check readOnlyAxis.hasRow(k) or k.endsWith("/unlisted")
  test "an unlisted shape declines by default, as feUnadmitted":
    for r in routes:
      let a = admitShape(r, wsUnlisted)
      check not a.admitted
      check a.decline[0] == some(feUnadmitted)
  test "every row of the three mayWrite routes is read by some shape":
    for k in readOnlyAxis.keys:
      if k.startsWith("lent/") or k.startsWith("hookcopy/") or
         k.startsWith("hookstore/"):
        var read = false
        for r in routes:
          for s in WriteShape:
            if shapeKey(r, s) == k: read = true
        check read
