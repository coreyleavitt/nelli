## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, items 2
## and 3: a call through a closure or a proc value into a variable whose
## address is taken, and `addr` of a part of an address-taken variable.
##
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (2) a closure or proc-value call binds each formal whose actual is an
##       address-taken variable, or a path into one, to the variable's cell
##       (`bindVarLocs`, as a direct call does since S8bs): a `var` actual by
##       name or by path, and a by-value argument Nim passes by address (a
##       large object: the walk passed a copy, and the callee's write through
##       the alias was lost -- swapped verdicts);
##   (3) `addr b.x` of an address-taken `b` is a sub-cell of `b`'s cell at
##       `.x`, for a direct call and a closure call alike.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint

template declines(fn: typed, lbl, why: string): untyped =
  ## A shape the walk does not model: `sxUnknown`, with the decline named.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 3, 5, 7]

type Box = object
  x: int

type Big = object
  x, a, b, c: int

var gpb: ptr Box
var gpi: ptr int
var gpbg: ptr Big

# ---- (2) a `var` actual that is a path into an address-taken variable ------

proc setXAfter(v: var int, k: int) =
  v = k
  gpb[].x = 5

proc sutPvPath(k: int) =
  ## A proc value; the write through the alias comes last.
  var b = Box(x: 0)
  gpb = addr b
  let f = setXAfter
  f(b.x, k)
  if b.x == 5 and k == 3: symexTarget("pp")
  if b.x != 5: symexTarget("pp_dead")

proc sutLamPath(k: int) =
  ## A lambda; the write through the formal comes last.
  var b = Box(x: 0)
  gpb = addr b
  let f = proc (v: var int, k: int) =
    gpb[].x = 5
    v = k
  f(b.x, k)
  if b.x == k and k == 3: symexTarget("lp")
  if b.x != k: symexTarget("lp_dead")

proc sutLamPathBranch(k: int) =
  ## A lambda with two exits, one writing through each name.
  var b = Box(x: 0)
  gpb = addr b
  let f = proc (v: var int, k: int) =
    if k > 2:
      v = k
      gpb[].x = 7
    else:
      gpb[].x = 9
      v = 1
  f(b.x, k)
  if b.x == 7 and k == 3: symexTarget("lb")
  if b.x == 1 and k == 0: symexTarget("lb2")
  if (k > 2 and b.x != 7) or (k <= 2 and b.x != 1):
    symexTarget("lb_dead")

# ---- (2) a `var` actual that is the address-taken variable itself ----------

proc setIAfter(v: var int, k: int) =
  v = k
  gpi[] = 5

proc sutPvWhole(k: int) =
  var x = 0
  gpi = addr x
  let f = setIAfter
  f(x, k)
  if x == 5 and k == 3: symexTarget("pw")
  if x != 5: symexTarget("pw_dead")

proc sutLamWholeRead(k: int) =
  ## The formal read after a write through the alias. `v * 2` crosses the
  ## Int-heap bridge: lowered at the Int it gave Z3 a query its step count
  ## never ended (`probeProto`, S8bu item 1).
  if k < 0 or k > 1000: return
  var x = 0
  gpi = addr x
  let f = proc (v: var int, k: int): int =
    v = k
    gpi[] = v * 2
    v
  let r = f(x, k)
  if r == 2 * k and x == 2 * k and k == 3: symexTarget("lw")
  if r != 2 * k or x != 2 * k: symexTarget("lw_dead")

# ---- (2) a by-value argument Nim passes by address -------------------------

proc rdBig(b: Big, k: int): int =
  gpbg[].x = k
  b.x

proc sutPvBig(k: int) =
  ## An object larger than three words is passed by address: the read
  ## after the write through the alias sees it. The walk passed a copy
  ## (swapped verdicts).
  var bg = Big(x: 0)
  gpbg = addr bg
  let f = rdBig
  let r = f(bg, k)
  if r == k and k == 3: symexTarget("pg")
  if r != k: symexTarget("pg_dead")

# ---- (3) `addr` of a part of an address-taken variable ---------------------

proc rdXAddr(p: ptr int, k: int): int =
  gpb[].x = k
  p[]

proc sutDirectAddrPart(k: int) =
  var b = Box(x: 0)
  gpb = addr b
  let r = rdXAddr(addr b.x, k)
  if r == k and b.x == k and k == 3: symexTarget("da")
  if r != k or b.x != k: symexTarget("da_dead")

proc wrXAddr(p: ptr int, k: int) =
  gpb[].x = 5
  p[] = k

proc sutDirectAddrPartWrite(k: int) =
  var b = Box(x: 0)
  gpb = addr b
  wrXAddr(addr b.x, k)
  if b.x == k and k == 3: symexTarget("dw")
  if b.x != k: symexTarget("dw_dead")

proc sutPvAddrPart(k: int) =
  var b = Box(x: 0)
  gpb = addr b
  let f = rdXAddr
  let r = f(addr b.x, k)
  if r == k and k == 3: symexTarget("pa")
  if r != k: symexTarget("pa_dead")

type Outer = object
  inner: Box
  n: int

var gpo: ptr Outer

proc rdOuter(p: ptr int, k: int): int =
  gpo[].inner.x = k
  p[]

proc sutDirectAddrNested(k: int) =
  var o = Outer(inner: Box(x: 0), n: 0)
  gpo = addr o
  let r = rdOuter(addr o.inner.x, k)
  if r == k and o.inner.x == k and k == 3: symexTarget("dn")
  if r != k or o.inner.x != k: symexTarget("dn_dead")

proc wrIAddr(p: ptr int, k: int) =
  gpi[] = 5
  p[] = k

proc sutDirectAddrWhole(k: int) =
  var x = 0
  gpi = addr x
  wrIAddr(addr x, k)
  if x == k and k == 3: symexTarget("dx")
  if x != k: symexTarget("dx_dead")

proc bumpAddr(p: ptr int, k: int) =
  p[] = k
  gpi[] = gpi[] + 1

proc sutDirectAddrElem(k: int) =
  if k < 0 or k > 1000: return
  var s = @[0, 0]
  gpi = addr s[0]
  bumpAddr(addr s[0], k)
  if s[0] == k + 1 and k == 3: symexTarget("de")
  if s[0] != k + 1: symexTarget("de_dead")

suite "S8bu (2): closure and proc-value calls into an address-taken variable":

  test "nim":
    let h = nativeHits(sutPvPath, ks) + nativeHits(sutLamPath, ks) +
            nativeHits(sutLamPathBranch, ks) + nativeHits(sutPvWhole, ks) +
            nativeHits(sutLamWholeRead, ks) + nativeHits(sutPvBig, ks)
    for l in ["pp", "lp", "lb", "lb2", "pw", "lw", "pg"]:
      checkpoint l
      check l in h
    for l in ["pp", "lp", "lb", "pw", "lw", "pg"]:
      checkpoint l & "_dead"
      check (l & "_dead") notin h

  test "a var actual by path":
    clean(sutPvPath, "pp", sxSat)
    clean(sutPvPath, "pp_dead", sxUnsat)
    clean(sutLamPath, "lp", sxSat)
    clean(sutLamPath, "lp_dead", sxUnsat)
    clean(sutLamPathBranch, "lb", sxSat)
    clean(sutLamPathBranch, "lb2", sxSat)
    clean(sutLamPathBranch, "lb_dead", sxUnsat)

  test "a var actual by name":
    clean(sutPvWhole, "pw", sxSat)
    clean(sutPvWhole, "pw_dead", sxUnsat)
    clean(sutLamWholeRead, "lw", sxSat)
    clean(sutLamWholeRead, "lw_dead", sxUnsat)

  test "a by-value argument passed by address":
    clean(sutPvBig, "pg", sxSat)
    clean(sutPvBig, "pg_dead", sxUnsat)

suite "S8bu (3): addr of a part of an address-taken variable":

  test "nim":
    let h = nativeHits(sutDirectAddrPart, ks) +
            nativeHits(sutDirectAddrPartWrite, ks) +
            nativeHits(sutPvAddrPart, ks) + nativeHits(sutDirectAddrNested, ks) +
            nativeHits(sutDirectAddrWhole, ks) + nativeHits(sutDirectAddrElem, ks)
    for l in ["da", "dw", "pa", "dn", "dx", "de"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a direct call":
    clean(sutDirectAddrPart, "da", sxSat)
    clean(sutDirectAddrPart, "da_dead", sxUnsat)
    clean(sutDirectAddrPartWrite, "dw", sxSat)
    clean(sutDirectAddrPartWrite, "dw_dead", sxUnsat)
    clean(sutDirectAddrNested, "dn", sxSat)
    clean(sutDirectAddrNested, "dn_dead", sxUnsat)
    clean(sutDirectAddrWhole, "dx", sxSat)
    clean(sutDirectAddrWhole, "dx_dead", sxUnsat)
    # An element of a seq with element cells: declined (reported in the
    # RFC): the call's cell shares the element's heap.
    # RFC-0005 S8ca: the actual is the element's cell (`sharesElemCell`).
    clean(sutDirectAddrElem, "de", sxSat)
    clean(sutDirectAddrElem, "de_dead", sxUnsat)

  test "a proc-value call":
    clean(sutPvAddrPart, "pa", sxSat)
    clean(sutPvAddrPart, "pa_dead", sxUnsat)

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
