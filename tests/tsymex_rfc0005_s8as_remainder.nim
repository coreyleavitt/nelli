## RFC-0005 (soundness channels) slice S8as -- S8an's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
import std/[unittest, strutils, math]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template verdictS(fn: typed, lbl: string, want: SymexStatusKind,
                  s: SymexSettings) =
  block:
    let r = symexFind(fn, tLabel(lbl), s)
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template notUnsat(fn: typed, lbl: string, kind: SymexErrorKind) =
  ## No longer a false `sxUnsat`: the walk models the write as a fresh value
  ## (`kind` recorded), so the target is a candidate. Replay decides it: the
  ## solver's witness need not be one that reaches it for real.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check r.errors.hasKind(kind)
    check not r.errors.hasKind(weInternalWalkerFault)

template clean(fn: typed, lbl: string, want: SymexStatusKind) =
  ## The verdict, with nothing recorded at all.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0

template declines(fn: typed, lbl: string, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (2) an opaque call writes a module-level variable ----------------------
#
# WRONG VERDICT before S8as: an inert opaque call (statement position, value
# arguments) was a no-op for the walk, on the argument that the walker did
# not model globals; S8an made it model them. `gOp` kept the value written
# before the call: `og` was a false `sxUnsat` with `errors` empty. Probed:
# `sutOpaqueGlobal(5)` reaches `og`.

var gOp: int

proc opSet(a: int) {.symexOpaque.} =
  gOp = a

proc opSetDeep(a: int) {.symexOpaque.} =
  opSet(a + 1)

proc sutOpaqueGlobal(v: int) =
  gOp = 0
  opSet(v)
  if gOp == 5: symexTarget("og")

proc sutOpaqueGlobalDeep(v: int) =
  gOp = 0
  opSetDeep(v)            # writes `gOp` through the routine it calls
  if gOp == 5: symexTarget("ogd")

proc opNoWrite(a: int) {.symexOpaque.} =
  discard a

proc sutOpaqueNoWrite(v: int) =
  gOp = 0
  opNoWrite(v)            # its summary is empty: `gOp` keeps 0
  if gOp == 0 and v == 1: symexTarget("onw")
  if gOp != 0: symexTarget("onw_dead")

proc sutNestedOpaque(v: int) =
  # WRONG VERDICT before S8as, the capture twin: `c` kept 0.
  var c = 0
  proc setc(a: int) {.symexOpaque.} =
    c = a
  setc(v)
  if c == 5: symexTarget("no")

# ---- (3) a module-level variable read before any write ----------------------

var gInit = 7
let gLet = 9
let gLetComputed = gInit * 2

proc sutGlobalEntry(x: int) =
  if gInit == 7 and x == 1: symexTarget("ge")
  let a = gInit
  if a != gInit: symexTarget("ge_dead")

proc sutLetLiteral(x: int) =
  if gLet == 9 and x == 1: symexTarget("ll")
  if gLet != 9: symexTarget("ll_dead")

proc sutLetComputed(x: int) =
  if gLetComputed == 14 and x == 1: symexTarget("lc")

proc readG(): int = gInit

proc sutCalleeEntry(x: int) =
  # A callee reads the entry value, the caller then writes: the callee's
  # second read sees the write.
  discard readG()
  gInit = 3
  if readG() == 3 and x == 2: symexTarget("ce")
  if readG() != 3: symexTarget("ce_dead")

proc sutClosureGlobal(v: int) =
  # A closure body reads the global the caller wrote (it declined).
  gOp = 0
  let f = proc (): int = gOp
  gOp = v                 # after the closure was built
  if f() == 3: symexTarget("cg")
  if f() != v: symexTarget("cg_dead")

# ---- (4) a closure's write to a capture or a global --------------------------

proc sutClosureCapWrite(v: int) =
  var c = 0
  let f = proc (a: int) =
    c = a
  f(v)
  if c == 5: symexTarget("cw")
  if c != v: symexTarget("cw_dead")

proc sutClosureGlobalWrite(v: int) =
  gOp = 0
  let h = proc (a: int) =
    gOp = a
  h(v)
  if gOp == 5: symexTarget("gw")
  if gOp != v: symexTarget("gw_dead")

proc sutClosureBranchWrite(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var c = 0
  let f = proc (a: int) =
    if a > 0: c = a
    else: c = -a
  f(v)
  if c == 3 and v < 0: symexTarget("cb")
  if c < 0: symexTarget("cb_dead")

proc sutClosureTwice(v: int) =
  # The body reads the global as it stands at each call.
  gOp = 0
  let f = proc (): int = gOp
  let a = f()
  gOp = v
  if f() == 5 and a == 0: symexTarget("ct")
  if f() == a and v != 0: symexTarget("ct_dead")

proc sutClosureIncTwice(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var n = v
  let inc1 = proc () =
    n += 1
  inc1()
  inc1()
  if n == 7: symexTarget("it")
  if n != v + 2: symexTarget("it_dead")

proc sutEvalOrder(v: int) =
  # Probed: `c + g()` is 15 under c and cpp -- the call runs first.
  var c = 1
  let g = proc (): int =
    c = 10
    5
  let r = c + g()
  if r == 15 and v == 1: symexTarget("eo")
  if r == 6: symexTarget("eo_dead")

proc sutShortCircuitWrite(v: int) =
  var c = 0
  let f = proc (): bool =
    c = 1
    true
  if v > 0 and f(): discard
  if c == 1 and v > 0: symexTarget("sw")
  if c == 1 and v <= 0: symexTarget("sw_dead")

proc sutShortCircuitRaise(x: int) =
  # WRONG VERDICT before S8as: the closure on the right of `and` was
  # evaluated unconditionally, so its raise on `x == 0` was reachable.
  let f = proc (): bool =
    if x == 0: raise newException(ValueError, "zero")
    true
  try:
    if x != 0 and f(): symexTarget("sr")
  except ValueError:
    symexTarget("sr_dead")

proc mkCounter(): proc () =
  var n = 0
  result = proc () =
    n += 1

proc sutOutOfFrame(v: int) =
  let c = mkCounter()
  c()
  if v == 1: symexTarget("of")

# ---- (1) recursion on a symbolic argument ------------------------------------

proc s8asFact(n: int): int =
  if n <= 1: 1 else: n * s8asFact(n - 1)

proc sutFact(n: int) =
  symexAssume(n >= 0 and n <= 5)
  if s8asFact(n) == 120: symexTarget("fa")
  if s8asFact(n) == 7: symexTarget("fa_dead")

proc s8asFib(k: int): int =
  if k < 2: k else: s8asFib(k - 1) + s8asFib(k - 2)

proc sutFib(n: int) =
  symexAssume(n >= 0 and n <= 4)
  if s8asFib(n) == 3: symexTarget("fb")

proc sutFibPair(n: int) =
  symexAssume(n >= 3 and n <= 4)
  if s8asFib(n) == 3: symexTarget("fp")

proc s8asSumTo(k: int): int =
  if k <= 0: 0 else: k + s8asSumTo(k - 1)

proc sutSumTo(n: int) =
  symexAssume(n >= 0 and n <= 5)
  if s8asSumTo(n) == 15: symexTarget("st")

proc s8asCount(k: int): int =
  var i = 0
  while i < k: inc i
  i

proc sutLoopCache(n: int) =
  symexAssume(n >= 0 and n <= 3)
  if n == 0:
    discard s8asCount(n)   # walked where `n == 0`: the loop never runs
  if s8asCount(n) == 2: symexTarget("lc2")

# ---- (7) the `int` heap is Int-sorted ----------------------------------------

proc s8asIncP(p: ptr int) = p[] += 1

proc sutHeapInt(v: int) =
  symexAssume(v > -1000 and v < 1000)
  let r = new int
  r[] = v
  r[] += 1
  if r[] == 5: symexTarget("hi")
  if r[] != v + 1: symexTarget("hi_dead")

proc sutAddrIncWide(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var x = v
  s8asIncP(addr x)
  s8asIncP(addr x)
  if x == 9: symexTarget("aw")
  if x != v + 2: symexTarget("aw_dead")

proc sutHeapOverflow(v: int) =
  ## An Int cell keeps its overflow obligation (`ziWidth = 64`).
  symexAssume(v > 9223372036854775797)
  let r = new int
  r[] = v
  r[] += 20

proc sutHeapBV(v, w: int) =
  ## `w` is a bit-vector (unranged), so the heap stays one.
  symexAssume(v > -1000 and v < 1000)
  let r = new int
  r[] = w
  if r[] != w: symexTarget("hb_dead")
  if r[] == v + 1: symexTarget("hb")

# ---- (6) two `addr` of different parts of one variable ----------------------

type
  S8asPair = object
    a, b: int
  S8asOuter = object
    inner: S8asPair
    c: int

proc twoPtr(p, q: ptr int; v: int) =
  p[] = v
  q[] = v + 1

proc pairAndPart(p: ptr S8asPair; q: ptr int; v: int) =
  p[].b = v
  q[] = v + 1

proc twoVar(x, y: var int; v: int) =
  x = v
  y = v + 1

proc sutAddrFields(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asPair()
  twoPtr(addr o.a, addr o.b, v)
  if o.a == 4 and o.b == 5: symexTarget("af")
  if o.b != o.a + 1: symexTarget("af_dead")

proc sutAddrElems(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var a: array[3, int]
  twoPtr(addr a[0], addr a[2], v)
  if a[0] == 4 and a[2] == 5 and a[1] == 0: symexTarget("ae")
  if a[1] != 0 or a[2] != a[0] + 1: symexTarget("ae_dead")

proc sutAddrNested(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asOuter()
  twoPtr(addr o.inner.a, addr o.c, v)
  if o.inner.a == 4 and o.c == 5: symexTarget("an")
  if o.inner.b != 0: symexTarget("an_dead")

proc sutVarFields(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asPair()
  twoVar(o.a, o.b, v)
  if o.a == 4 and o.b == 5: symexTarget("vf")
  if o.b != o.a + 1: symexTarget("vf_dead")

proc sutAddrOverlap(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var o = S8asOuter()
  pairAndPart(addr o.inner, addr o.inner.a, v)   # a whole and its part
  if o.inner.b == 4: symexTarget("ao")

# ---- (5) more `addr` forms ---------------------------------------------------

proc sutAddrIndexAlias(v: int) =
  var a: array[3, int]
  var p = addr a[1]
  p[] = v
  if a[1] == 4 and a[0] == 0: symexTarget("ai")
  if a[1] != v: symexTarget("ai_dead")

proc sutAddrRepoint(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var x, y: int
  var p = addr x
  p[] = v
  p = addr y
  p[] = v + 1
  if x == 4 and y == 5: symexTarget("rp")
  if y != x + 1: symexTarget("rp_dead")

proc sutAddrTwoDecls(v: int) =
  var x, y: int
  let p = addr x
  let q = addr y
  let
    r = addr x
    s = addr y
  p[] = v
  s[] = 2
  if r[] == 4 and q[] == 2: symexTarget("md")
  if x != v: symexTarget("md_dead")

proc sutAddrRepointBranch(v: int) =
  var x, y: int
  var p = addr x
  if v > 0: p = addr y      # re-pointed on one arm only
  p[] = 1
  if x == 1: symexTarget("rb")

suite "RFC-0005 S8as: walker version":
  test "symexWalkerVersion is at least 192":
    check parseInt(symexWalkerVersion) >= 192

suite "RFC-0005 S8as (2): an opaque call's writes":
  test "an opaque routine's write to a global reaches the caller":
    notUnsat(sutOpaqueGlobal, "og", feGlobalHavoc)
  test "through a routine it calls":
    notUnsat(sutOpaqueGlobalDeep, "ogd", feGlobalHavoc)
  test "a routine that writes nothing leaves the global as it was, clean":
    clean(sutOpaqueNoWrite, "onw", sxSat)
    clean(sutOpaqueNoWrite, "onw_dead", sxUnsat)
  test "a nested opaque routine's write to its capture reaches it":
    notUnsat(sutNestedOpaque, "no", feGlobalHavoc)

suite "RFC-0005 S8as (3): a global's entry value":
  test "a var global read before any write holds its entry value":
    verdict(sutGlobalEntry, "ge", sxSat)
    verdict(sutGlobalEntry, "ge_dead", sxUnsat)
  test "a let global initialised by a literal reads the literal, clean":
    clean(sutLetLiteral, "ll", sxSat)
    clean(sutLetLiteral, "ll_dead", sxUnsat)
  test "a let global with a computed initialiser holds a fresh value":
    verdict(sutLetComputed, "lc", sxSat)
  test "a callee reads the entry value and then the caller's write":
    verdict(sutCalleeEntry, "ce", sxSat)
    verdict(sutCalleeEntry, "ce_dead", sxUnsat)
  test "a closure body reads the global as the caller holds it":
    verdict(sutClosureGlobal, "cg", sxSat)
    verdict(sutClosureGlobal, "cg_dead", sxUnsat)

suite "RFC-0005 S8as (4): a closure's writes reach the caller":
  test "a capture written in the frame that built the closure":
    verdict(sutClosureCapWrite, "cw", sxSat)
    verdict(sutClosureCapWrite, "cw_dead", sxUnsat)
  test "a global written by a closure body":
    verdict(sutClosureGlobalWrite, "gw", sxSat)
    verdict(sutClosureGlobalWrite, "gw_dead", sxUnsat)
  test "a write on each of two arms":
    verdict(sutClosureBranchWrite, "cb", sxSat)
    verdict(sutClosureBranchWrite, "cb_dead", sxUnsat)
  test "a global read by the body at each of two calls":
    verdict(sutClosureTwice, "ct", sxSat)
    verdict(sutClosureTwice, "ct_dead", sxUnsat)
  test "two calls each read the other's write":
    verdict(sutClosureIncTwice, "it", sxSat)
    verdict(sutClosureIncTwice, "it_dead", sxUnsat)
  test "the call in an operand runs before the operands are read":
    verdict(sutEvalOrder, "eo", sxSat)
    verdict(sutEvalOrder, "eo_dead", sxUnsat)
  test "a closure on the right of `and` runs only under its guard":
    verdict(sutShortCircuitWrite, "sw", sxSat)
    verdict(sutShortCircuitWrite, "sw_dead", sxUnsat)
    verdict(sutShortCircuitRaise, "sr", sxSat)
    verdict(sutShortCircuitRaise, "sr_dead", sxUnsat)
  test "a capture written by a closure applied outside its frame is kept":
    # RFC-0005 S8ax: the capture lives in an env cell the walk threads to
    # every frame (was the scoped `ceCaptureByRefUnmodelled` decline).
    let r = symexFind(sutOutOfFrame, tLabel("of"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(ceCaptureByRefUnmodelled)

suite "RFC-0005 S8as (6): the alias check is by path":
  test "two fields of one object are two cells":
    verdict(sutAddrFields, "af", sxSat)
    verdict(sutAddrFields, "af_dead", sxUnsat)
  test "two constant indices of one array are two cells":
    verdict(sutAddrElems, "ae", sxSat)
    verdict(sutAddrElems, "ae_dead", sxUnsat)
  test "nested field paths that part":
    verdict(sutAddrNested, "an", sxSat)
    verdict(sutAddrNested, "an_dead", sxUnsat)
  test "two `var` fields of one object":
    verdict(sutVarFields, "vf", sxSat)
    verdict(sutVarFields, "vf_dead", sxUnsat)
  test "a whole and its part still decline":
    declines(sutAddrOverlap, "ao", feUnsupportedOp, "aliases another argument")

suite "RFC-0005 S8as (5): more `addr` forms are modelled":
  test "the address of a constant array element":
    verdict(sutAddrIndexAlias, "ai", sxSat)
    verdict(sutAddrIndexAlias, "ai_dead", sxUnsat)
  test "a pointer re-pointed by a statement of its own list":
    verdict(sutAddrRepoint, "rp", sxSat)
    verdict(sutAddrRepoint, "rp_dead", sxUnsat)
  test "several pointers declared in one section":
    verdict(sutAddrTwoDecls, "md", sxSat)
    verdict(sutAddrTwoDecls, "md_dead", sxUnsat)
  test "a pointer re-pointed under a branch still declines":
    declines(sutAddrRepointBranch, "rb", heUnsafeCast, "addr")

suite "RFC-0005 S8as (1): recursion on a symbolic argument":
  test "the walk drops an infeasible `if` arm inside a recursion":
    ## RED: `fib(n)` under `n in 0..4` did not end in 15 minutes at
    ## `maxCallDepth = 6` (every arm of every level was walked).
    symexIfArmsPruned = 0
    verdictS(sutFib, "fb", sxSat,
             SymexSettings(budget: ResourceBudget(maxCallDepth: 5)))
    check symexIfArmsPruned > 0
    verdictS(sutFact, "fa", sxSat,
             SymexSettings(budget: ResourceBudget(maxCallDepth: 6)))
    verdictS(sutFact, "fa_dead", sxUnsat,
             SymexSettings(budget: ResourceBudget(maxCallDepth: 6)))
  test "a summary walked under a pruned context is not cached":
    ## A false `sxUnsat` the pruning first exposed: `fib(n - 2)` walked
    ## inside `fib(n - 1)`'s frame (`n - 2 < 2` dropped there) was cached
    ## and replayed at the outer call. The S8k loop pruning had the same
    ## hole: `s8asCount(n)` walked where `n == 0` cached the one path that
    ## skips the loop.
    verdictS(sutFibPair, "fp", sxSat,
             SymexSettings(budget: ResourceBudget(maxCallDepth: 5)))
    verdict(sutLoopCache, "lc2", sxSat)
  test "past the call-depth budget it declines with the reason":
    ## `sumTo(5)` needs six frames; the default budget is three, so the
    ## deep paths declined and said which budget to raise. RFC-0005 S8ax:
    ## the frontier does not grow with depth, so the walk now extends past
    ## `maxCallDepth` and reaches the label (the decline past the hard
    ## budget is pinned in `tsymex_rfc0005_s8ax_remainder`).
    verdict(sutSumTo, "st", sxSat)
    verdictS(sutSumTo, "st", sxSat,
             SymexSettings(budget: ResourceBudget(maxCallDepth: 7)))

suite "RFC-0005 S8as (7): the `int` heap is Int-sorted":
  test "wide-range arithmetic on an int cell decides at once":
    ## Before: `hi_dead` 55 s and `aw_dead` 26 s (Linux, Z3 5.1); the
    ## `int2bv`/`bv2int` round trip through a BV-sorted heap.
    verdict(sutHeapInt, "hi", sxSat)
    verdict(sutHeapInt, "hi_dead", sxUnsat)
    verdict(sutAddrIncWide, "aw", sxSat)
    verdict(sutAddrIncWide, "aw_dead", sxUnsat)
  test "an Int cell still raises on overflow":
    let r = symexFind(sutHeapOverflow, tRaisedExn("OverflowDefect"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "a bit-vector parameter keeps the bit-vector heap":
    verdict(sutHeapBV, "hb", sxSat)
    verdict(sutHeapBV, "hb_dead", sxUnsat)
