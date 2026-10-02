## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
import std/[unittest, strutils, sequtils]
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

proc depth(d: int): SymexSettings =
  SymexSettings(budget: ResourceBudget(maxCallDepth: d))

# ---- (1) the call cache is keyed by the arguments and the facts -------------
#
# WRONG VERDICT before S8ax: the cache key was `argShapeKey`, an XOR of
# 32-bit Z3 AST hashes, and a hit replayed the first call's return with no
# check that the arguments were the same. The 64-bit literals 8472 and 45048
# hash alike, so `s8axId(45048)` replayed `s8axId(8472)`'s `result == 8472`:
# `hc` was a false `sxUnsat` and `hc_dead` a false `sxSat`, both with
# `errors` empty. Probed: `sutHashCollide(1)` reaches `hc`.

proc s8axId(k: int): int = k

proc sutHashCollide(v: int) =
  let a = s8axId(8472)
  let b = s8axId(45048)
  if b == 45048 and v == 1: symexTarget("hc")
  if b == 8472: symexTarget("hc_dead")
  discard a

proc s8axFib(k: int): int =
  if k < 2: k else: s8axFib(k - 1) + s8axFib(k - 2)

proc sutFib(n: int) =
  symexAssume(n >= 0 and n <= 4)
  if s8axFib(n) == 3: symexTarget("fb")
  if s8axFib(n) == 4: symexTarget("fb_dead")

# ---- (2) `if` arms outside a recursion ---------------------------------------
#
# A dead arm that guards a loop: the walk used to unroll the loop under a
# context no execution reaches. Probed: `sutDeadArm(3)` reaches `da`.

proc sutDeadArm(n: int) =
  symexAssume(n >= 0 and n <= 3)
  var acc = 0
  if n > 10:
    var i = 0
    while i < n:
      acc += i
      inc i
  if acc == 0 and n == 3: symexTarget("da")
  if acc != 0: symexTarget("da_dead")

# ---- (3) the call depth adapts to the frontier --------------------------------
#
# `sumTo(n)` with `n` in `0..5` needs six frames, past the default
# `maxCallDepth = 3`: it declined. One feasible path per level, so the walk
# now extends. An unbounded `n` extends to the hard budget; the first
# extended level then drops what it walked and declines, naming both
# budgets. Probed: `sutSumToAx(5)` reaches `st` (15), `sutDownBounded(20)`
# reaches `db`, `sutDownMixed(5)` reaches `dm`.

proc s8axSumTo(k: int): int =
  if k <= 0: 0 else: k + s8axSumTo(k - 1)

proc sutSumToAx(n: int) =
  symexAssume(n >= 0 and n <= 5)
  if s8axSumTo(n) == 15: symexTarget("st")
  if s8axSumTo(n) == 16: symexTarget("st_dead")

proc s8axDown(k: int): bool =
  if k <= 0: true else: s8axDown(k - 1)

proc sutDownBounded(n: int) =
  symexAssume(n >= 0 and n <= 20)
  if s8axDown(n) and n == 20: symexTarget("db")

proc sutDownDeep(n: int) =
  symexAssume(n >= 0)
  if s8axDown(n) and n == 30: symexTarget("dd")

proc sutDownMixed(n: int) =
  symexAssume(n >= 0)
  if s8axDown(n) and n == 5: symexTarget("dm")

suite "RFC-0005 S8ax: walker version":
  test "symexWalkerVersion is at least 197":
    check parseInt(symexWalkerVersion) >= 197

suite "RFC-0005 S8ax (1): the call cache":
  test "two calls whose argument hashes collide are two calls":
    ## RED before S8ax: `hc` sxUnsat and `hc_dead` sxSat, `errors` empty.
    clean(sutHashCollide, "hc", sxSat)
    clean(sutHashCollide, "hc_dead", sxUnsat)
  test "a recursion's summaries are reused under their pruned facts":
    ## S8as left a summary walked under a pruned context uncached, so
    ## `fib` was walked at every call: `fb_dead` 25.3 s, 49 walks, no hit
    ## (Linux, Z3 5.1, `maxCallDepth = 5`); 8.2 s, 27 walks, 20 hits after.
    let r = symexFind(sutFib, tLabel("fb_dead"), depth(5))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let st = r.callStats.filterIt(it.name == "s8axFib")
    check st.len == 1
    check st[0].cacheHits > 0
    verdictS(sutFib, "fb", sxSat, depth(5))

suite "RFC-0005 S8ax (2): `if` arms outside a recursion":
  test "a dead arm outside a recursion is dropped before it is walked":
    symexIfArmsPruned = 0
    clean(sutDeadArm, "da", sxSat)
    check symexIfArmsPruned > 0
    clean(sutDeadArm, "da_dead", sxUnsat)

suite "RFC-0005 S8ax (3): the call depth adapts to the frontier":
  test "a recursion its arguments bound is followed past maxCallDepth":
    ## RED before S8ax: `st` declined at `maxCallDepth=3`.
    clean(sutSumToAx, "st", sxSat)
    clean(sutSumToAx, "st_dead", sxUnsat)
  test "twenty-one frames, one feasible path per level":
    clean(sutDownBounded, "db", sxSat)
  test "past the hard budget it still declines, and names both budgets":
    ## `s8axDown(30)` needs 31 frames, past the default hard budget.
    let r = symexFind(sutDownDeep, tLabel("dd"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(beBudgetExhaustedUnmodelled)
    check "maxCallDepth=3" in show(r.errors)
    check "maxRecursionDepth=24" in show(r.errors)
  test "an unbounded recursion declines at maxCallDepth, as before":
    ## The extension's root drops all it walked once any path reached the
    ## hard budget, so the later queries cost what they did before S8ax;
    ## `n == 5` returned within it and is declined with the rest.
    let r = symexFind(sutDownMixed, tLabel("dm"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(beBudgetExhaustedUnmodelled)
  test "maxRecursionDepth = 0 turns the extension off":
    let r = symexFind(sutSumToAx, tLabel("st"),
      SymexSettings(budget: ResourceBudget(maxRecursionDepth: 0)))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(beBudgetExhaustedUnmodelled)
  test "maxRecursionDepth enters the cache key only when not the default":
    check ";mrd=" notin canonicalize(SymexSettings())
    check ";mrd=7" in canonicalize(
      SymexSettings(budget: ResourceBudget(maxRecursionDepth: 7)))

# ---- (5) an opaque routine's raises, heap writes and other writes ------------
#
# WRONG VERDICTS before S8ax, each with `errors` empty: an inert opaque call
# never raised and always returned. `try: s8axBoom(v) except ValueError`
# was a false `sxUnsat`, a target after `s8axAlwaysRaise(v)` a false `sxSat`,
# a target after `s8axSpin(v)` (it never returns for `v == 2`) a false
# `sxSat`, and `tRaisedExn("ValueError")` through `s8axAlwaysRaise` a false
# `sxUnsat`. A nested opaque routine's write through a captured `let` ref
# was dropped (S8as skipped a capture that is not writable): a false
# `sxUnsat`. A `Defect` the body raises, caught around the call: a false
# `sxUnsat`.

type
  S8axNode = ref object
    val: int
  S8axErr = object of ValueError

var gS8axNode: S8axNode
var gS8axCast: int

proc s8axBoom(a: int) {.symexOpaque.} =
  if a == 3: raise newException(ValueError, "boom")

proc s8axAlwaysRaise(a: int) {.symexOpaque.} =
  raise newException(ValueError, "always")

proc s8axSpin(a: int) {.symexOpaque.} =
  var i = 0
  while a == 2: inc i

proc s8axDiv(a: int) {.symexOpaque.} =
  discard 10 div a

proc s8axRaisesBase(a: int) {.symexOpaque, raises: [ValueError].} =
  if a == 4: raise newException(S8axErr, "sub")

proc s8axBump(n: S8axNode) {.symexOpaque.} =
  n.val = 7

proc s8axSetVar(x: var int) {.symexOpaque.} =
  x = 9

proc s8axSetGlobalNode() {.symexOpaque.} =
  gS8axNode = S8axNode(val: 3)

proc s8axCastWrite(a: int) {.symexOpaque.} =
  gS8axCast = cast[int](a)

proc sutOpaqueRaise(v: int) =
  try:
    s8axBoom(v)
  except ValueError:
    if v == 3: symexTarget("or")

proc sutOpaqueAlways(v: int) =
  s8axAlwaysRaise(v)
  if v == 1: symexTarget("oa")

proc sutOpaqueSpin(v: int) =
  s8axSpin(v)
  if v == 2: symexTarget("os")

proc sutOpaqueRaiseBoundary(v: int) =
  s8axAlwaysRaise(v)

proc sutOpaqueDefect(v: int) =
  try:
    s8axDiv(v)
  except DivByZeroDefect:
    symexTarget("od")

proc sutOpaqueSubtype(v: int) =
  try:
    s8axRaisesBase(v)
  except S8axErr:
    symexTarget("osub")

proc sutOpaqueHeap(v: int) =
  let n = S8axNode(val: 1)
  s8axBump(n)
  if n.val == 7 and v == 1: symexTarget("oh")
  if n == nil: symexTarget("oh_dead")

proc sutOpaqueVar(v: int) =
  var x = 0
  var y = 3
  s8axSetVar(x)
  if x == 9 and v == 1: symexTarget("ov")
  if y != 3: symexTarget("ov_dead")

proc sutOpaqueGlobalRef(v: int) =
  gS8axNode = S8axNode(val: 0)
  s8axSetGlobalNode()
  if gS8axNode.val == 3 and v == 1: symexTarget("ogn")

proc sutOpaqueLetCapture(v: int) =
  let c = S8axNode(val: 1)
  proc w8ax() {.symexOpaque.} =
    c.val = 5
  w8ax()
  if c.val == 5 and v == 1: symexTarget("olc")

proc sutOpaqueCast(v: int) =
  gS8axCast = 0
  s8axCastWrite(v)
  if gS8axCast == 5 and v == 5: symexTarget("oc")

suite "RFC-0005 S8ax (5): an opaque routine's effects":
  test "a raise its `raises` list names is forked":
    ## RED before S8ax: sxUnsat, `errors` empty.
    verdict(sutOpaqueRaise, "or", sxSat)
  test "a target past a call that always raises is not reached":
    ## RED before S8ax: sxSat, `errors` empty. The returning path is a
    ## replayed candidate now, and the replay raises.
    let r = symexFind(sutOpaqueAlways, tLabel("oa"))
    checkpoint show(r.errors)
    check r.status != sxSat
    check r.errors.hasKind(feOpaqueEffectHavoc)
  test "a raise reaches the boundary":
    ## RED before S8ax: sxUnsat, `errors` empty.
    let r = symexFind(sutOpaqueRaiseBoundary, tRaisedExn("ValueError"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "a routine that may not return declines":
    ## RED before S8ax: sxSat, `errors` empty (and a replay of it would not
    ## end).
    declines(sutOpaqueSpin, "os", feOpaqueCallUnmodelled, "`while` loop")
  test "a Defect caught around the call declines":
    ## RED before S8ax: sxUnsat, `errors` empty.
    declines(sutOpaqueDefect, "od", feOpaqueCallUnmodelled, "Defect")
  test "an arm naming a subtype of a raised type declines":
    ## RED before S8ax: sxUnsat, `errors` empty.
    let r = symexFind(sutOpaqueSubtype, tLabel("osub"))
    checkpoint show(r.errors)
    check r.status != sxUnsat
    check r.errors.hasKind(feOpaqueCallUnmodelled)
  test "a write through a ref argument reaches its cell":
    ## S8as declined the call (a ref argument).
    verdict(sutOpaqueHeap, "oh", sxSat)
    verdict(sutOpaqueHeap, "oh_dead", sxUnsat)
  test "a write through a var argument reaches the variable alone":
    verdict(sutOpaqueVar, "ov", sxSat)
    verdict(sutOpaqueVar, "ov_dead", sxUnsat)
  test "a global that reaches heap cells is rebound":
    ## S8as declined the call (a ref global).
    verdict(sutOpaqueGlobalRef, "ogn", sxSat)
  test "a write through a captured `let` ref reaches its cell":
    ## RED before S8ax: sxUnsat, `errors` empty.
    verdict(sutOpaqueLetCapture, "olc", sxSat)
  test "a cast havocs every global and heap instead of declining":
    verdict(sutOpaqueCast, "oc", sxSat)

# ---- (4) every signed int heap cell is Int-sorted -----------------------------
#
# S8as made the plain `int` heap Int-sorted only when every `int` parameter
# was an Int; a ranged or narrower cell stayed a bit-vector. A cell of one
# sort holding a value of the other went through `int2bv`/`bv2int` and back,
# which Z3 decides only slowly. Measured (Linux, Z3 5.1), before -> after:
# `mx_dead` 50.6 s -> 0.03 s, `rg_dead` 71.1 s -> 0.03 s, `nw_dead`
# 18.0 s -> 0.02 s; `mw_dead` and the S8an `ab_dead` shape stay under 0.02 s.
# Each cell's sort is its type's; a bit-vector stored and read back meets
# its source unconverted (`intOfBV`, and a read at the address the heap's
# last store wrote is that store's value). The rlimit below is far under
# what the slow forms needed.

type S8axBox = object
  s: range[-5000..5000]

proc sutIntMixed(v, w: int) =
  symexAssume(v > -1000 and v < 1000)
  let r = new int
  r[] = v
  r[] += 1
  if r[] == 5 and w == 3: symexTarget("mx")
  if r[] != v + 1: symexTarget("mx_dead")

proc sutIntMixedW(v, w: int) =
  symexAssume(v > -1000 and v < 1000)
  let q = new int
  q[] = w
  if q[] != w: symexTarget("mw_dead")
  if q[] == v + 1: symexTarget("mw")

proc sutIntRanged(v: int) =
  symexAssume(v > -1000 and v < 1000)
  let b = new S8axBox
  b.s = v
  b.s = b.s + 1
  if b.s == 5: symexTarget("rg")
  if b.s != v + 1: symexTarget("rg_dead")

proc sutIntNarrow(v: int32) =
  symexAssume(v > -1000 and v < 1000)
  let r = new int32
  r[] = v
  r[] += 1
  if r[] == 5: symexTarget("nw")
  if r[] != v + 1: symexTarget("nw_dead")

proc s8axGetQ(p: ptr int): int = p[]

proc sutIntAddrBV(v: int) =
  var x = v
  if s8axGetQ(addr x) == 7: symexTarget("ab")
  if s8axGetQ(addr x) != v: symexTarget("ab_dead")

proc sutIntNarrowWiden(v: int32) =
  let r = new int32
  r[] = v
  if int(r[]) > 5 and int64(r[]) < 9: symexTarget("nwd")

const s8axTight = SymexSettings(budget: ResourceBudget(queryRLimit: 5_000_000))

suite "RFC-0005 S8ax (4): Int-sorted int heap cells":
  test "a cell of a mixed Int and bit-vector run":
    verdictS(sutIntMixed, "mx", sxSat, s8axTight)
    verdictS(sutIntMixed, "mx_dead", sxUnsat, s8axTight)
    verdictS(sutIntMixedW, "mw", sxSat, s8axTight)
    verdictS(sutIntMixedW, "mw_dead", sxUnsat, s8axTight)
  test "a ranged cell":
    verdictS(sutIntRanged, "rg", sxSat, s8axTight)
    verdictS(sutIntRanged, "rg_dead", sxUnsat, s8axTight)
  test "a cell narrower than 64 bits":
    verdictS(sutIntNarrow, "nw", sxSat, s8axTight)
    verdictS(sutIntNarrow, "nw_dead", sxUnsat, s8axTight)
  test "a narrow cell widened":
    verdict(sutIntNarrowWiden, "nwd", sxSat)
  test "a bit-vector stored through `addr` and read back":
    verdictS(sutIntAddrBV, "ab", sxSat, s8axTight)
    verdictS(sutIntAddrBV, "ab_dead", sxUnsat, s8axTight)

# ---- (7) a read and a later call that writes what it reads ------------------
#
# WRONG VERDICTS before S8ax (each `bad` was sxSat, nothing recorded): the
# parser hoisted each operand's statements where it stood, so an operand
# Nim reads inline was read BEFORE a later operand's call that writes it,
# and a constructor element Nim stores before the call was read after it.
# Nim (c and cpp, probed): a variable, a field, a ref field, a dereference
# or an element is read with its enclosing operation, after the later
# operands' calls; a call, a checked `+ - *` and every constructor element
# are evaluated where they stand. `-x` and `x div y` check where they stand
# and read late; an element read checks its bound where it stands.

proc s8axK(a, b: int): int = a * 100 + b

type S8axRR = ref object
  a: int

var gS8axOrd: int
proc s8axSetOrd(): int =
  gS8axOrd = 10
  0

proc sutOrdArray(v: int) =
  var x = v
  proc g(): int =
    x = 10
    0
  let a = [x, g()]
  if a[0] == 1 and v == 1: symexTarget("ok")
  if a[0] == 10 and v == 1: symexTarget("bad")

proc sutOrdSeq(v: int) =
  var x = v
  proc g(): int =
    x = 10
    0
  let a = @[x, g()]
  if a[0] == 1 and v == 1: symexTarget("ok")
  if a[0] == 10 and v == 1: symexTarget("bad")

proc sutOrdTuple(v: int) =
  var x = v
  proc g(): int =
    x = 10
    0
  let a = (x, g())
  if a[0] == 1 and v == 1: symexTarget("ok")
  if a[0] == 10 and v == 1: symexTarget("bad")

proc sutOrdField(v: int) =
  var x = (a: v, b: 2)
  proc g(): int =
    x.a = 10
    0
  let r = x.a + g()
  if r == 10 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

proc sutOrdRefField(v: int) =
  var rr = S8axRR(a: v)
  proc g(): int =
    rr.a = 10
    0
  let r = rr.a + g()
  if r == 10 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

proc sutOrdGlobal(v: int) =
  gS8axOrd = v
  let r = (gS8axOrd and 15) + s8axSetOrd()
  if r == 10 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

proc sutOrdArg(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  proc g(): int =
    x = 10
    0
  let r = s8axK(x + 0, g())
  if r == 100 and v == 1: symexTarget("ok")
  if r == 1000 and v == 1: symexTarget("bad")

proc sutOrdNeg(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  proc g(): int =
    x = 10
    0
  let r = -x + g()
  if r == -10 and v == 1: symexTarget("ok")
  if r == -1 and v == 1: symexTarget("bad")

proc sutOrdNegKept(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  var y = 0
  proc g(): int =
    y = x
    0
  let r = -x + g()
  if r == -1 and v == 1: symexTarget("ok")
  if r != -v: symexTarget("bad")

proc sutOrdDiv(v: int) =
  var x = v
  proc g(): int =
    x = 40
    0
  let r = x div 2 + g()
  if r == 20 and v == 4: symexTarget("ok")
  if r == 2 and v == 4: symexTarget("bad")

proc sutOrdIndex(v: int) =
  var s = @[1, v, 3]
  proc g(): int =
    s[1] = 20
    0
  let r = s[1] + g()
  if r == 20 and v == 1: symexTarget("ok")
  if r == 1 and v == 1: symexTarget("bad")

suite "RFC-0005 S8ax (7): evaluation order":
  test "a constructor's element is read before a later element's call":
    clean(sutOrdArray, "ok", sxSat)
    clean(sutOrdArray, "bad", sxUnsat)
    clean(sutOrdSeq, "ok", sxSat)
    clean(sutOrdSeq, "bad", sxUnsat)
    clean(sutOrdTuple, "ok", sxSat)
    clean(sutOrdTuple, "bad", sxUnsat)
  test "a field, a ref field and a global are read after the call":
    clean(sutOrdField, "ok", sxSat)
    clean(sutOrdField, "bad", sxUnsat)
    clean(sutOrdRefField, "ok", sxSat)
    clean(sutOrdRefField, "bad", sxUnsat)
    clean(sutOrdGlobal, "ok", sxSat)
    clean(sutOrdGlobal, "bad", sxUnsat)
  test "a checked `+` argument is evaluated before a later argument":
    verdict(sutOrdArg, "ok", sxSat)
    verdict(sutOrdArg, "bad", sxUnsat)
  test "a checked read whose value a later call changes declines":
    declines(sutOrdNeg, "ok", feEvalOrderUnmodelled, "reads after a later")
    declines(sutOrdDiv, "ok", feEvalOrderUnmodelled, "reads after a later")
    declines(sutOrdIndex, "ok", feEvalOrderUnmodelled, "reads after a later")
  test "a checked read the call leaves alone is exact":
    clean(sutOrdNegKept, "ok", sxSat)
    clean(sutOrdNegKept, "bad", sxUnsat)

# ---- (6) a closure applied away from the frame that built it ----------------
#
# DECLINED before S8ax (`ceCaptureByRefUnmodelled`, every case below): a
# closure's by-reference captures were read as they stood at construction
# and its writes were dropped wherever it ran outside its own frame. Nim
# keeps them in a heap env the frame and the closure share; the walk keeps
# each in an env cell threaded through every call as a global is.
# Expected values probed on c and cpp.

proc s8axCounter(start: int): proc(): int =
  var c = start
  result = proc(): int =
    c += 1
    c

proc s8axApply(f: proc(): int): int = f()

proc s8axApplyRaise(f: proc(): int): int =
  discard f()
  raise newException(ValueError, "boom")

proc s8axApplyIf(f: proc(): int; c: bool): int =
  if c: f() else: 0

proc s8axReadVar(a: var int; f: proc(): int): int =
  discard f()
  a

proc sutCloEscaped(v: int) =
  symexAssume(v > -100 and v < 100)
  let f = s8axCounter(v)
  discard f()
  let b = f()
  if b == v + 2: symexTarget("ok")
  if b != v + 2: symexTarget("bad")

proc sutCloTwoEnvs(v: int) =
  symexAssume(v > -100 and v < 100)
  let f = s8axCounter(v)
  let h = s8axCounter(v)
  discard f()
  let b = h()
  if b == v + 1: symexTarget("ok")
  if b != v + 1: symexTarget("bad")

proc sutCloPassed(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  x = 50
  let r = s8axApply(f)
  if r == 51 and x == 51: symexTarget("ok")
  if r != 51 or x != 51: symexTarget("bad")

proc sutCloMixed(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  discard f()
  discard s8axApply(f)
  discard f()
  let r = s8axApply(f) + x
  if r == 2 * v + 8: symexTarget("ok")
  if r != 2 * v + 8: symexTarget("bad")

proc sutCloRaise(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  try:
    discard s8axApplyRaise(f)
  except ValueError:
    if x == v + 1: symexTarget("ok")
    if x != v + 1: symexTarget("bad")

proc sutCloBranch(v: int) =
  symexAssume(v > -100 and v < 100)
  let f = s8axCounter(v)
  discard s8axApplyIf(f, v > 0)
  let b = f()
  if v > 0 and b == v + 2: symexTarget("ok")
  if (v > 0 and b != v + 2) or (v <= 0 and b != v + 1): symexTarget("bad")

proc sutCloLoop(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  var i = 0
  while i < 3:
    discard s8axApply(f)
    inc i
  if x == v + 3: symexTarget("ok")
  if x != v + 3: symexTarget("bad")

proc sutCloByAddr(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  let r = s8axReadVar(x, f)
  if r == v + 1: symexTarget("ok")

suite "RFC-0005 S8ax (6): a closure applied away from its frame":
  test "a closure returned from its frame keeps its env":
    clean(sutCloEscaped, "ok", sxSat)
    clean(sutCloEscaped, "bad", sxUnsat)
    clean(sutCloTwoEnvs, "ok", sxSat)
    clean(sutCloTwoEnvs, "bad", sxUnsat)
  test "a closure a callee applies writes the frame's variable":
    clean(sutCloPassed, "ok", sxSat)
    clean(sutCloPassed, "bad", sxUnsat)
    clean(sutCloMixed, "ok", sxSat)
    clean(sutCloMixed, "bad", sxUnsat)
    clean(sutCloLoop, "ok", sxSat)
    clean(sutCloLoop, "bad", sxUnsat)
  test "the write survives a raise and a branch":
    clean(sutCloRaise, "ok", sxSat)
    clean(sutCloRaise, "bad", sxUnsat)
    clean(sutCloBranch, "ok", sxSat)
    clean(sutCloBranch, "bad", sxUnsat)
  test "a capture passed by address while the closure runs declines":
    declines(sutCloByAddr, "ok", ceCaptureByRefUnmodelled, "passed by address")
