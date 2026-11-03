## RFC-0005 (soundness channels) slice S8as -- S8an's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8as_remainder`, `tsymex_rfc0005_s8as_remainder_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 80 s).

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
  test "a pointer re-pointed under a branch is decided":
    ## RFC-0005 S8ax: `addr x` of a routine variable is its address cell,
    ## so a pointer re-pointed on one arm is exact (it declined here).
    verdict(sutAddrRepointBranch, "rb", sxSat)
    let r = symexFind(sutAddrRepointBranch, tLabel("rb"))
    if r.status == sxSat: check r.witness[0] <= 0

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
