## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 1 of 7 of this suite, with
## `tsymex_rfc0005_s8ax_remainder_b`, `tsymex_rfc0005_s8ax_remainder_c`,
## `tsymex_rfc0005_s8ax_remainder_d`, `tsymex_rfc0005_s8ax_remainder_e`,
## `tsymex_rfc0005_s8ax_remainder_f`, `tsymex_rfc0005_s8ax_remainder_g`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 132 s).

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

proc sutFibFree(x: int) =
  # `x` free: `fib` fans out, so the depth is not extended.
  if s8axFib(x) == 13: symexTarget("ff")

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
  test "a recursion that fans out is not extended":
    ## RED (on 7190da2): `tsymex_phase3_recursion`'s `fib(x) == 13` was
    ## killed at 900 s: the depth-first frontier test admitted `fib`'s
    ## leftmost chain to the hard budget. Now 12 walks.
    let r = symexFind(sutFibFree, tLabel("ff"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(beBudgetExhaustedUnmodelled)
    let st = r.callStats.filterIt(it.name == "s8axFib")
    check st.len == 1
    check st[0].walked <= 20
  test "maxRecursionDepth = 0 turns the extension off":
    ## `sutDownBounded`, not `sutSumToAx`: a declined `sumTo` frame leaves
    ## `k + <fresh>` whose overflow query runs for minutes (on the base
    ## too, 468 s), which the test is not about.
    let r = symexFind(sutDownBounded, tLabel("db"),
      SymexSettings(budget: ResourceBudget(maxRecursionDepth: 0)))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(beBudgetExhaustedUnmodelled)
  test "maxRecursionDepth enters the cache key only when not the default":
    check ";mrd=" notin canonicalize(SymexSettings())
    check ";mrd=7" in canonicalize(
      SymexSettings(budget: ResourceBudget(maxRecursionDepth: 7)))

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

type S8axRR = ref object
  a: int

type S8axPair = object
  a, b: int
