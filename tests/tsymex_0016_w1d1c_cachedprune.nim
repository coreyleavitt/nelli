## RFC-0016 W1-d1c -- a call summary that relied on a pruned undefined side
## (W1-d1a/b's `logPrune` from `drainArithTraps`) is replayed only where the
## prune holds (`pruneFactsSince` records it, `pruneFactsHold` re-checks it).
## A callee holding the division is called twice; the first call's context
## rules the undefined side out, the second admits it.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc udivCallee(a, b: uint64): uint64 = a div b

proc modCallee(a, b: int): int = a mod b

proc sutUDivTwice(k: uint64) =
  ## Only the `k == 0` path (the fall-through of the guard) admits zero.
  ## `r == 11` is unreachable on any defined path.
  if k != 0:
    discard udivCallee(10, k)
  let r = udivCallee(10, k)
  if r == 11: symexTarget("hit")

proc sutUDivTwiceGuarded(k: uint64) =
  ## Both calls sit under the guard: reusing the summary is legitimate.
  if k != 0:
    discard udivCallee(10, k)
    let r = udivCallee(10, k)
    if r == 11: symexTarget("hit")

proc sutModTwice(x: int) =
  if x != low(int):
    discard modCallee(x, -1)
  let r = modCallee(x, -1)
  if r != 0: symexTarget("hit")

proc sutModTwiceGuarded(x: int) =
  if x != low(int):
    discard modCallee(x, -1)
    let r = modCallee(x, -1)
    if r != 0: symexTarget("hit")

const kDom = sampled([0'u64, 1, 2, 3, 5, 10, 11])

proc hitsOf[T](r: SymexResult[T]; name: string): int =
  let st = r.callStats.filterIt(it.name == name)
  if st.len == 1: st[0].cacheHits else: -1

suite "W1-d1c cached prunes":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 280

  test "div: the second call admitting zero is not a trusted sxUnsat":
    let r = symexFind(sutUDivTwice, tLabel("hit"))
    checkpoint show(r.errors)
    check not r.trusted
    check r.status != sxSat
    check r.errors.named(ubUnsignedDivZero)

  test "mod: the same":
    let r = symexFind(sutModTwice, tLabel("hit"))
    checkpoint show(r.errors)
    check not r.trusted
    check r.status != sxSat
    check r.errors.named(ubIntMinModMinusOne)

  test "control: both calls guarded reuse the summary, verdict stays trusted":
    let r = symexFind(sutUDivTwiceGuarded, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check r.trusted
    check not r.errors.named(ubUnsignedDivZero)
    check r.hitsOf("udivCallee") >= 1

  test "control: mod, both guarded":
    let r = symexFind(sutModTwiceGuarded, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    check r.trusted
    check not r.errors.named(ubIntMinModMinusOne)
    ## No cache-hit assertion: a signed `mod` callee carries a divisor
    ## defect-survivor fact, so it is never cached (it is walked per call)
    ## and there is no summary to reuse.
    check r.hitsOf("modCallee") == 0

  test "the failing div shape also walks the callee and reuses the guarded summary":
    ## The k != 0 path replays the first summary (prune holds there); the
    ## k == 0 path re-walks, which is what halts it.
    let r = symexFind(sutUDivTwice, tLabel("hit"))
    check r.hitsOf("udivCallee") >= 1
    check r.callStats.anyIt(it.name == "udivCallee" and it.walked >= 2)
