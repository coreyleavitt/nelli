## RFC-0005 (soundness channels) slice S8be -- S8ax's remainder.
##
## Items (9)-(11); (1)-(8) are in `tsymex_rfc0005_s8be_remainder`, (12)-(13)
## in `tsymex_rfc0005_s8be_remainder_c`
## (RFC-0005 S8bo split the suite, which took 83 s to compile and run).
##
## Each section below names the wrong verdict, the crash or the decline it
## closes. Every expected value was probed against the real compiler (Nim
## 2.2.10, the debug build the test binary itself is).
import std/[unittest, strutils, os]
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

template verdict(fn: typed, tgt: SymexTarget, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template verdictS(fn: typed, tgt: SymexTarget, want: SymexStatusKind,
                  s: SymexSettings) =
  block:
    let r = symexFind(fn, tgt, s)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template declines(fn: typed, tgt: SymexTarget, kind: SymexErrorKind,
                  needle: string) =
  block:
    let r = symexFind(fn, tgt)
    checkpoint $tgt & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(kind)
    check needle in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (9) a returned tuple of closures ----------------------------------------
#
# DECLINE before S8be (`ceUnsupportedHof`): a routine returning a tuple of
# closures sharing one capture. A closure called through a tuple field
# (`t.f()`) did not compile ("cannot resolve callee `t.f`").

proc s8bePair(start: int): (proc(): int, proc(): int) =
  var c = start
  result = (proc(): int =
              c += 1
              c,
            proc(): int = c)

proc sutCloTuple(v: int) =
  symexAssume(v > -100 and v < 100)
  let (inc1, get1) = s8bePair(v)
  discard inc1()
  if get1() == v + 1: symexTarget("ok")
  if get1() != v + 1: symexTarget("bad")

proc s8beTriple(start: int): tuple[n: int, f: proc(): int] =
  var c = start
  (n: start * 2, f: proc(): int =
                      c += 3
                      c)

proc sutCloNamed(v: int) =
  symexAssume(v > -100 and v < 100)
  let t = s8beTriple(v)
  let a = t.f()
  discard t.f()
  if a == v + 3 and t.f() == v + 9 and t.n == 2 * v: symexTarget("ok")
  if a != v + 3 or t.n != 2 * v: symexTarget("bad")

# ---- (10) an opaque routine applying a closure -------------------------------
#
# WRONG VERDICT before S8be: an opaque routine handed a closure kept the
# closure's captures unchanged, so `x == v + 1` after it applied the
# closure was a false `sxUnsat`.

proc s8beApplyOpaque(f: proc(): int) {.symexOpaque.} =
  discard f()

proc sutOpaqueClo(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let f = proc(): int =
    x += 1
    x
  s8beApplyOpaque(f)
  if x == v + 1: symexTarget("moved")

# ---- (11) the call cache under capture cells ---------------------------------
#
# A routine reading a capture or a global is cached keyed by their values
# as it found them; one that writes one is not cached. Before S8be such a
# frame bypassed the cache (cost, not soundness); these pins guard the
# staleness the key must rule out.

proc s8beFib(k: int): int =
  if k < 2: k else: s8beFib(k - 1) + s8beFib(k - 2)

proc sutCacheCap(n: int) =
  symexAssume(n >= 0 and n <= 6)
  var c = 0
  let bump = proc() = c += 1
  bump()
  if s8beFib(n) + c == 9: symexTarget("hit")

proc sutCapStale(v: int) =
  symexAssume(v >= 0 and v < 10)
  var c = v
  proc rd(): int = c * 2
  let a = rd()
  c = c + 1
  let b = rd()
  if b == a + 2: symexTarget("ok")
  if b != a + 2: symexTarget("bad")

var s8beG = 0
proc s8beRdG(k: int): int = s8beG + k

proc sutGlobStale(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8beG = v
  let a = s8beRdG(1)
  s8beG = v + 5
  let b = s8beRdG(1)
  if b == a + 5: symexTarget("ok")
  if b != a + 5: symexTarget("bad")

var s8beCnt = 0
proc s8beTick(k: int): int =
  s8beCnt += 1
  k

proc sutGlobWrite(v: int) =
  symexAssume(v >= 0 and v < 10)
  s8beCnt = 0
  discard s8beTick(1)
  discard s8beTick(1)
  if s8beCnt == 2: symexTarget("ok")
  if s8beCnt != 2: symexTarget("bad")

suite "RFC-0005 S8be: walker version":
  test "symexWalkerVersion is at least 205":
    check parseInt(symexWalkerVersion) >= 205

suite "RFC-0005 S8be (9): a returned tuple of closures":
  test "an unnamed tuple":
    verdict(sutCloTuple, tLabel("ok"), sxSat)
    verdict(sutCloTuple, tLabel("bad"), sxUnsat)
  test "a named tuple, the closure called through its field":
    verdict(sutCloNamed, tLabel("ok"), sxSat)
    verdict(sutCloNamed, tLabel("bad"), sxUnsat)

suite "RFC-0005 S8be (10): an opaque routine applying a closure":
  test "the closure's captures are havocked":
    verdict(sutOpaqueClo, tLabel("moved"), sxSat)

suite "RFC-0005 S8be (11): the call cache under capture cells":
  test "a recursion under a frame with a capture cell":
    verdictS(sutCacheCap, tLabel("hit"), sxSat,
             SymexSettings(budget: ResourceBudget(maxCallDepth: 8,
                                                  maxRecursionDepth: 0)))
  test "a capture read after a write is read again":
    verdict(sutCapStale, tLabel("ok"), sxSat)
    verdict(sutCapStale, tLabel("bad"), sxUnsat)
  test "a global read after a write is read again":
    verdict(sutGlobStale, tLabel("ok"), sxSat)
    verdict(sutGlobStale, tLabel("bad"), sxUnsat)
  test "a call writing a global is walked each time":
    verdict(sutGlobWrite, tLabel("ok"), sxSat)
    verdict(sutGlobWrite, tLabel("bad"), sxUnsat)

