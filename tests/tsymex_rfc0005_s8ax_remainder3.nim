## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 3 of 9 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder2`,
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

proc s8axFib(k: int): int =
  if k < 2: k else: s8axFib(k - 1) + s8axFib(k - 2)

proc s8axDown(k: int): bool =
  if k <= 0: true else: s8axDown(k - 1)

proc sutDownBounded(n: int) =
  symexAssume(n >= 0 and n <= 20)
  if s8axDown(n) and n == 20: symexTarget("db")

proc sutDownMixed(n: int) =
  symexAssume(n >= 0)
  if s8axDown(n) and n == 5: symexTarget("dm")

proc sutFibFree(x: int) =
  # `x` free: `fib` fans out, so the depth is not extended.
  if s8axFib(x) == 13: symexTarget("ff")

suite "RFC-0005 S8ax (3): the call depth adapts to the frontier":
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
