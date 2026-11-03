## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 2 of 9 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder3`,
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

template clean(fn: typed, lbl: string, want: SymexStatusKind) =
  ## The verdict, with nothing recorded at all.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0

proc s8axDown(k: int): bool =
  if k <= 0: true else: s8axDown(k - 1)

proc sutDownBounded(n: int) =
  symexAssume(n >= 0 and n <= 20)
  if s8axDown(n) and n == 20: symexTarget("db")

proc sutDownDeep(n: int) =
  symexAssume(n >= 0)
  if s8axDown(n) and n == 30: symexTarget("dd")

suite "RFC-0005 S8ax (3): the call depth adapts to the frontier":
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
