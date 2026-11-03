## RFC-0005 (soundness channels) slice S8au -- the S8an / S8ag remainder.
##
## Pinned here (the RFC's "As landed (S8au)" note has the design and the
## measurements):
##   (1) a local distinct value with no distinct-typed parameter: closed by
##       S8ad (`ensureDistinctSort`, walker 175); re-pinned over more shapes
##       (borrowed `+` / `==` / `<`, default-initialised, float base, a
##       returned value, an object field). A `seq` of a distinct type was
##       a scoped decline (a different mechanism, reported); RFC-0005 S8ba
##       models it;
##   (2) `start < 0 and y > 1 and start div y == start` under the sequence
##       theory: closed by S8ad (`divRangeFacts`) and pinned in
##       `tsymex_rfc0005_s8ad_remainder`; re-measured for S8au, not
##       re-walked here;
##   (3) a copy-in/copy-out `var` actual (or an `addr` actual) whose heap
##       cell a global or a capture the callee reaches can also hold:
##       RED, a false `sxSat` (the callee's write through the global was
##       lost to the write-back); S8au declined it (`feUnsupportedOp`),
##       and RFC-0005 S8ba passes the cell by reference, so the dead
##       labels are `sxUnsat` (`tsymex_rfc0005_s8ba_remainder` (4));
##   (4) every `find` needle (a literal of any length, a computed one) and
##       `rfind` lower to S8ag's index split: the axioms by a randomized
##       differential against Z3's own terms with three mutants, and the
##       walker by hits that were `sxUnknown` at the base;
##   (5) the chain facts link consecutive splits only (counted);
##   (6) the `c notin t` form follows the linked Z3 version;
##   and `var ptr` formals: `f(addr x)` does not compile; a local `p = addr
##   x` passed to one was `heUnsafeCast`, and is now S8an's local pointer.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8au_remainder`, `tsymex_rfc0005_s8au_remainder_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 75 s).

import std/[unittest, strutils, random, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- (1) local distinct values ------------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

type Secs = distinct float
proc `+`(a, b: Secs): Secs {.borrow.}
proc `<`(a, b: Secs): bool {.borrow.}

# The walker side of (4): each of these lowered to Z3's own term at the base
# (no split). `mf_dead` and `rf_dead` were `sxUnknown` there (`mf_dead`
# 20.3M units, 350 s on Z3 5.1; `rf_dead` 20M, 163 s); every one is now
# decided through splits (`mf_dead` 0.1M units; `rf_dead` 12k with the
# rfind-find link, 10M without it), its live neighbour with a witness the
# compiled code agrees with.

proc mFind(s: string) =
  let i = s.find("\r\n")
  if i == 3:
    let j = s.find("\r\n", i + 2)
    if j == 7: symexTarget("mf")
  if i >= 0 and s[i + 1] != '\n': symexTarget("mf_dead")

proc mOverlap(s: string) =
  let i = s.find("aa")
  if i == 1 and s.len == 4: symexTarget("mo")
  if i == 2 and s[1] == 'a': symexTarget("mo_dead")

proc symFind(s, t: string) =
  symexAssume(t.len <= 2 and s.len <= 6)
  let i = s.find(t)
  if i == 2 and t.len == 2: symexTarget("sf")
  if i >= 0 and i + t.len > s.len: symexTarget("sf_dead")
  if t.len == 0 and i != 0: symexTarget("sf_dead2")

proc rFind(s: string) =
  let i = s.rfind("ab")
  if i == 2 and s.len == 6: symexTarget("rf")
  if i >= 0 and i < 100 and s.find("ab", i + 1) >= 0: symexTarget("rf_dead")

proc rFindChar(s: string) =
  let i = s.rfind(':')
  if i == 3 and s.len == 5: symexTarget("rc")
  if i >= 0 and i < s.len - 1 and s[s.len - 1] == ':': symexTarget("rc_dead")

proc rFindEmpty(s: string) =
  if s.rfind("") == 2: symexTarget("re")
  if s.rfind("") != s.len: symexTarget("re_dead")

template split(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    check indexSplitCounter > 0   # the find / rfind was split
    r

suite "S8au (4): finds and rfinds the base left to Z3 are split":

  test "two-character literal needle, chained":
    let r = split(mFind, "mf", sxSat)
    if r.status == sxSat:
      let s = r.witness[0]
      check s.find("\r\n") == 3 and s.find("\r\n", 5) == 7
    discard split(mFind, "mf_dead", sxUnsat)

  test "an overlapping needle":
    let r = split(mOverlap, "mo", sxSat)
    if r.status == sxSat: check r.witness[0].find("aa") == 1
    discard split(mOverlap, "mo_dead", sxUnsat)

  test "a computed needle, the empty one included":
    let r = split(symFind, "sf", sxSat)
    if r.status == sxSat:
      let (s, t) = r.witness
      check s.find(t) == 2 and t.len == 2
    discard split(symFind, "sf_dead", sxUnsat)
    discard split(symFind, "sf_dead2", sxUnsat)

  test "rfind of a literal, a char and the empty needle":
    let r = split(rFind, "rf", sxSat)
    if r.status == sxSat: check r.witness[0].rfind("ab") == 2
    discard split(rFind, "rf_dead", sxUnsat)
    let c = split(rFindChar, "rc", sxSat)
    if c.status == sxSat: check c.witness[0].rfind(':') == 3
    discard split(rFindChar, "rc_dead", sxUnsat)
    let e = split(rFindEmpty, "re", sxSat)
    if e.status == sxSat: check e.witness[0].len == 2
    discard split(rFindEmpty, "re_dead", sxUnsat)

# ---- (5) the chain facts: consecutive, not all pairs --------------------------
#
# S8ag asserted a chain fact (`indexSplitChain`) for every ordered pair of
# reached splits of one haystack: n (n - 1) for n splits. Each fact is
# valid on its own (implied by the two splits' axioms; S8ag (1) checks it
# on random instances), so any subset is exact, and S8au keeps the
# consecutive ones in lowering order: n - 1. Only `find` splits chain (an
# `rfind` split has no `start`), and only on one haystack.

suite "S8au (5): chain facts between consecutive splits only":

  test "four chained finds: 8 axioms and 3 chains (S8ag: 12 chains)":
    indexSplits.setLen 0
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let t = mkStringVar(ctx, "t")
    var ix = lowerIndexSplit(s, mkString(ctx, ":"), mkInt(ctx, 0))
    for _ in 1 .. 3:
      ix = lowerIndexSplit(s, mkString(ctx, ":"), ix + mkInt(ctx, 1))
    check indexSplitRoots(ctx, @[ix > mkInt(ctx, 0)]).len == 4 * 2 + 3
    # An rfind of the same haystack and a find of another add their two
    # axioms each and no chain.
    let r = lowerIndexSplit(s, mkString(ctx, "ab"), mkInt(ctx, 0), last = true)
    let o = lowerIndexSplit(t, mkString(ctx, ":"), mkInt(ctx, 0))
    check indexSplitRoots(ctx, @[ix > mkInt(ctx, 0), r > o]).len ==
      6 * 2 + 3
    indexSplits.setLen 0

  test "a split reached only through another's needle is reached":
    ## A computed needle may hold a split (`s.find(s[0 ..< s.find(":")])`).
    indexSplits.setLen 0
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let inner = lowerIndexSplit(s, mkString(ctx, ":"), mkInt(ctx, 0))
    let outer = lowerIndexSplit(mkStringVar(ctx, "u"),
                                substr(s, mkInt(ctx, 0), inner),
                                mkInt(ctx, 0))
    check indexSplitRoots(ctx, @[outer > mkInt(ctx, 0)]).len == 4
    indexSplits.setLen 0

# ---- (6) the `c notin t` form, per Z3 version ---------------------------------
#
# S8ag measured the one-character regex `t in (allchar & ~c)*` against
# `not str.contains(t, c)`: on Z3 5.1 the regex is far cheaper (N36 8.2M
# units against 53.5M; round-6 B1-3 needs it), on 4.13.4 `not contains`
# is cheaper for N36 (8.3M against 15.3M). S8au measured both on both
# versions (the RFC's S8au note) and takes each version's cheaper form
# (`notInFormFor`); the differential in (4) checks both forms exact.

suite "S8au (6): the c-notin-t form follows the linked Z3":

  test "5.x takes the regex, 4.x not-contains":
    check notInFormFor(5, 1) == nfRegex
    check notInFormFor(4, 13) == nfNotContains
    let v = z3Version()
    check notInForm() == notInFormFor(int(v.major), int(v.minor))

suite "S8au: walker version floor":

  test "symexWalkerVersion >= 194":
    check parseInt(symexWalkerVersion) >= 194
