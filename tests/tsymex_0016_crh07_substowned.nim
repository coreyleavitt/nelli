## RFC-0016 CRH-07: `checkExact` owns the terms it substitutes.
##
## Each recursive value (`replace`'s, and `strutils.count`'s) is a fresh `v`
## whose definition `v == term` sits in `regexRecDefConds`. After step 0,
## `checkExact` resolves each definition's term against the earlier ones
## (`Z3_substitute`) and substitutes them all into the query. It held the
## resolved term raw: a `Z3_substitute` result has no reference until it is
## wrapped, and Z3 frees it at the next call that returns an AST. The roots
## built over it then read freed nodes, and releasing them crashed
## (SIGSEGV at `byteLeafIds`' `dec_ref`, S8cf's report). S8cf avoided the
## crash by inlining `count`'s term; that avoidance is gone, so `count`
## reaches the substitution again.
##
## RED (the avoidance removed, the raw hold kept): `countPlain` read
## `sxUnsat` although `"aa"` satisfies it, then `countNo` crashed with SIGSEGV
## in `byteLeafIds`' `=destroy`. Under the ASan libz3
## (`scripts/build-z3-asan.sh`) the first stale read is reported as a
## heap-use-after-free. GREEN: each verdict is native's. In
## `scripts/asan-slice.sh`'s core set.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/canonicalize

proc countPlain(s: string) =
  # one definition: `count` alone
  if s.len <= 16 and s.count('a') == 2:
    symexTarget("crh07_plain")

proc countNo(s: string) =
  # two definitions, the second naming the first: `count` over a `replace`
  if s.len <= 16 and s.replace(re"a", "-").count('a') > 0:
    symexTarget("crh07_count_no")

proc countBy(s: string) =
  if s.len <= 16 and s.replace(re"a", "-").count('-') == 2:
    symexTarget("crh07_count_by")

proc nested(s: string) =
  # two `replace` definitions, the outer naming the inner
  if s.len <= 8 and s.replace(re"a", "b").replace(re"b", "c") == "cc":
    symexTarget("crh07_nested")

proc nestedNo(s: string) =
  if s.len <= 8 and s.replace(re"a", "b").replace(re"b", "c").contains("a"):
    symexTarget("crh07_nested_no")

suite "RFC-0016 CRH-07: substituted definition terms are owned":
  test "native agrees":
    check "aa".count('a') == 2
    check "xaxax".replace(re"a", "-").count('-') == 2
    check "ab".replace(re"a", "b").replace(re"b", "c") == "cc"

  test "count alone":
    check symexFind(countPlain, tLabel("crh07_plain")).status == sxSat

  test "count over a replace value":
    check symexFind(countNo, tLabel("crh07_count_no")).status == sxUnsat
    check symexFind(countBy, tLabel("crh07_count_by")).status == sxSat

  test "a replace over a replace value":
    check symexFind(nested, tLabel("crh07_nested")).status == sxSat
    # No subject reaches it. Z3 leaves the substituted query undecided
    # (`sxUnknown`): a precision limit of the nested term, not this slice's.
    # What this pins is that it is never a false `sxSat` and never a crash.
    check symexFind(nestedNo, tLabel("crh07_nested_no")).status != sxSat

  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 372
