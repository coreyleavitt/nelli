## RFC-0005 (soundness channels) slice S8bv -- S8bq's remainder, item 1 (a set[char]: a count).
##
## `for x in s` over a builtin `set[T]` declined. It is unrolled over `T`'s
## domain in ascending order, exactly as `system.items` iterates (`T(i) in a`
## re-read at every step), up to `maxBitSetIterDomain` values. Split so each
## file stays under 60 s on Windows.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

proc itCharCount(s: set[char]) =
  var k = 0
  for c in s: inc k
  if k == 2: symexTarget("bv_it_char_count")

suite "S8bv: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 250

suite "S8bv (1): for x in a builtin set":
  test "a set[char]: a count":
    check verdict(itCharCount, "bv_it_char_count").status == sxSat
