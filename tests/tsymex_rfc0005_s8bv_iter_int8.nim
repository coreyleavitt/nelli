## RFC-0005 (soundness channels) slice S8bv -- S8bq's remainder, item 1 (a set[int8]: its low bound).
##
## `for x in s` over a builtin `set[T]` declined. It is unrolled over `T`'s
## domain in ascending order, exactly as `system.items` iterates (`T(i) in a`
## re-read at every step), up to `maxBitSetIterDomain` values. Each fixture is
## also run natively (`symexCaptureBegin`): symex's verdict agrees with the
## targets a real run hits. Split so each file stays under 60 s on Windows.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc hasMsg(errs: seq[SymexErrorInfo]; k: SymexErrorKind; sub: string): bool =
  for e in errs:
    if e.kind == k and sub in e.msg: return true
  false

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

template nativeHits(body: untyped): HashSet[string] =
  symexCaptureBegin()
  body
  symexCaptureEnd()
proc itInt8First(s: set[int8]) =
  var first = 0'i8
  var seen = false
  for v in s:
    if not seen:
      first = v
      seen = true
  if seen and first > 0 and -5'i8 in s: symexTarget("bv_it_int8_first")
  if seen and first == -128'i8: symexTarget("bv_it_int8_min")

suite "S8bv: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 226

suite "S8bv (1): for x in a builtin set":
  test "a signed set starts at its low bound":
    check verdict(itInt8First, "bv_it_int8_min").status == sxSat
    check "bv_it_int8_min" in nativeHits(itInt8First({-128'i8, 3}))
