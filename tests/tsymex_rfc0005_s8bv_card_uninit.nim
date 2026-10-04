## RFC-0005 (soundness channels) slice S8bv -- S8bq's remainder, items 3
## and 4 (items 1 and 2 are in `tsymex_rfc0005_s8bv_remainder`).
##
## Item 3: a pigeonhole-hard `card` comparison (`card(s + {c}) > card(s) +
## 1` over `set[char]`) ran out of `seqQueryRLimit` (`sxUnknown`). Each
## query relating two counts carries their part identities (`card(a) ==
## card(a * b) + card(a - b)`, valid, so the models are its own), and decides.
##
## Item 4: `newSeqUninit` taints a read only where it reads an unwritten
## element: an inline `map` / `filter` forks (it tainted the whole path), a
## seq nested in a tuple or object call result keeps its written-ness (it
## declined), and a slice, a heap cell or a mapped array reads its base's
## (each counted as unwritten everywhere).
import std/[unittest, strutils, sets, sequtils]
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

# ---- item 3: pigeonhole-hard card queries -----------------------------------

proc phIncl(s: set[char]; c: char) =
  # S8bq's case: unbounded it ran past 280 s; bounded, `sxUnknown`.
  if card(s + {c}) > card(s) + 1: symexTarget("bv_ph_incl")

proc phUnion(s, t: set[char]) =
  if card(s) + card(t) < card(s + t): symexTarget("bv_ph_union")

proc phExcl(s: set[char]; c: char) =
  var u = s
  u.excl c
  if c in s and card(u) != card(s) - 1: symexTarget("bv_ph_excl")

proc phSplit(s, t: set[char]) =
  if card(s - t) + card(s * t) != card(s): symexTarget("bv_ph_split")

proc phSat(s, t: set[char]) =
  if card(s) == 100 and card(t) == 100 and card(s * t) == 50:
    symexTarget("bv_ph_sat")

# ---- item 4: newSeqUninit written-ness, precisely ------------------------

proc unMapOneArm(i, k: int) =
  # `map` reads every element; on this one path xs[1] is unwritten exactly
  # when `i == 0` (a symbolic index write).
  if i < 0 or i > 1 or k < 0 or k > 100: return
  var xs = newSeqUninit[int](2)
  xs[0] = k
  xs[i] = k
  let ys = xs.map(proc(x: int): int = x + 1)
  if i == 1 and ys[1] == 8: symexTarget("bv_un_map_written")
  if i == 0 and ys[0] == 8: symexTarget("bv_un_map_unwritten")

proc unFilterOneArm(i, k: int) =
  if i < 0 or i > 1 or k < 0 or k > 100: return
  var xs = newSeqUninit[int](2)
  xs[0] = k
  xs[i] = k
  let ys = xs.filter(proc(x: int): bool = x > 0)
  if i == 1 and ys.len == 2 and k == 3: symexTarget("bv_un_filter_written")
  if i == 0 and k == 3: symexTarget("bv_un_filter_unwritten")

proc mkUninitPair(k: int): (seq[int], int) =
  var s = newSeqUninit[int](2)
  s[0] = k
  (s, 1)

proc unPairWritten(k: int) =
  let p = mkUninitPair(k)
  if p[0][0] == 4 and p[1] == 1: symexTarget("bv_un_pair_written")

proc unPairUnwritten(k: int) =
  let p = mkUninitPair(k)
  if p[0][1] == 4: symexTarget("bv_un_pair_unwritten")

type UnBox = object
  s: seq[int]
  n: int

proc mkUninitBox(k: int): UnBox =
  result.s = newSeqUninit[int](3)
  result.s[2] = k
  result.n = 7

proc unBoxWritten(k: int) =
  let b = mkUninitBox(k)
  if b.s[2] == 5 and b.n == 7: symexTarget("bv_un_box_written")
  if b.s[0] == 5: symexTarget("bv_un_box_unwritten")

proc unSliceWritten(k: int) =
  var xs = newSeqUninit[int](4)
  xs[0] = k
  xs[1] = k
  let ys = xs[0 .. 1]
  if ys[1] == 3: symexTarget("bv_un_slice_written")
  let zs = xs[1 .. 2]
  if zs[1] == 3: symexTarget("bv_un_slice_unwritten")

type UnRef = ref object
  s: seq[int]

proc unHeapWritten(k: int) =
  let r = UnRef(s: newSeqUninit[int](2))
  r.s[0] = k
  if r.s[0] == 3: symexTarget("bv_un_heap_written")
  if r.s[1] == 3: symexTarget("bv_un_heap_unwritten")

proc unMappedWritten(n, k: int) =
  # A symbolic length: `map` is the array map over the data (axiom path,
  # itself `ceUnsupportedHof`: the closure is not applied per element).
  if n < 2 or n > 1000 or k < 0 or k > 100: return
  var xs = newSeqUninit[int](n)
  xs[0] = k
  let ys = xs.map(proc(x: int): int = x + 1)
  if ys[0] == 4: symexTarget("bv_un_mapped_written")

proc unMappedUnwritten(n, k: int) =
  if n < 2 or n > 1000 or k < 0 or k > 100: return
  var xs = newSeqUninit[int](n)
  xs[0] = k
  let ys = xs.map(proc(x: int): int = x + 1)
  if ys[1] == 4: symexTarget("bv_un_mapped_unwritten")

suite "S8bv: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 226

suite "S8bv (3): pigeonhole-hard card queries decide":
  test "card(s + {c}) is at most card(s) + 1":
    let r = verdict(phIncl, "bv_ph_incl")
    check r.status == sxUnsat
    check r.errors.len == 0
  test "card of a union is at most the sum":
    check verdict(phUnion, "bv_ph_union").status == sxUnsat
  test "excl of a member removes exactly one":
    check verdict(phExcl, "bv_ph_excl").status == sxUnsat
  test "a set splits into its difference and intersection":
    check verdict(phSplit, "bv_ph_split").status == sxUnsat
  test "a satisfiable count query still finds its model":
    let r = verdict(phSat, "bv_ph_sat")
    check r.status == sxSat
    check r.errors.len == 0
    check "bv_ph_sat" in nativeHits(phSat({'\x00'..'\x63'}, {'\x32'..'\x95'}))

const uninitReadText = "newSeqUninit element read before it is written"

proc clean(r: SymexResult): bool =
  ## The hit is on a path no unwritten read tainted (not a replay-confirmed
  ## spurious one).
  r.status == sxSat and scSpurious notin r.soundness.pathTaint

proc unsure(r: SymexResult): bool =
  ## The target is reached only through an unwritten read: undecided, or a
  ## spurious path the replay had to confirm.
  r.status == sxUnknown or scSpurious in r.soundness.pathTaint

suite "S8bv (4): newSeqUninit taints only an unwritten element's read":
  test "inline map taints only where it reads an unwritten element":
    check clean(verdict(unMapOneArm, "bv_un_map_written"))
    check "bv_un_map_written" in nativeHits(unMapOneArm(1, 7))
    check unsure(verdict(unMapOneArm, "bv_un_map_unwritten"))
  test "inline filter taints only where it reads an unwritten element":
    check clean(verdict(unFilterOneArm, "bv_un_filter_written"))
    check "bv_un_filter_written" in nativeHits(unFilterOneArm(1, 3))
    check unsure(verdict(unFilterOneArm, "bv_un_filter_unwritten"))
  test "a seq nested in a tuple call result keeps its written-ness":
    check clean(verdict(unPairWritten, "bv_un_pair_written"))
    check "bv_un_pair_written" in nativeHits(unPairWritten(4))
    check unsure(verdict(unPairUnwritten, "bv_un_pair_unwritten"))
  test "a seq field of an object call result keeps its written-ness":
    check clean(verdict(unBoxWritten, "bv_un_box_written"))
    check "bv_un_box_written" in nativeHits(unBoxWritten(5))
    check unsure(verdict(unBoxWritten, "bv_un_box_unwritten"))
  test "a slice carries its base's written-ness":
    check clean(verdict(unSliceWritten, "bv_un_slice_written"))
    check "bv_un_slice_written" in nativeHits(unSliceWritten(3))
    check unsure(verdict(unSliceWritten, "bv_un_slice_unwritten"))
  test "a heap cell carries its base's written-ness":
    check clean(verdict(unHeapWritten, "bv_un_heap_written"))
    check "bv_un_heap_written" in nativeHits(unHeapWritten(3))
    check unsure(verdict(unHeapWritten, "bv_un_heap_unwritten"))
  test "a mapped array carries its base's written-ness":
    # The axiom-path map is `ceUnsupportedHof` either way; the written
    # element's read is no longer an unwritten one.
    let r = verdict(unMappedWritten, "bv_un_mapped_written")
    check r.errors.hasKind(ceUnsupportedHof)
    check not r.errors.hasMsg(feUnsupportedOpHavoc, uninitReadText)
    check "bv_un_mapped_written" in nativeHits(unMappedWritten(2, 3))
    let u = verdict(unMappedUnwritten, "bv_un_mapped_unwritten")
    check u.status == sxUnknown
    check u.errors.hasMsg(feUnsupportedOpHavoc, uninitReadText)
