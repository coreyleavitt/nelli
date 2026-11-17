## RFC-0016 K9c-g. Every path that reaches a seq element of a type the model
## does not back (`seq[seq[int]]`, `seq[Table[int,int]]`) must be exact or
## decline `seNestedSeqUnsupported`. None may record `weInternalWalkerFault`,
## which is the label for a walker bug, not for a known modelling gap.
##
## Each probe runs over four sources of the seq: an empty literal (E), a
## non-empty literal (L), `newSeq[T](k)` (N), and a parameter (P). A path
## passes when its verdict is exact and trusted, or `sxUnknown` carrying
## `seNestedSeqUnsupported`; `weInternalWalkerFault` never passes.
from ./s8cu_helpers import named, show
import std/[unittest, strutils, sequtils, tables, algorithm, macros]
import nelli/symex
import nelli/smt/canonicalize

# ---- element-seq probes: `o` is a `seq[seq[int]]`, `k` an int ---------------
template bForIn(o, k: untyped) =
  for x in o:
    if x.len == 0: symexTarget("t")
  symexTarget("t")
template bForItems(o, k: untyped) =
  for x in o.items:
    if x.len == 0: symexTarget("t")
  symexTarget("t")
template bForPairs(o, k: untyped) =
  for i, x in o.pairs:
    if i == 0 and x.len == 0: symexTarget("t")
  symexTarget("t")
template bForIdx(o, k: untyped) =
  for i in 0 ..< o.len:
    if o[i].len == 0: symexTarget("t")
  symexTarget("t")
template bForIdxAssign(o, k: untyped) =
  for i in 0 ..< o.len:
    o[i] = @[i]
  symexTarget("t")
template bForMitems(o, k: untyped) =
  for x in o.mitems:
    x.add 1
  symexTarget("t")
template bMapIt(o, k: untyped) =
  let m = o.mapIt(it.len)
  if m.len >= 0: symexTarget("t")
template bFilterIt(o, k: untyped) =
  let m = o.filterIt(it.len > 0)
  if m.len >= 0: symexTarget("t")
template bFoldl(o, k: untyped) =
  let s = o.foldl(a + b.len, 0)
  if s >= 0: symexTarget("t")
template bAnyIt(o, k: untyped) =
  if o.anyIt(it.len > 0): symexTarget("t")
  symexTarget("t")
template bAllIt(o, k: untyped) =
  if o.allIt(it.len > 0): symexTarget("t")
  symexTarget("t")
template bContains(o, k: untyped) =
  if @[1] in o: symexTarget("t")
  symexTarget("t")
template bFind(o, k: untyped) =
  if o.find(@[1]) >= 0: symexTarget("t")
  symexTarget("t")
template bSlice(o, k: untyped) =
  let s = o[0 ..< 1]
  if s.len >= 0: symexTarget("t")
template bSliceTail(o, k: untyped) =
  let s = o[1 .. ^1]
  if s.len >= 0: symexTarget("t")
template bConcat(o, k: untyped) =
  let c = o & o
  if c.len >= 0: symexTarget("t")
template bConcatElem(o, k: untyped) =
  let c = o & @[1]
  if c.len >= 0: symexTarget("t")
template bAdd(o, k: untyped) =
  o.add @[k]
  symexTarget("t")
template bLenOfElem(o, k: untyped) =
  if o.len > 0 and o[0].len == 0: symexTarget("t")
  symexTarget("t")
template bPop(o, k: untyped) =
  if o.len > 0:
    discard o.pop()
  symexTarget("t")
template bDel(o, k: untyped) =
  if o.len > 0: o.del(0)
  symexTarget("t")
template bInsert(o, k: untyped) =
  o.insert(@[1], 0)
  symexTarget("t")
template bSetLen(o, k: untyped) =
  o.setLen(0)
  symexTarget("t")
template bReverse(o, k: untyped) =
  o.reverse()
  symexTarget("t")
template bEq(o, k: untyped) =
  let p = o
  if p == o: symexTarget("t")
  symexTarget("t")
template bCopyRead(o, k: untyped) =
  let p = o
  if p.len > 0 and p[0].len == 0: symexTarget("t")
  symexTarget("t")
template bAssign(o, k: untyped) =
  if o.len > 0: o[0] = @[1]
  symexTarget("t")
template bFirstLast(o, k: untyped) =
  if o.len > 0:
    let a = o[0]
    let b = o[o.len - 1]
    if a.len == b.len: symexTarget("t")
  symexTarget("t")
template bIndexK(o, k: untyped) =
  let a = o[k]
  if a.len >= 0: symexTarget("t")
template bZip(o, k: untyped) =
  let z = zip(o, o)
  if z.len >= 0: symexTarget("t")
template bCount(o, k: untyped) =
  if o.count(@[1]) >= 0: symexTarget("t")
template bConcatSeqs(o, k: untyped) =
  let c = concat(o)
  if c.len >= 0: symexTarget("t")
template bMapProc(o, k: untyped) =
  let m = o.map(proc (x: seq[int]): int = x.len)
  if m.len >= 0: symexTarget("t")
template bLenOnly(o, k: untyped) =
  if o.len == 0: symexTarget("t")
  symexTarget("t")
template bHighLow(o, k: untyped) =
  if o.high >= 0: symexTarget("t")
  symexTarget("t")
template bWhile(o, k: untyped) =
  var i = 0
  while i < o.len:
    if o[i].len == 0: symexTarget("t")
    inc i
  symexTarget("t")

# ---- Table-element probes: `o` is a `seq[Table[int,int]]` ------------------
template tForIn(o, k: untyped) =
  for x in o:
    if x.len == 0: symexTarget("t")
  symexTarget("t")
template tRead(o, k: untyped) =
  if o.len > 0 and o[0].len == 0: symexTarget("t")
  symexTarget("t")
template tReadK(o, k: untyped) =
  let a = o[k]
  if a.len >= 0: symexTarget("t")
template tAssign(o, k: untyped) =
  if o.len > 0: o[0] = initTable[int, int]()
  symexTarget("t")
template tPop(o, k: untyped) =
  if o.len > 0: discard o.pop()
  symexTarget("t")
template tMapIt(o, k: untyped) =
  let m = o.mapIt(it.len)
  if m.len >= 0: symexTarget("t")
template tAdd(o, k: untyped) =
  o.add initTable[int, int]()
  symexTarget("t")
template tSlice(o, k: untyped) =
  let s = o[0 ..< 1]
  if s.len >= 0: symexTarget("t")
template tConcat(o, k: untyped) =
  let c = o & o
  if c.len >= 0: symexTarget("t")
template tContains(o, k: untyped) =
  if initTable[int, int]() in o: symexTarget("t")
  symexTarget("t")

macro genProbes(prefix, bodyPrefix, elemTy, litA, litB: static string;
                names: static seq[string]): untyped =
  ## `<prefix><name>{E,L,N,P}`, each calling the template `<bodyPrefix><name>`.
  var src = ""
  for n in names:
    let body = bodyPrefix & n
    let nm = prefix & n
    src.add "proc " & nm & "E(k: int) =\n  var o: seq[" & elemTy &
      "] = @[]\n  " & body & "(o, k)\n"
    src.add "proc " & nm & "L(k: int) =\n  var o: seq[" & elemTy &
      "] = @[" & litA & ", " & litB & "]\n  " & body & "(o, k)\n"
    src.add "proc " & nm & "N(k: int) =\n  symexAssume(k >= 0 and k <= 3)\n" &
      "  var o = newSeq[" & elemTy & "](k)\n  " & body & "(o, k)\n"
    src.add "proc " & nm & "P(o0: seq[" & elemTy & "]; k: int) =\n" &
      "  var o = o0\n  " & body & "(o, k)\n"
  parseStmt(src)

macro checkProbes(prefix: static string; names: static seq[string]): untyped =
  var src = ""
  for n in names:
    for suf in ["E", "L", "N", "P"]:
      src.add "probeCheck(" & prefix & n & suf & ")\n"
  parseStmt(src)

const
  seqNames = @["ForIn", "ForItems", "ForPairs", "ForIdx", "ForIdxAssign",
    "ForMitems", "MapIt", "FilterIt", "Foldl", "AnyIt", "AllIt", "Contains",
    "Find", "Slice", "SliceTail", "Concat", "ConcatElem", "Add", "LenOfElem",
    "Pop", "Del", "Insert", "SetLen", "Reverse", "Eq", "CopyRead", "Assign",
    "FirstLast", "IndexK", "Zip", "Count", "ConcatSeqs", "MapProc", "LenOnly",
    "HighLow", "While"]
  tabNames = @["ForIn", "Read", "ReadK", "Assign", "Pop", "MapIt", "Add",
    "Slice", "Concat", "Contains"]

genProbes("s", "b", "seq[int]", "@[1]", "@[2]", seqNames)
genProbes("t", "t", "Table[int, int]", "initTable[int, int]()",
          "initTable[int, int]()", tabNames)

template probeCheck(fn: untyped) =
  block:
    let r = symexFind(fn, tLabel("t"))
    checkpoint astToStr(fn) & " " & $r.status & " " & show(r.errors)
    check not r.errors.named(weInternalWalkerFault)
    # Exact (a verdict, or the raise the SUT really makes), or a classified
    # decline; never a silent one.
    check (r.status in {sxSat, sxUnsat, sxRaised} and r.trusted) or
          (r.status == sxUnknown and r.errors.anyIt(taintsRun(it)))

suite "K9c-g unbacked element paths":
  test "seq[seq[int]] paths never record weInternalWalkerFault":
    checkProbes("s", seqNames)
  test "seq[Table[int,int]] paths never record weInternalWalkerFault":
    checkProbes("t", tabNames)

  test "insert into an empty seq of an unbacked element declines as a gap":
    let r = symexFind(sInsertE, tLabel("t"))
    check r.status == sxUnknown
    check r.errors.named(seNestedSeqUnsupported)
    check not r.errors.named(weInternalWalkerFault)

  test "a loop over an empty seq of an unbacked element runs zero times":
    let r = symexFind(sForInE, tLabel("t"))
    check r.status == sxSat and r.trusted
    let w = symexFind(sWhileE, tLabel("t"))
    check w.status == sxSat and w.trusted

  test "walker version floor >= 374 (RFC-0016 K9c-g)":
    check parseInt(symexWalkerVersion) >= 374
