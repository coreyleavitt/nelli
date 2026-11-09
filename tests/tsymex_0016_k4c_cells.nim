## RFC-0016 K4c (section 8.1): the stdlib-body axis's declined and `never`
## cells, each pinned through `symexFind`, and the declines name their cell.
##
##   * W-47: the four stdlib generic objects are rows (`declined`), and the
##     decline carries the row's cell (the type bridge's catch-all reads the
##     axis; a head with no row is the absent case, the same kind);
##   * STY-02: Table and HashSet iteration order are `never` rows; the
##     walker's declines name them;
##   * STY-06: `algorithm.sort` on a symbolic-length sequence is a `never`
##     row its decline names; concurrency and full Unicode case folding are
##     `never` rows with no declining site yet (allowlisted, see the file);
##   * AUD-11: `rfind` is decided exactly, which is the coverage note's claim.
import std/[unittest, strutils, algorithm, options, tables, sets, deques]
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/stdlib_rows
import ./s8cu_helpers

proc sOpt(o: Option[int]) =
  if o.isSome: symexTarget("hit")
proc sOT(o: OrderedTable[int, int]) =
  if o.len == 1: symexTarget("hit")
proc sCT(o: CountTable[int]) =
  if o.len == 1: symexTarget("hit")
proc sDq(o: Deque[int]) =
  if o.len == 1: symexTarget("hit")
proc sHS(a: int) =
  var h = initHashSet[int]()
  h.incl a
  h.incl 5
  for x in h:
    if x == 3: symexTarget("hit")
proc sTbl(a: int) =
  var t = initTable[int, int]()
  t[a] = 1
  t[5] = 2
  var first = -1
  for k in t.keys:
    first = k
    break
  if first == 3 and a == 3: symexTarget("hit")
proc sSort(s: seq[int]) =
  var t = s
  t.sort()
  if t.len > 1 and t[0] == 3: symexTarget("hit")
proc sRfind(a: int) =
  let s = if a > 3: "abab" else: "ab"
  if s.rfind('b') == 3 and a == 5: symexTarget("hit")

template declined(sut: untyped; cell: static string; kind: SymexErrorKind) =
  test cell:
    let c = cellKey(axStdlibBody, cell)
    pinDecline(sut, c, kind, needle = render(c))

suite "K4c W-47: stdlib generic objects are rows":
  declined(sOpt, "options.Option", feUnsupportedParamType)
  declined(sOT, "tables.OrderedTable", feUnsupportedParamType)
  declined(sCT, "tables.CountTable", feUnsupportedParamType)
  declined(sDq, "deques.Deque", feUnsupportedParamType)

  test "a declined row names a kind and is open work (iModel)":
    for c in stdlibAxis.cells:
      if render(c.cell) in ["stdlib:options.Option", "stdlib:deques.Deque"]:
        check not c.admitted
        check c.intent == iModel

  test "a head with no row is the absent case with the same kind":
    let a = admitStdlibBody("tables.Table", ssType,
                            absent = some(feUnsupportedParamType))
    check not a.admitted
    check a.decline[0] == some(feUnsupportedParamType)
    check "stdlib:tables.Table" in a.decline[1]

suite "K4c STY-02: iteration order is a never row":
  test "stdlib:sets.HashSet/iterationOrder":
    let c = cellKey(axStdlibBody, "sets.HashSet/iterationOrder")
    pinDecline(sHS, c, feUnsupportedStmtKind, needle = render(c))
  test "stdlib:tables.Table/iterationOrder":
    let c = cellKey(axStdlibBody, "tables.Table/iterationOrder")
    pinDecline(sTbl, c, feTableIterOrder, needle = render(c))
  test "both are never rows":
    var seen = 0
    for c in stdlibAxis.cells:
      if render(c.cell) in ["stdlib:sets.HashSet/iterationOrder",
                            "stdlib:tables.Table/iterationOrder"]:
        inc seen
        check not c.admitted
        check c.intent == iNever
    check seen == 2

suite "K4c STY-06: what the walker cannot model of the stdlib":
  test "stdlib:algorithm.sort/symbolicLength":
    let c = cellKey(axStdlibBody, "algorithm.sort/symbolicLength")
    pinDecline(sSort, c, feUnsupportedOp, needle = render(c))
  test "concurrency and full Unicode case folding are never rows":
    var seen = 0
    for c in stdlibAxis.cells:
      if render(c.cell) in ["stdlib:typedthreads.createThread/concurrency",
                            "stdlib:unicode.toLower/fullCaseFold"]:
        inc seen
        check not c.admitted
        check c.intent == iNever
    check seen == 2

suite "K4c AUD-11: the indexof link covers native terms only":
  test "stdlib:strutils.rfind/indexofLink: rfind is decided exactly":
    let r = pinExact(sRfind, cellKey(axStdlibBody, "strutils.rfind/indexofLink"),
                     domain = sampled([0, 3, 4, 5, 6]))
    check r.status == sxSat
