## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part c: Table iteration, leaf-split seq elements, a recursive value object to a
## bounded depth (items 6, 3).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
import std/[unittest, strutils, sequtils, tables, sets, hashes]
import nelli
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

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (6) Table iteration ---------------------------------------------------
#
# RFC-0005 S8bc: `pairs` / `keys` / `values` (and `for k, v in t`) over a
# Table is a bounded unroll over an enumeration of its present keys in a
# FREE order (`isTabKeys`). Nim's order is the hash order, so a table that
# can hold two or more entries taints the path `feTableIterOrder`
# (`dcFreshSymbol`): the candidate is replayed, and one whose label needs an
# order Nim does not produce is refuted to sxUnknown.

proc tiSum(a, b: int) =
  if a < -100 or a > 100 or b < -100 or b > 100: return   # no overflow
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var s = 0
  for k, v in t:
    s += v + k
  if s == 13 and a == 4: symexTarget("ti_sum")
  # Every enumeration sums the same: a + b + 3 over two entries, b + 2 over
  # one (a == b, the second write wins).
  if a != b and s != a + b + 3: symexTarget("ti_sum_dead")
  if a == b and s != b + 2: symexTarget("ti_sum_dead")

proc tiOrder(a, b: int) =
  # Nim 2.2.10 visits the keys 1, 2 of this table as 2 then 1 (probed).
  if a != 1 or b != 2: return
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var first = -1
  for k in t.keys:
    if first == -1: first = k
  if first == 2: symexTarget("ti_order_real")
  if first == 1: symexTarget("ti_order_other")

proc tiValues(a: int) =
  var t = initTable[string, int]()
  t["x"] = a
  t["y"] = 3
  var s = 0
  for v in t.values:
    s += v
  if s == 10: symexTarget("ti_values")

const tupleBudget = SymexSettings(budget: ResourceBudget(
  queryRLimit: 300_000_000'u))
  ## RFC-0005 batch 7: past `tiTuple`'s label search on both pinned Z3s
  ## (see its test), and not the 250M default, which a tainted path does
  ## not take as the caller's.

proc tiTuple(a: int) =
  # Bounded: `s += k * v` overflows for a huge `a`, a real `OverflowDefect`
  # that wins over the label (seen on Windows, RFC-0005 S8bc).
  if a < -1000 or a > 1000: return
  var t = initTable[int, int]()
  t[1] = a
  t[2] = 5
  var s = 0
  for (k, v) in t.pairs:
    s += k * v
  var u = 0
  for kv in t.pairs:
    u += kv[1]
  if s == 16 and u == a + 5: symexTarget("ti_tuple")

proc tiStrKey(x: string) =
  var t = initTable[string, int]()
  t["a"] = 1
  t[x] = 2
  var found = false
  for k in t.keys:
    if k == "zz":
      found = true
      break
  if found: symexTarget("ti_strkey")
  if t.len == 1 and x != "a": symexTarget("ti_strkey_dead")

proc tiParam(t: Table[int, int]) =
  symexAssume(t.len <= 3)
  var c = 0
  for k in t.keys:
    inc c
  if c != t.len: symexTarget("ti_param_dead")

proc tiOne(a: int) =
  var t = initTable[int, int]()
  for k in t.keys: symexTarget("ti_empty_dead")
  t[a] = 7
  for k, v in t:
    if k == 3 and v == 7: symexTarget("ti_one")

proc tiGrow(a: int) =
  var t = initTable[int, int]()
  t[1] = 1
  for k in t.keys:
    t[k + a] = 0
  symexTarget("ti_grow")

proc tiFloat(a: float) =
  var t = initTable[float, int]()
  t[a] = 1
  var c = 0
  for k in t.keys: inc c
  if c == 1: symexTarget("ti_float")

suite "S8bc (6): Table iteration":
  test "for k, v in t: an order-independent fold":
    let r = symexFind(tiSum, tLabel("ti_sum"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(tiSum(r.witness[0], r.witness[1]), "ti_sum")
    let d = symexFind(tiSum, tLabel("ti_sum_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an order Nim produces is found; another declines":
    let r = symexFind(tiOrder, tLabel("ti_order_real"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(tiOrder(r.witness[0], r.witness[1]), "ti_order_real")
    let o = symexFind(tiOrder, tLabel("ti_order_other"))
    checkpoint $o.status & " " & show(o.errors)
    check o.status == sxUnknown
    check o.errors.hasKind(feReplayRefuted)
    check o.errors.hasKind(feTableIterOrder)

  test "values, over a string-keyed table":
    let r = symexFind(tiValues, tLabel("ti_values"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
      check reproduces(tiValues(r.witness[0]), "ti_values")

  test "for (k, v) in t.pairs, and for kv in t.pairs":
    ## RFC-0005 batch 7 (S8bp on this pin): the label query multiplies a
    ## key by its value, two symbolic 64-bit terms, and Nim's overflow
    ## checks on that product (`bvsmul_noovfl` / `noudfl`) are a hard
    ## bit-vector search from the query's own text: 120,971,633 units on
    ## Z3 5.1 and 79,811,624 on 4.13.4 in a context of its own, against
    ## 40,490 in the walk's context before S8bp (the same 57 assertions;
    ## without the four overflow checks the text alone takes 632,702).
    ## The path is tainted (`feTableIterOrder`), so its solve runs under
    ## `taintedSolveRLimit`'s 20M: under the defaults it declines
    ## (`beSolverUndef`), never `sxUnsat`; with a budget past the search it
    ## finds Nim's own witness (`a == 6`, replayed natively).
    let d = symexFind(tiTuple, tLabel("ti_tuple"))
    checkpoint "default " & $d.status & " " & show(d.errors)
    check d.status in {sxSat, sxUnknown}
    if d.status == sxUnknown: check d.errors.hasKind(beSolverUndef)
    let r = symexFind(tiTuple, tLabel("ti_tuple"), tupleBudget)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
      check reproduces(tiTuple(r.witness[0]), "ti_tuple")

  test "keys of a string-keyed table, with a break":
    let r = symexFind(tiStrKey, tLabel("ti_strkey"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == "zz"
      check reproduces(tiStrKey(r.witness[0]), "ti_strkey")
    let d = symexFind(tiStrKey, tLabel("ti_strkey_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an input table: the enumeration is all of its keys":
    let d = symexFind(tiParam, tLabel("ti_param_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an empty or one-entry table is exact (no order taint)":
    let d = symexFind(tiOne, tLabel("ti_empty_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(tiOne, tLabel("ti_one"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feTableIterOrder)
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(tiOne(r.witness[0]), "ti_one")

  test "a body that changes the length raises AssertionDefect on that path":
    # RFC-0005 S8bl moved this pin: the iterator's `assert(len(t) == L)` is
    # modelled (an `AssertionDefect`), where S8bc declined the path. The
    # label is reached only without a length change, at `a == 0`.
    let r = symexFind(tiGrow, tLabel("ti_grow"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.anyIt(it.kind == feUnsupportedOp and
                             "length changed" in it.msg)
    if r.status == sxSat:
      check r.witness[0] == 0
      check reproduces(tiGrow(r.witness[0]), "ti_grow")

  test "a float key declines":
    let r = symexFind(tiFloat, tLabel("ti_float"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feUnsupportedOp and "float" in it.msg)

# ---- (3) a seq whose element is a tuple or object ---------------------------
#
# RFC-0005 S8bc: a seq of a tuple, object, array or case object is held
# leaf-split, one `Int -> leaf` array per leaf of the element (as a Table's
# container value is, S8at's `tvTree`). It declined in every position
# (`seNestedSeqUnsupported`). A value object that recurs through a seq is
# unrolled to a bounded depth; a read past it declines
# (`seRecursiveValueDepth`).

type
  LPt = tuple[x: int, y: int]
  LObj = object
    a: int
    s: string
  LHold = object
    ps: seq[LObj]
  LNest = object
    q: seq[int]
    b: bool
  LKind = enum lkA, lkB
  LVar = object
    case k: LKind
    of lkA: i: int
    of lkB: str: string
  LBox = ref object
    ps: seq[LPt]
  RTree = object
    kids: seq[RTree]
    v: int

proc lsTup(s: seq[LPt]) =
  if s.len == 2 and s[1].x == 3 and s[0].y == -2: symexTarget("ls_tup")
  if s.len == 1 and s[0].x != s[0].x: symexTarget("ls_tup_dead")

proc lsObj(s: seq[LObj]) =
  if s.len >= 1 and s[0].a == 7 and s[0].s == "hi": symexTarget("ls_obj")

proc lsField(h: LHold) =
  if h.ps.len == 1 and h.ps[0].a == 3: symexTarget("ls_field")

proc lsAdd(x, y: int) =
  var s: seq[LPt]
  s.add((x, y))
  s.add((y, x))
  if s[1].x == 4 and s[0].x == 9: symexTarget("ls_add")
  if s.len != 2 or s[0].y != y: symexTarget("ls_add_dead")

proc lsAssign(s: seq[LPt], v: int) =
  var t = s
  if t.len < 2: return
  t[0] = (v, v)
  if t[0].x == 11 and t[1].y == s[1].y and t[1].x == 5: symexTarget("ls_assign")
  if t[0].y != v or t[1].x != s[1].x: symexTarget("ls_assign_dead")

proc lsLit(a: int) =
  if a < -1000 or a > 1000: return   # no overflow in the sum
  let s = @[(a, 1), (2, a)]
  var tot = 0
  for p in s: tot += p[0] + p[1]
  if tot == 13: symexTarget("ls_lit")
  if tot != 2 * a + 3: symexTarget("ls_lit_dead")

proc lsNest(s: seq[LNest]) =
  if s.len == 1 and s[0].q.len == 2 and s[0].q[1] == 6 and s[0].b:
    symexTarget("ls_nest")

proc lsOps(x: int) =
  var s = @[(1, 2), (3, 4), (5, 6)]
  s.del(0)               # (5, 6), (3, 4)
  s.insert((x, x), 1)    # (5, 6), (x, x), (3, 4)
  let p = s.pop()        # (3, 4)
  if s.len == 2 and s[1][0] == 8 and s[0][0] == 5 and p[1] == 4:
    symexTarget("ls_ops")
  if s[0][1] != 6: symexTarget("ls_ops_dead")

proc lsBranch(c: bool, x: int) =
  var s = @[(0, 0)]
  if c: s[0] = (x, 1)
  else: s.add((2, x))
  if s.len == 1 and s[0][0] == 3: symexTarget("ls_branch")
  if s.len == 2 and s[1][1] == 6: symexTarget("ls_branch2")
  if s.len == 2 and s[0][0] != 0: symexTarget("ls_branch_dead")

proc lsSlice(s: seq[LPt]) =
  if s.len == 3:
    let t = s[1..2]
    if t[0].x == 4 and t.len == 2: symexTarget("ls_slice")

proc lsLong(n: int) =
  # An element's nested seq built in the body may be longer than an input
  # seq's `1024` bound; the read of the element asserts no such bound.
  if n < 1100 or n > 1200: return
  var s: seq[LNest]
  s.add(LNest(q: newSeq[int](n), b: true))
  if s[0].q.len == 1150 and s[0].b: symexTarget("ls_long")

proc lsMap(a: int) =
  let s = @[(a, 1), (2, 3)]
  let xs = s.map(proc(p: (int, int)): int = p[0] + p[1])
  if xs[0] == 10: symexTarget("ls_map")

proc lsVariant(s: seq[LVar]) =
  if s.len == 1 and s[0].k == lkB and s[0].str == "q": symexTarget("ls_variant")

proc lsTab(t: Table[string, seq[LPt]]) =
  if "a" in t and t["a"].len == 1 and t["a"][0].y == 4: symexTarget("ls_tab")

proc lsHeap(b: LBox) =
  if b != nil and b.ps.len == 1 and b.ps[0].x == 2: symexTarget("ls_heap")

proc rtOne(p: RTree) =
  if p.kids.len == 2 and p.kids[1].v == 3 and p.v == 1: symexTarget("rt_one")

proc rtTwo(p: RTree) =
  if p.kids.len == 1 and p.kids[0].kids.len == 1 and
     p.kids[0].kids[0].v == 4:
    symexTarget("rt_two")

proc rtDeep(p: RTree) =
  if p.kids.len == 1 and p.kids[0].kids.len == 1 and
     p.kids[0].kids[0].kids.len == 1:
    symexTarget("rt_deep")

proc rtBuild(x: int) =
  let leaf = RTree(v: x)
  var root = RTree(v: 0)
  root.kids.add(leaf)
  if root.kids[0].v == 5 and root.kids.len == 1: symexTarget("rt_build")
  if root.kids[0].kids.len != 0: symexTarget("rt_build_dead")

proc rtSelf(x: int) =
  var root = RTree(v: x)
  root.kids.add(root)
  if root.kids[0].v == 5: symexTarget("rt_self")

suite "S8bc (3): a seq of a tuple or object":
  test "a seq[tuple] parameter":
    let r = symexFind(lsTup, tLabel("ls_tup"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(seNestedSeqUnsupported)
    if r.status == sxSat: replays(lsTup(r.witness[0]), "ls_tup")
    let d = symexFind(lsTup, tLabel("ls_tup_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq[object] parameter with a string field":
    let r = symexFind(lsObj, tLabel("ls_obj"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(lsObj(r.witness[0]), "ls_obj")

  test "a seq[object] field":
    let r = symexFind(lsField, tLabel("ls_field"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(lsField(r.witness[0]), "ls_field")

  test "add of a tuple":
    let r = symexFind(lsAdd, tLabel("ls_add"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
      check r.witness[1] == 4
      check reproduces(lsAdd(r.witness[0], r.witness[1]), "ls_add")
    let d = symexFind(lsAdd, tLabel("ls_add_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an element assignment":
    let r = symexFind(lsAssign, tLabel("ls_assign"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 11
      replays(lsAssign(r.witness[0], r.witness[1]), "ls_assign")
    let d = symexFind(lsAssign, tLabel("ls_assign_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq literal of tuples, iterated":
    let r = symexFind(lsLit, tLabel("ls_lit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
      check reproduces(lsLit(r.witness[0]), "ls_lit")
    let d = symexFind(lsLit, tLabel("ls_lit_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an element holding a seq":
    let r = symexFind(lsNest, tLabel("ls_nest"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(lsNest(r.witness[0]), "ls_nest")

  test "del, insert and pop":
    let r = symexFind(lsOps, tLabel("ls_ops"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 8
      check reproduces(lsOps(r.witness[0]), "ls_ops")
    let d = symexFind(lsOps, tLabel("ls_ops_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a merge of two branches":
    let r = symexFind(lsBranch, tLabel("ls_branch"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(lsBranch(r.witness[0], r.witness[1]), "ls_branch")
    let r2 = symexFind(lsBranch, tLabel("ls_branch2"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat:
      check reproduces(lsBranch(r2.witness[0], r2.witness[1]), "ls_branch2")
    let d = symexFind(lsBranch, tLabel("ls_branch_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a slice":
    let r = symexFind(lsSlice, tLabel("ls_slice"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(lsSlice(r.witness[0]), "ls_slice")

  test "an element holding a seq longer than an input seq may be":
    let r = symexFind(lsLong, tLabel("ls_long"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 1150
      check reproduces(lsLong(r.witness[0]), "ls_long")

  test "map over a seq of tuples":
    let r = symexFind(lsMap, tLabel("ls_map"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
      check reproduces(lsMap(r.witness[0]), "ls_map")

  test "a seq of a case object":
    let r = symexFind(lsVariant, tLabel("ls_variant"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(lsVariant(r.witness[0]), "ls_variant")

  test "a Table whose value is a seq of tuples":
    let r = symexFind(lsTab, tLabel("ls_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(lsTab(r.witness[0]), "ls_tab")

  test "a heap cell holding a seq of tuples":
    let r = symexFind(lsHeap, tLabel("ls_heap"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)

suite "S8bc (3): a recursive value object, to a bounded depth":
  test "a child's field":
    let r = symexFind(rtOne, tLabel("rt_one"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(rtOne(r.witness[0]), "rt_one")

  test "a grandchild's field":
    let r = symexFind(rtTwo, tLabel("rt_two"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(rtTwo(r.witness[0]), "rt_two")

  test "a read past the depth bound declines":
    let r = symexFind(rtDeep, tLabel("rt_deep"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(seRecursiveValueDepth)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a tree built in the body":
    let r = symexFind(rtBuild, tLabel("rt_build"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
      check reproduces(rtBuild(r.witness[0]), "rt_build")
    let d = symexFind(rtBuild, tLabel("rt_build_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a value stored one level deeper than its depth declines":
    let r = symexFind(rtSelf, tLabel("rt_self"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      check reproduces(rtSelf(r.witness[0]), "rt_self")
