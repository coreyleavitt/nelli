## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part c: Table iteration, leaf-split seq elements, a recursive value object to a
## bounded depth (items 6, 3).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_c`, `tsymex_rfc0005_s8bc_remainder_c2`,
## `tsymex_rfc0005_s8bc_remainder_c3`. Split so that each part compiles and
## runs in under 60 s on the Windows legs (the whole file took 134 s).
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
