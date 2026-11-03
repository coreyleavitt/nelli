## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part c: Table iteration, leaf-split seq elements, a recursive value object to a
## bounded depth (items 6, 3).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_c`, `tsymex_rfc0005_s8bc_remainder_c2`,
## `tsymex_rfc0005_s8bc_remainder_c4`. Split so that each part compiles and
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
    # RFC-0005 S8cn: a `keys` variable holds the slot's memory while the body
    # writes the Table, so the loop declines first (`lentLoopDecline`).
    let r = symexFind(tiGrow, tLabel("ti_grow"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feUnsupportedOp and
                         "the memory the body may write" in it.msg)
    check reproduces(tiGrow(0), "ti_grow")

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
