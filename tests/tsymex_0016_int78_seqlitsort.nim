## RFC-0016 INT-78 -- an `int` component of a seq's tuple element was held
## as a Z3 Int, while the same `int` held by a `seq[int]`, a table's cell or
## a bit-vector local is a 64-bit bit-vector.
##
## A seq whose element is a tuple or an object keeps one data array per
## leaf of the element (S8bc), each leaf built at the sort `heapLeafTerm`
## gives it. Since S8as/S8ax that sort is an Int for a signed `int`
## (`intHeapCell`): the right sort for a `ref int` cell, and the wrong one
## for a seq, whose scalar `int` element is a bit-vector
## (`allocateSeqDataRaw`). A literal's bit-vector component went in through
## `bv2int`, and whatever read it back into the bit-vector world -- a
## `seq[int]`, a table's 64-bit cell, an operand of a bit-vector compare --
## took it out through `int2bv`: the F5 shape, `int2bv(bv2int(x))`, which Z3
## rarely decides in a branch check's cap. `{"a": x}.toTable` (stdlib
## `toTable` walks `for key, val in items(pairs)` since INT-75) is the shape
## that surfaced it: the `s8cq_twice11` q10 target took 98-275 s against
## 5 s at d977c2f2, where the walk still declined on that loop. A seq of
## tuples never reached through `toTable` paid the same, at d977c2f2 too.
##
## The fix: a seq's data array holds an `int` part as the bit-vector of its
## width, the sort a `seq[int]` element has, for every element type (a
## tuple, an object, a nested tuple). One Nim type, one sort in a seq.
##
## The cost bounds are in the walker's own units (the K7 walk-units log),
## not wall time: a walk's units are its Z3 checks' resource counts, the
## same on every host and backend for one Z3. Each bound is anchored to the
## cost of a twin shape the defect never touched -- a `seq[int]` holding the
## same values, or q10 at d977c2f2 -- and its comment records the figures.
import std/[unittest, strutils, tables, os, sets]
import nelli
import nelli/symex
import nelli/smt/runtime
import ./s8cu_helpers

type O = object
  a: int
  b: string

# A tuple literal's component, through a table built by `toTable`.
proc tt(x: int) =
  var t = {"a": x}.toTable
  discard t.mgetOrPut("a", 0)
  if t["a"] == x: symexTarget("hit")
proc ttNever(x: int) =
  var t = {"a": x}.toTable
  discard t.mgetOrPut("a", 0)
  if t["a"] != x: symexTarget("hit")
# A seq-of-tuples literal read back by index into a table's 64-bit cell,
# and its `seq[int]` twin.
proc st(x: int) =
  let s = @[(1, x)]
  var t = initTable[int, int]()
  t[s[0][0]] = s[0][1]
  if t[1] == x: symexTarget("hit")
proc stTwin(x: int) =
  let s = @[1, x]
  var t = initTable[int, int]()
  t[s[0]] = s[1]
  if t[1] == x: symexTarget("hit")
# Two components of a seq-of-tuples literal, one through a `seq[int]`, and
# its `seq[int]` twin.
proc sq(x: int) =
  let s = @[(1, x), (x, 2)]
  var g = @[0]
  g[0] = s[0][1]
  if g[0] != s[1][0]: symexTarget("hit")
proc sqTwin(x: int) =
  let s = @[1, x, x, 2]
  var g = @[0]
  g[0] = s[1]
  if g[0] != s[2]: symexTarget("hit")
# A nested tuple, an object, an `int32` component, an array literal.
proc nt(x: int) =
  let s = @[((1, x), 2)]
  var g = @[0]
  g[0] = s[0][0][1]
  if g[0] != x: symexTarget("hit")
proc ob(x: int) =
  let s = @[O(a: x, b: "q")]
  var g = @[0]
  g[0] = s[0].a
  if g[0] == x and s[0].b == "q": symexTarget("hit")
proc i32(x: int32) =
  let s = @[(1'i32, x)]
  var g = @[0'i32]
  g[0] = s[0][1]
  if g[0] != x: symexTarget("hit")
proc ar(x: int) =
  let s = [(1, x)]
  var g = @[0]
  g[0] = s[0][1]
  if g[0] == x: symexTarget("hit")
# The other direction: a bounded parameter, an Int when the run proves its
# arithmetic free of overflow, stored and read back.
proc rv(x: int) =
  if x < 0 or x > 1000: return
  let s = @[(1, x)]
  if s[0][1] + 1 != x + 1: symexTarget("hit")

# The `s8cq_twice11` q10 target, in its original `toTable` form.
var gN: int
proc key(): string = (inc gN; "a")
proc q10(x: int) =
  gN = 0
  var tb = {"a": x}.toTable
  discard tb.mgetOrPut(key(), 0)
  if gN == 1: symexTarget("q10_once") else: symexTarget("q10_ne")

proc unitsIn(log: string): int =
  ## The units the walks of one `symexFind` spent (the K7 log's lines; the
  ## K10b tail walks, a replay candidate's own check, are not counted).
  if fileExists(log):
    for line in readFile(log).splitLines:
      let f = line.split('\t')
      if f.len >= 2 and f[1] != "k10b-tail": result += parseInt(f[0])
  removeFile(log)

template unitsOf(fn: typed; lbl: string; outSt: var SymexStatusKind): int =
  let log = getTempDir() / ("int78_units_" & $getCurrentProcessId() & ".log")
  removeFile(log)
  putEnv(walkUnitsLogEnv, log)
  try: outSt = symexFind(fn, tLabel(lbl)).status
  finally: delEnv(walkUnitsLogEnv)
  unitsIn(log)

let tCell = cellKey(axTypeClass, "tuple")
const i32dom = sampled([low(int32), -1'i32, 0'i32, 1'i32, 7'i32, high(int32)])

suite "INT-78":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 437
  test "native truth":
    check native(tt(3)) == "hit"
    check native(st(3)) == "hit"
    check native(ob(3)) == "hit"
    check native(ar(3)) == "hit"
    check "q10_once" in nativeHits(q10(3))
    check "q10_ne" notin nativeHits(q10(3))
  test "a tuple literal's int component, exact against native":
    check pinExact(tt, tCell).status == sxSat
    check pinExact(ttNever, tCell).status == sxUnsat
    check pinExact(st, tCell).status == sxSat
    check pinExact(stTwin, tCell).status == sxSat
    check pinExact(sq, tCell).status == sxUnsat
    check pinExact(sqTwin, tCell).status == sxUnsat
  test "a nested tuple, an object, an int32, an array literal":
    check pinExact(nt, tCell).status == sxUnsat
    check pinExact(ob, tCell).status == sxSat
    check pinExact(i32, tCell, domain = i32dom).status == sxUnsat
    check pinExact(ar, tCell).status == sxSat
  test "a bounded parameter stored and read back":
    check pinExact(rv, tCell).status == sxUnsat
  test "a tuple component costs what a seq[int] element costs":
    # Measured (units, c): `st` 296,035 at d977c2f2 and at 081b39c4,
    # 3,198 at walker 437, against its twin's 1,112 -- the component's
    # `int2bv(bv2int(x))` was the cost. `sq` spent 250,007,127 in 491 s at
    # 081b39c4 and ended `sxUnknown` (`beSolverUndef`, native: never hits);
    # 3,870 at walker 437, its twin 4,320. The
    # requirement: the tuple's component costs what the twin's element
    # does, give or take the tuple's second leaf array -- within four times
    # for `st` (2.9 at walker 437, 266 before) and twice for `sq` (0.9).
    var s1, s2: SymexStatusKind
    let a = unitsOf(st, "hit", s1)
    let b = unitsOf(stTwin, "hit", s2)
    checkpoint "st " & $a & " twin " & $b
    check s1 == sxSat and s2 == sxSat
    check a <= 4 * b
    let c = unitsOf(sq, "hit", s1)
    let d = unitsOf(sqTwin, "hit", s2)
    checkpoint "sq " & $c & " twin " & $d
    check s1 == sxUnsat and s2 == sxUnsat
    check c <= 2 * d
  test "q10 in its `toTable` form costs what it cost at d977c2f2":
    # Measured (units, c, the run's walks): 6,067,999 at d977c2f2,
    # where the walk declined at `toTable`'s destructuring loop; 393,184,773
    # (98-214 s) at 081b39c4 (INT-75 walks the loop, and the literal's
    # component crossed Int and bit-vector); 10,068,896 at walker 437, the
    # extra over d977c2f2 being the loop it now walks. `initTable` and `[]=`
    # (the form `s8cq_twice11` was reshaped to): 5,164,352. The requirement
    # is d977c2f2's cost: within three times it.
    var st: SymexStatusKind
    let u = unitsOf(q10, "q10_once", st)
    checkpoint "q10 " & $u
    # Native hits `q10_once`; the table's internals still decline, as in
    # the `initTable` form (`s8cq_twice11`).
    check st == sxUnknown
    check u <= 3 * 6_067_999
