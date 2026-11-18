## RFC-0016 INT-80 -- seq concatenation declined.
##
## `system.&` has three overloads for seqs: `seq & seq`, `seq & T` (append
## an element) and `T & seq` (prepend one). The walker modelled string `&`
## (`iekStrConcat`) and a seq's `add` of one element (`iekSeqAdd`), but no
## seq `&`: every one of them reached the infix arm's catch-all and declined
## `feUnsupportedOp: unsupported infix operator `&``, as did `add` of a seq
## (system's `add(var seq[T], openArray[T])`). INT-79 pinned that decline on
## an iterator's actual computed by `&` (`evens(g & @[4])`).
##
## The model: the result's length is the sum of the operands', and element
## `i` reads the left operand's `i` below its length and the right one's
## `i - len(left)` from there, for every per-part array of a tuple or object
## element, each at its own sort (INT-78: an `int` part is a bit-vector of
## its width). It is an array lambda over the operands' arrays, as a slice
## (`iekSeqSlice`) and a written-back view (`iekSeqSplice`) are: the lambda
## captures the arrays the operands held when `&` ran, so a later write to
## an operand does not show through (Nim's `&` copies), and the queries stay
## quantifier-free.
##
## Each shape has a `hit` twin native reaches for every `k` in its range and
## a `never` twin it reaches for none, pinned exact against native.
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import ./s8cu_helpers

type O = object
  a: int
  b: string

iterator evens(s: seq[int]): int =
  for x in s:
    if x mod 2 == 0: yield x

# `seq & seq`: the boundary indices (last of the left, first of the right).
proc c1(k: int): int =
  let a = @[k, 2]
  let b = @[3, k + 1]
  let h = a & b
  h.len * 1000 + h[1] * 100 + h[2] * 10 + h[3] + h[0]
# `seq & T` and `T & seq`.
proc c2(k: int): int =
  let h = @[1, 2] & k
  h.len * 100 + h[1] * 10 + h[2]
proc c3(k: int): int =
  let h = k & @[5, 6]
  h.len * 100 + h[0] + h[1] * 10
# Chained, left-associative.
proc c4(k: int): int =
  let a = @[k]
  let h = a & @[2] & 3 & a
  h.len * 1000 + h[1] * 100 + h[2] * 10 + h[3]
# Ints of other widths: each part keeps its sort.
proc w1(k: int): int =
  let a: seq[int8] = @[int8(k), 2'i8]
  let h = a & @[3'i8]
  h.len * 100 + int(h[0]) + int(h[2]) * 10
proc w2(k: int): int =
  let a = @[uint16(k + 50)]
  let h = a & uint16(7)
  h.len * 1000 + int(h[0]) + int(h[1]) * 100
proc w3(k: int): int =
  let h = int32(k) & @[4'i32, 5'i32]
  h.len * 100 + int(h[0]) + int(h[2]) * 10
# Tuples and objects (per-part arrays), strings.
proc t1(k: int): int =
  let h = @[(k, "a")] & @[(2, "bc")]
  h.len * 1000 + h[1][1].len * 100 + h[1][0] * 10 + h[0][0] + h[0][1].len
proc o1(k: int): int =
  let h = @[O(a: k, b: "q")] & O(a: 3, b: "rr")
  h.len * 1000 + h[1].b.len * 100 + h[1].a * 10 + h[0].a
proc s1(k: int): int =
  let h = @["ab", "c"] & "xyz"
  result = k + h.len * 1000 + h[1].len * 10 + h[2].len * 100
  if h[2] != "xyz" or h[0] != "ab": result = 0
# Empty operands.
proc e1(k: int): int =
  let e: seq[int] = @[]
  let h = e & @[k]
  let g = @[k] & e
  let z = e & e
  h.len * 1000 + g.len * 100 + z.len * 10 + h[0] + g[0]
# A length the walk does not know: `newSeq[int](n)`, read at `n`.
proc l1(k: int): int =
  if k < 0 or k > 5: return -1
  let a = newSeq[int](k)
  let h = a & @[7, k]
  if h.len == k + 2 and h[k] == 7 and h[k + 1] == k and
     (k == 0 or h[k - 1] == 0): 1 else: 0
# Aliasing: both operands the same seq.
proc a1(k: int): int =
  let g = @[k, 2]
  let h = g & g
  h.len * 1000 + h[1] * 100 + h[2] + h[3] * 10
# Copy semantics: a later write to an operand does not show through the
# result, nor a write to the result through the operand.
proc p1(k: int): int =
  var g = @[k, 2]
  let h = g & @[5]
  g[0] = 100
  g.add 9
  h.len * 1000 + h[0] + h[2] * 10
proc p2(k: int): int =
  let g = @[k, 2]
  var h = g & @[5]
  h[0] = 100
  h[2] = 6
  g.len * 1000 + g[0] + h[2] * 10
# `add` of a seq and `&=` (system's `add(var seq[T], openArray[T])`).
proc d1(k: int): int =
  var g = @[k]
  g.add(@[2, 3])
  g.len * 1000 + g[0] + g[1] * 10 + g[2] * 100
proc d2(k: int): int =
  var g = @[k]
  g &= @[4]
  g.len * 100 + g[0] + g[1] * 10
type Box = object
  s: seq[int]
proc d3(k: int): int =
  var b = Box(s: @[1])
  b.s.add([k, 4])
  b.s &= @[9, k]
  b.s.len * 1000 + b.s[1] + b.s[2] * 10 + b.s[3] * 100
# An expression operand, not bound to a name.
proc x1(k: int): int =
  (@[1] & @[k, 3]).len * 100 + (@[1] & @[k])[1]
# INT-79's u4: an iterator's actual computed by `&`.
proc u4(k: int): int =
  var g = @[k, 2]
  for x in evens(g & @[4]):
    g[1] = 100
    result += x

template pair(name, neverName: untyped; call, hitV, neverV: untyped) =
  proc name(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == hitV: symexTarget("hit")
  proc neverName(k {.inject.}: int) =
    if k > 50 or k < -50: return
    if call == neverV: symexTarget("hit")
pair(eC1, eC1Never, c1(k), 4231 + 2 * k, 4232 + 2 * k)
pair(eC2, eC2Never, c2(k), 320 + k, 321 + k)
pair(eC3, eC3Never, c3(k), 350 + k, 340 + k)
pair(eC4, eC4Never, c4(k), 4230 + k, 4230 + k + 1)
pair(eW1, eW1Never, w1(k), 330 + k, 320 + k)
pair(eW2, eW2Never, w2(k), 2750 + k, 2751 + k)
pair(eW3, eW3Never, w3(k), 350 + k, 340 + k)
pair(eT1, eT1Never, t1(k), 2221 + k, 2211 + k)
pair(eO1, eO1Never, o1(k), 2230 + k, 2130 + k)
pair(eS1, eS1Never, s1(k), 3310 + k, 3320 + k)
pair(eE1, eE1Never, e1(k), 1100 + 2 * k, 1110 + 2 * k)
pair(eL1, eL1Never, l1(k), (if k < 0 or k > 5: -1 else: 1), 0)
pair(eA1, eA1Never, a1(k), 4220 + k, 4221 + k)
pair(eP1, eP1Never, p1(k), 3050 + k, 3150)
pair(eP2, eP2Never, p2(k), 2060 + k, 2160)
pair(eD1, eD1Never, d1(k), 3320 + k, 3330 + k)
pair(eD2, eD2Never, d2(k), 240 + k, 230 + k)
pair(eD3, eD3Never, d3(k), 5940 + k, 5840 + k)
pair(eX1, eX1Never, x1(k), 300 + k, 301 + k)
pair(eU4, eU4Never, u4(k), 6 + (if k mod 2 == 0: k else: 0),
     104 + (if k mod 2 == 0: k else: 0))
# A seq of seqs declines wherever it is built (INT-79's `n3`): by name.
proc n1(k: int): int =
  let h = @[@[k]] & @[@[2, 3]]
  h.len * 100 + h[1].len * 10 + h[0][0]
pair(eN1, eN1Never, n1(k), 220 + k, 221 + k)

# The cost twin of `c1`: the same seq built by a hand-written loop.
proc c1Loop(k: int): int =
  let a = @[k, 2]
  let b = @[3, k + 1]
  var h = a
  for x in b: h.add x
  h.len * 1000 + h[1] * 100 + h[2] * 10 + h[3] + h[0]
pair(eC1Loop, eC1LoopNever, c1Loop(k), 4231 + 2 * k, 4232 + 2 * k)
proc l1Loop(k: int): int =
  if k < 0 or k > 5: return -1
  let a = newSeq[int](k)
  var h = a
  for x in [7, k]: h.add x
  if h.len == k + 2 and h[k] == 7 and h[k + 1] == k and
     (k == 0 or h[k - 1] == 0): 1 else: 0
pair(eL1Loop, eL1LoopNever, l1Loop(k), (if k < 0 or k > 5: -1 else: 1), 0)

proc unitsIn(log: string): int =
  ## The units the walks of one `symexFind` spent (the K7 log's lines; the
  ## K10b tail walks, a replay candidate's own check, are not counted).
  if fileExists(log):
    for line in readFile(log).splitLines:
      let f = line.split('\t')
      if f.len >= 2 and f[1] != "k10b-tail": result += parseInt(f[0])
  removeFile(log)

template unitsOf(fn: typed; outSt: var SymexStatusKind): int =
  let log = getTempDir() / ("int80_units_" & $getCurrentProcessId() & ".log")
  removeFile(log)
  putEnv(walkUnitsLogEnv, log)
  try: outSt = symexFind(fn, tLabel("hit")).status
  finally: delEnv(walkUnitsLogEnv)
  unitsIn(log)

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42, -7])
let cell = cellKey(axTypeClass, "seq")
template exact(hitP, neverP: untyped) =
  check pinExact(hitP, cell, domain = idom).status == sxSat
  check pinExact(neverP, cell, domain = idom).status == sxUnsat

suite "INT-80":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 439
  test "native truth":
    for e in [eC1, eC2, eC3, eC4, eW1, eW2, eW3, eT1, eO1, eS1, eE1, eL1,
              eA1, eP1, eP2, eD1, eD2, eD3, eX1, eU4, eN1, eC1Loop]:
      for k in [-42, -7, 0, 1, 2, 3, 5]:
        check native(e(k)) == "hit"
    for e in [eC1Never, eC2Never, eC3Never, eC4Never, eW1Never, eW2Never,
              eW3Never, eT1Never, eO1Never, eS1Never, eE1Never, eL1Never,
              eA1Never, eP1Never, eP2Never, eD1Never, eD2Never, eD3Never,
              eX1Never,
              eU4Never, eN1Never, eC1LoopNever]:
      for k in [-42, -7, 0, 1, 2, 3, 5, 42]:
        check native(e(k)) == "ran"
  test "`seq & seq`, `seq & T`, `T & seq`, chained":
    exact(eC1, eC1Never)
    exact(eC2, eC2Never)
    exact(eC3, eC3Never)
    exact(eC4, eC4Never)
  test "ints of other widths keep their sort":
    exact(eW1, eW1Never)
    exact(eW2, eW2Never)
    exact(eW3, eW3Never)
  test "tuples, objects, strings":
    exact(eT1, eT1Never)
    exact(eO1, eO1Never)
    exact(eS1, eS1Never)
  test "empty operands, and a length the walk does not know":
    exact(eE1, eE1Never)
    exact(eL1, eL1Never)
  test "aliasing and copy semantics":
    exact(eA1, eA1Never)
    exact(eP1, eP1Never)
    exact(eP2, eP2Never)
  test "`add` of a seq and `&=`":
    exact(eD1, eD1Never)
    exact(eD2, eD2Never)
    exact(eD3, eD3Never)
  test "an unnamed operand":
    exact(eX1, eX1Never)
  test "INT-79's u4: an iterator's actual computed by `&`":
    exact(eU4, eU4Never)
  test "a seq of seqs declines by name, never faults":
    pinDecline(eN1, cell, seNestedSeqUnsupported,
               excluding = {weInternalWalkerFault})
  test "`&` costs what the hand-written loop costs":
    # Measured (units, c, walker 439): `c1` 390,602 against its loop twin's
    # 294,059 (1.3x); `l1`, a length the walk does not know, 77,947 against
    # 84,738 (0.9x). The lambda's `ite` is read where an index meets it; the
    # loop's store chain is read the same way. The requirement: within
    # twice the loop.
    var s1, s2: SymexStatusKind
    let a = unitsOf(eC1, s1)
    let b = unitsOf(eC1Loop, s2)
    check s1 == sxSat
    check s2 == sxSat
    checkpoint "units c1: `&` " & $a & ", loop " & $b
    check a > 0 and b > 0
    check a <= 2 * b
    var s3, s4: SymexStatusKind
    let c = unitsOf(eL1, s3)
    let d = unitsOf(eL1Loop, s4)
    check s3 == sxSat
    check s4 == sxSat
    checkpoint "units l1: `&` " & $c & ", loop " & $d
    check c > 0 and d > 0
    check c <= 2 * d
