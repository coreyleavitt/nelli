## RFC-0016 INT-79 -- a seq literal written directly as a `for` loop's
## operand was a walker fault.
##
## `for p in items(@[("a", x)])` desugars (the `itSeq` arm of the `for`
## lowering) to an index loop over the operand: `let L = len(s); while i <
## L: let p = s[i]; ...`. The operand was bound to a temporary only when it
## held a call (S8cd); a seq literal holds none, so the literal itself went
## to the index statement, whose container must be a variable or a field
## chain over one (`lowerLeafInExpr` asserts `iekVar`/`iekField`, and met
## `iekSeqLit`): `weInternalWalkerFault`, an internal fault where Nim simply
## iterates. An array literal (`for x in [a, b]`) was fixed by S8bl, which
## binds any array operand that is not a variable or a field once.
##
## The fix: the seq operand that is not a variable or a field chain over one
## is bound to a temporary the way `let s = @[...]` is, once, where the loop
## starts (Nim evaluates `items`' argument once), and the loop reads it.
##
## A literal handed to a user iterator did not fault: the expansion binds
## the formal to a copy (`let s = @[...]`), but the S8cn `lent` check read
## the copied formal as a formal (a caller's pointer may reach its memory)
## and declined the iterator's own `for x in s` whenever the loop body
## wrote anything through a `var` (`result += x`). Nim's expansion makes
## that copy a fresh local (`transf.putArgInto`, paFastAsgn): only the
## iterator's own `addr` reaches it, and the check now reads it so
## (`ParseCtx.copiedIterFormals`).
##
## The suite covers the class: the `items`/`pairs`/bare forms over seq and
## array literals of ints, tuples, objects, strings and nested literals,
## destructured (`for (a, b) in [...]`), and a literal handed to a user
## iterator. Each shape has a `hit` twin native reaches for every `k` and a
## `never` twin it reaches for none, pinned exact against native.
import std/[unittest, strutils, tables]
import nelli
import nelli/symex
import ./s8cu_helpers

type O = object
  a: int
  b: string

iterator evens(s: seq[int]): int =
  for x in s:
    if x mod 2 == 0: yield x
iterator firsts(a: array[2, (int, int)]): int =
  for p in a: yield p[0]

# The reported shape: a seq of (string, int) tuples under `items`.
proc r1(k: int): int =
  for p in items(@[("a", k)]): result += p[1] + p[0].len
# Seq and array literals of ints: bare, `items`, method call.
proc a1(k: int): int =
  for x in @[k, k + 1, 3]: result += x
proc a2(k: int): int =
  for x in items(@[k, 7]): result += x * 2
proc a3(k: int): int =
  for x in @[k, 5].items: result += x
proc a4(k: int): int =
  for x in [k, 2]: result += x
# Tuples, objects, strings.
proc t1(k: int): int =
  for p in @[(k, 2), (3, k)]: result += p[0] * p[1]
proc o1(k: int): int =
  for o in @[O(a: k, b: "q"), O(a: 2, b: "rr")]: result += o.a + o.b.len
proc s1(k: int): int =
  result = k
  for s in @["ab", "c"]:
    if s == "c": result += 10
    else: result += s.len
# Nested literals: a seq of arrays, a seq of nested tuples, a seq of seqs.
proc n1(k: int): int =
  for row in @[[k, 1], [2, 3]]:
    for x in row: result += x
proc n2(k: int): int =
  for q in @[((k, 1), 2)]: result += q[0][0] + q[0][1] * 10 + q[1] * 100
# Destructured, over a seq and an array literal; `pairs`.
proc d1(k: int): int =
  for (a, b) in @[(k, 2), (3, 4)]: result += a + b * 10
proc d2(k: int): int =
  for (a, b) in [(k, 2), (3, 4)]: result += a * b
proc p1(k: int): int =
  for i, x in pairs(@[k, 5]): result += i * 100 + x
proc p2(k: int): int =
  for i, (a, b) in pairs(@[(k, 1), (2, 3)]): result += i * 100 + a + b
# A literal handed to a user iterator.
proc u1(k: int): int =
  for x in evens(@[k, 4, 5]): result += x
proc u2(k: int): int =
  for x in firsts([(k, 1), (3, 4)]): result += x
# A computed actual is the iterator's copy: the body's write to the seq it
# was computed from does not show through it.
proc u3(k: int): int =
  var g = @[k, 2]
  for x in evens(@[g[0], g[1], 4]):
    g[1] = 100
    result += x
# The same copy computed by seq `&` (modelled since INT-80, walker 439;
# it declined `feUnsupportedOp` before, as `let h = g & @[4]` did).
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
pair(eR1, eR1Never, r1(k), k + 1, k + 2)
pair(eA1, eA1Never, a1(k), 2 * k + 4, 2 * k + 3)
pair(eA2, eA2Never, a2(k), 2 * k + 14, 2 * k + 7)
pair(eA3, eA3Never, a3(k), k + 5, k + 6)
pair(eA4, eA4Never, a4(k), k + 2, k + 3)
pair(eT1, eT1Never, t1(k), 5 * k, 5 * k + 1)
pair(eO1, eO1Never, o1(k), k + 5, k + 4)
pair(eS1, eS1Never, s1(k), k + 12, k + 11)
pair(eN1, eN1Never, n1(k), k + 6, k + 4)
# A seq of seqs is a decline of the walker's seq model wherever it is
# built (`let s = @[@[k, 1], @[2]]` too): not a fault.
proc n3(k: int): int =
  for row in @[@[k, 1], @[2]]:
    for x in row: result += x
pair(eN3, eN3Never, n3(k), k + 3, k + 4)
pair(eN2, eN2Never, n2(k), k + 210, k + 201)
pair(eD1, eD1Never, d1(k), k + 63, k + 36)
pair(eD2, eD2Never, d2(k), 2 * k + 12, 2 * k + 13)
pair(eP1, eP1Never, p1(k), k + 105, k + 5)
pair(eP2, eP2Never, p2(k), k + 106, k + 6)

proc eU1(k: int) =
  if k > 50 or k < -50: return
  if u1(k) == 4 + (if k mod 2 == 0: k else: 0): symexTarget("hit")
proc eU1Never(k: int) =
  if k > 50 or k < -50: return
  if u1(k) == 4 + (if k mod 2 == 0: 0 else: k) and k != 0:
    symexTarget("hit")
pair(eU2, eU2Never, u2(k), k + 3, k + 4)
proc eU3(k: int) =
  if k > 50 or k < -50: return
  if u3(k) == 6 + (if k mod 2 == 0: k else: 0): symexTarget("hit")
proc eU3Never(k: int) =
  if k > 50 or k < -50: return
  if u3(k) == 104 + (if k mod 2 == 0: k else: 0): symexTarget("hit")
proc eU4(k: int) =
  if k > 50 or k < -50: return
  if u4(k) == 6 + (if k mod 2 == 0: k else: 0): symexTarget("hit")
proc eU4Never(k: int) =
  if k > 50 or k < -50: return
  if u4(k) == 104 + (if k mod 2 == 0: k else: 0): symexTarget("hit")

# `mgetOrPut` with a computed key (`s8cq_twice11` q10): the key is
# evaluated once, after the receiver and before the default.
var gC: int
proc kf(s: string): string = (gC = gC * 10 + 1; s)
proc df(v: int): int = (gC = gC * 10 + 2; v)
proc mk1(k: int) =
  var t = initTable[string, int]()
  t["a"] = k
  gC = 0
  let v = t.mgetOrPut(kf("a"), 7)
  if v == k and gC == 1 and t.len == 1: symexTarget("hit")
proc mk1Never(k: int) =
  var t = initTable[string, int]()
  t["a"] = k
  gC = 0
  let v = t.mgetOrPut(kf("a"), 7)
  if v != k or gC != 1 or t.len != 1: symexTarget("hit")
proc mk2(k: int) =
  var t = initTable[string, int]()
  t["a"] = 1
  gC = 0
  let v = t.mgetOrPut(kf("b"), k)
  if v == k and t.len == 2 and t["b"] == k and gC == 1: symexTarget("hit")
proc mk2Never(k: int) =
  var t = initTable[string, int]()
  t["a"] = 1
  gC = 0
  let v = t.mgetOrPut(kf("b"), k)
  if v != k or t.len != 2 or t["a"] != 1: symexTarget("hit")
proc mk3(k: int) =
  var t = initTable[string, int]()
  gC = 0
  discard t.mgetOrPut(kf("a"), df(k))
  if gC == 12 and t["a"] == k: symexTarget("hit")
proc mk3Never(k: int) =
  var t = initTable[string, int]()
  gC = 0
  discard t.mgetOrPut(kf("a"), df(k))
  if gC == 21: symexTarget("hit")
proc mk4(k: int) =
  if k > 50 or k < -50: return
  var t = initTable[int, int]()
  t[2 * k] = k
  discard t.mgetOrPut(k + k, 5)
  discard t.mgetOrPut(k + 1, 5)
  if t[2 * k] == k and (k == 1 or t[k + 1] == 5): symexTarget("hit")
proc mk4Never(k: int) =
  if k > 50 or k < -50: return
  var t = initTable[int, int]()
  t[2 * k] = k
  discard t.mgetOrPut(k + k, 5)
  if t[2 * k] == 5 and k != 5: symexTarget("hit")

const idom = sampled([0, 1, 2, 3, 4, 5, -42, 42, -7])
let cell = cellKey(axTypeClass, "seq")
let mgCell = cellKey(axStdlibBody, "tables.mgetOrPut")
template exact(hitP, neverP: untyped) =
  check pinExact(hitP, cell, domain = idom).status == sxSat
  check pinExact(neverP, cell, domain = idom).status == sxUnsat

suite "INT-79":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 439
  test "native truth":
    for e in [eR1, eA1, eA2, eA3, eA4, eT1, eO1, eS1, eN1, eN2, eD1, eD2,
              eP1, eP2, eU1, eU2, eU3, eU4]:
      for k in [-42, -7, 0, 1, 2, 3]:
        check native(e(k)) == "hit"
    for e in [eR1Never, eA1Never, eA2Never, eA3Never, eA4Never, eT1Never,
              eO1Never, eS1Never, eN1Never, eN2Never, eD1Never, eD2Never,
              eP1Never, eP2Never, eU1Never, eU2Never, eU3Never, eU4Never]:
      for k in [-42, -7, 0, 1, 2, 3]:
        check native(e(k)) == "ran"
  test "the reported shape: a seq literal of tuples under `items`":
    exact(eR1, eR1Never)
  test "a seq or array literal of ints, bare, `items`, method call":
    exact(eA1, eA1Never)
    exact(eA2, eA2Never)
    exact(eA3, eA3Never)
    exact(eA4, eA4Never)
  test "a literal of tuples, objects, strings":
    exact(eT1, eT1Never)
    exact(eO1, eO1Never)
    exact(eS1, eS1Never)
  test "nested literals":
    exact(eN1, eN1Never)
    exact(eN2, eN2Never)
    check native(eN3(3)) == "hit"
    pinDecline(eN3, cell, seNestedSeqUnsupported,
               excluding = {weInternalWalkerFault})
  test "destructured, and `pairs`":
    exact(eD1, eD1Never)
    exact(eD2, eD2Never)
    exact(eP1, eP1Never)
    exact(eP2, eP2Never)
  test "a literal handed to a user iterator":
    exact(eU1, eU1Never)
    exact(eU2, eU2Never)
    exact(eU3, eU3Never)
    exact(eU4, eU4Never)
  test "`mgetOrPut` with a computed key, exact against native":
    for e in [mk1, mk2, mk3, mk4]:
      for k in [-42, -7, 0, 1, 2, 3]:
        check native(e(k)) == "hit"
    for e in [mk1Never, mk2Never, mk3Never, mk4Never]:
      for k in [-42, -7, 0, 1, 2, 3]:
        check native(e(k)) == "ran"
    check pinExact(mk1, mgCell, domain = idom).status == sxSat
    check pinExact(mk1Never, mgCell, domain = idom).status == sxUnsat
    check pinExact(mk2, mgCell, domain = idom).status == sxSat
    check pinExact(mk2Never, mgCell, domain = idom).status == sxUnsat
    check pinExact(mk3, mgCell, domain = idom).status == sxSat
    check pinExact(mk3Never, mgCell, domain = idom).status == sxUnsat
    check pinExact(mk4, mgCell, domain = idom).status == sxSat
    check pinExact(mk4Never, mgCell, domain = idom).status == sxUnsat
