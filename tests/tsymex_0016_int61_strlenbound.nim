## RFC-0016 INT-61: the length of a string built from a char beside an
## accumulator's arithmetic. `len($chr(t + 128))` (magic `CharToStr`) and
## `var s = "ab"; s.add chr(t + 128); s.len` (magic `AppendStrCh`) were
## exact but slow (84-114 s on c): the `int` addition's overflow side asks
## whether `str.len(str.from_code(k))` (or the appended string's length)
## leaves the `int` range, and Z3's sequence solver did not refute that in
## 12.4M units. `seqLenBoundFacts` puts each such length's structural
## bound (`str.len(str.from_code(k)) <= 1`, ...) beside the query, and the
## arithmetic refutes the side at once.
##
##   (1) every fact kind is a theorem of Z3's sequence theory: its negation
##       is UNSAT with every argument free, which takes in `str.at` and
##       `str.substr` at negative or out-of-range offsets and
##       `str.from_code` outside the code range (each the empty string);
##   (2) a length with an unbounded part (an input string) gets no fact;
##   (3) the cost: each row walks in at most `int61Budget` rlimit units;
##   (4) the version floor.
import std/[unittest, strutils, sequtils]
import z3
import z3/ffi
import nelli
import nelli/symex
import nelli/smt/runtime
import nelli/smt/admission
import ./s8cu_helpers

# ---- (1) the facts are theorems ----------------------------------------------

suite "INT-61 (1): every fact seqLenBoundFacts asserts is valid":
  setup:
    let ctx {.inject.} = newContext()
    let s {.inject.} = mkStringVar(ctx, "s")
    let i {.inject.} = mkIntVar(ctx, "i")
    let n {.inject.} = mkIntVar(ctx, "n")
    let k {.inject.} = mkIntVar(ctx, "k")
    let b {.inject.} = mkBoolVar(ctx, "b")

  proc lenOf(x: Z3String): Z3Int = x.len

  proc allValid(ctx: Z3Context; facts: seq[Z3Bool]): bool =
    ## Each fact over free variables: valid iff its negation is UNSAT.
    result = true
    for f in facts:
      if querySolver(ctx, [not f], 0).check() != zsUnsat: return false

  template expectFacts(x: Z3String; count: int) {.dirty.} =
    let l = lenOf(x)
    let facts = seqLenBoundFacts(ctx, [l == l])
    checkpoint $facts
    check facts.len == count
    check allValid(ctx, facts)

  test "str.from_code at any code, in range or not":
    expectFacts(fromCode(ctx, k), 1)

  test "str.at at any offset, negative or past the end":
    expectFacts(at(s, i), 1)

  test "a concatenation of bounded parts, a literal among them":
    expectFacts(mkString(ctx, "ab") & fromCode(ctx, k) & at(s, i), 1)

  test "str.substr at any offset and count":
    expectFacts(substr(mkString(ctx, "xyz") & at(s, i), i, n), 1)

  test "ite of bounded arms":
    expectFacts(ite(b, fromCode(ctx, k), mkString(ctx, "xyz")), 1)

  test "nested: a substr of an ite of concatenations":
    expectFacts(substr(ite(b, at(s, k) & at(s, k + mkInt(ctx, 1)),
                           mkString(ctx, "abcd") & fromCode(ctx, i)), i, n), 1)

  test "every bounded length under one root, each with its fact":
    let a = lenOf(fromCode(ctx, k))
    let c = lenOf(mkString(ctx, "ab") & at(s, i))
    let facts = seqLenBoundFacts(ctx, [a + c > mkInt(ctx, 4)])
    check facts.len == 2
    check allValid(ctx, facts)
    # The facts refute the root: the bounds are what the arithmetic uses.
    check querySolver(ctx, @[a + c > mkInt(ctx, 4)] & facts, 0).check() ==
      zsUnsat

# ---- (2) unbounded parts get none ---------------------------------------------

suite "INT-61 (2): a length with an unbounded part gets no fact":
  setup:
    let ctx {.inject.} = newContext()
    let s {.inject.} = mkStringVar(ctx, "s")
    let k {.inject.} = mkIntVar(ctx, "k")

  test "an input string, alone or in a concatenation, or str.from_int":
    for x in [s, mkString(ctx, "ab") & s, fromCode(ctx, k) & s,
              wrap[Z3String](ctx, ctx.checkErr Z3_mk_int_to_str(ctx.raw,
                                                                k.raw))]:
      let l = x.len
      check seqLenBoundFacts(ctx, [l == l]).len == 0

# ---- (3) the cost ------------------------------------------------------------

const int61Budget = 250_000
  ## Each row's walk, bounded at `loopPruneRLimit` (250k units, the pruning
  ## budget: what one undefined side may take before it is asked again
  ## under the query budget, `decideUndefined`). Measured on c at walker
  ## 421: `CharToStr` 34,206 units, `AppendStrCh` 36,423 (about 1 s each);
  ## before the facts the overflow side alone ran 12.4M units to
  ## `zsUnknown` (84-114 s per row), 50 times this bound.

proc i61Chr(a, b: int8) =
  let t = int(a)
  var acc = 0
  acc = acc + len($chr(t + 128))
  if acc == 1: symexTarget("hit")

proc i61App(a, b: int8) =
  let t = int(a)
  var acc = 0
  var s = "ab"
  s.add chr(t + 128)
  acc = acc + s.len
  if acc == 3: symexTarget("hit")

suite "INT-61 (3): each row walks in a bounded number of units":
  template walkUnits(fn: untyped; key: CellKey): untyped =
    # The verdict is pinned (K9): the witness hits natively.
    let all = exhaustive(toSeq(low(int8) .. high(int8)))
    symexQueryStats.setLen 0
    let r = pinExact(fn, key, tLabel("hit"), all)
    var units = 0
    for q in symexQueryStats: units += q.rlimitDelta
    echo "INT61UNITS ", astToStr(fn), " ", units
    checkpoint $r.status & " trusted=" & $r.trusted & " units=" & $units
    check r.status == sxSat
    check r.trusted
    units

  test "len($chr(t + 128)) (CharToStr)":
    let u = walkUnits(i61Chr, cellKey(axMagic, "CharToStr"))
    check u > 0
    check u <= int61Budget

  test "s.add chr(t + 128); s.len (AppendStrCh)":
    let u = walkUnits(i61App, cellKey(axMagic, "AppendStrCh"))
    check u > 0
    check u <= int61Budget

# ---- (4) the version floor ---------------------------------------------------

suite "INT-61 (4)":
  test "symexWalkerVersion >= 421":
    check parseInt(symexWalkerVersion) >= 421
