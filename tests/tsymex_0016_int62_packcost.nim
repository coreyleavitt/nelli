## RFC-0016 INT-62: the solve cost of a program that sums several exact
## rows' values into one accumulator grew far faster than the rows' own
## costs. Six type x memory-op rows, each exact alone in under 1 s, packed
## into one accumulator took 359 s on c. Every query after a `set[char]`
## row's `card` joined the accumulator bit-blasted that 256-bit set again,
## and the overflow side `acc + c1[1] + 2 + card(x2)` leaving the `int`
## range took about 4M units each (two such sides), against 94.6k for the
## set row's whole walk. A query that counts a set's members is now asked
## first with each count a free variable (`cardFreeAbstraction`), beside
## the ranges of the query's `int` views (`bvViewRangeFacts`: `-128 <=
## view(sext(b)) <= 127`, `0 <= view(card(s)) <= 256`, sums of ranged
## terms); its UNSAT is the query's own, in a few thousand units.
##
##   (1) every fact kind is a theorem: its negation is UNSAT with every
##       argument free;
##   (1b) a query that counts a set's members is first asked with each
##       count a fresh variable in its range (`cardFreeAbstraction`), so
##       the packed program's later queries do not bit-blast the set again;
##   (2) a view with no structural range (an input, a sum) gets no fact;
##   (3) the cost: the packed program walks in at most `int62Ratio` times
##       the sum of its rows' own walks, in rlimit units;
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

proc view(x: Z3BitVec[64]): Z3Int =
  ## The signed Int view the walker builds for an `int` (`bvTermToZ3Int`).
  wrap[Z3Int](x.ctx, x.ctx.checkErr Z3_mk_bv2int(x.ctx.raw, x.raw, true))

proc ext(ctx: Z3Context; signed: bool; k: int; y: RawZ3Ast): Z3BitVec[64] =
  wrap[Z3BitVec[64]](ctx, ctx.checkErr(
    if signed: Z3_mk_sign_ext(ctx.raw, cuint(k), y)
    else: Z3_mk_zero_ext(ctx.raw, cuint(k), y)))

proc cardOfFreeSet(ctx: Z3Context; n: int): Z3BitVec[64] =
  ## `card` of a free `n`-bit set, as the walker lowers it (`bsCard`).
  let s = Z3_mk_const(ctx.raw, Z3_mk_string_symbol(ctx.raw, cstring("s" & $n)),
                      Z3_mk_bv_sort(ctx.raw, cuint(n)))
  bsCard(wrap[Z3AnyAst](ctx, ctx.checkErr s), n)

suite "INT-62 (1): every fact bvViewRangeFacts asserts is valid":
  setup:
    let ctx {.inject.} = newContext()
    let b {.inject.} = mkBitVecVar[8](ctx, "b")
    let h {.inject.} = mkBitVecVar[9](ctx, "h")
    let i {.inject.} = mkIntVar(ctx, "i")
    let arr {.inject.} = mkArrayVar[Z3Int, Z3BitVec[64]](ctx, "arr")

  proc allValid(ctx: Z3Context; facts: seq[Z3Bool]): bool =
    ## Each fact over free variables: valid iff its negation is UNSAT.
    result = true
    for f in facts:
      if querySolver(ctx, [not f], 0).check() != zsUnsat: return false

  template expectFacts(x: Z3BitVec[64]; count: int) {.dirty.} =
    let v = view(x)
    let facts = bvViewRangeFacts(ctx, [v == v])
    checkpoint $facts
    check facts.len == count
    check allValid(ctx, facts)

  test "a sign extension of a narrower bit-vector":
    expectFacts(ext(ctx, true, 56, b.raw), 2)

  test "a sign extension of a 32-bit term (bounds past a C int)":
    let q = mkBitVecVar[32](ctx, "q")
    expectFacts(ext(ctx, true, 32, q.raw), 2)

  test "a zero extension of a narrower bit-vector":
    expectFacts(ext(ctx, false, 55, h.raw), 2)

  test "an extension read back out of an array cell it was stored in":
    let cell = wrap[Z3BitVec[64]](ctx, ctx.checkErr Z3_mk_select(ctx.raw,
      ctx.checkErr(Z3_mk_store(ctx.raw, arr.raw, i.raw,
                               ext(ctx, true, 56, b.raw).raw)), i.raw))
    expectFacts(cell, 2)

  test "card of a 256-bit set, and of a 9-bit one":
    for (s, n) in [(cardOfFreeSet(ctx, 256), 256), (cardOfFreeSet(ctx, 9), 9)]:
      let v = view(s)
      let facts = bvViewRangeFacts(ctx, [v == v])
      checkpoint $facts
      check facts.len == 2
      check allValid(ctx, facts)
      # The bound is the set's size, not the count's width.
      check querySolver(ctx, @[v > mkInt(ctx, n)] & facts, 0).check() ==
        zsUnsat

  test "a sum, a difference and an ite of ranged terms, and a numeral":
    let e = ext(ctx, true, 56, b.raw)
    let z = ext(ctx, false, 55, h.raw)
    let k = mkBitVec[64](ctx, -5)
    block: expectFacts(e + z + k, 2)
    block: expectFacts(z - e, 2)
    block: expectFacts(ite(mkBoolVar(ctx, "c"), e, z + z), 2)

  # A sum's or difference's range is a fact only when the operation cannot
  # wrap its width. Each case reaches its width's signed bound exactly (or,
  # at 64 bits, the walker's own bound of 2^62), and each fact is valid
  # there.
  # Every handle is held (`H`): a bare one in a reference-counted context
  # is freed by the next API call.
  type H = Z3AnyAst
  proc h(ctx: Z3Context; r: RawZ3Ast): H = wrap[Z3AnyAst](ctx, ctx.checkErr r)
  proc zx(ctx: Z3Context; tag: string; iw, w: int): H =
    ## A free `iw`-bit term zero-extended to `w` bits.
    let x = h(ctx, Z3_mk_const(ctx.raw, Z3_mk_string_symbol(ctx.raw,
      cstring("zx" & tag & $iw & "_" & $w)), Z3_mk_bv_sort(ctx.raw, cuint(iw))))
    h(ctx, Z3_mk_zero_ext(ctx.raw, cuint(w - iw), x.raw))
  proc sx(ctx: Z3Context; tag: string; iw, w: int): H =
    ## A free `iw`-bit term sign-extended to `w` bits.
    let x = h(ctx, Z3_mk_const(ctx.raw, Z3_mk_string_symbol(ctx.raw,
      cstring("sx" & tag & $iw & "_" & $w)), Z3_mk_bv_sort(ctx.raw, cuint(iw))))
    h(ctx, Z3_mk_sign_ext(ctx.raw, cuint(w - iw), x.raw))
  proc num(ctx: Z3Context; v: string; w: int): H =
    h(ctx, Z3_mk_numeral(ctx.raw, cstring(v), Z3_mk_bv_sort(ctx.raw, cuint(w))))
  proc add(x, y: H): H = h(x.ctx, Z3_mk_bvadd(x.ctx.raw, x.raw, y.raw))
  proc sub(x, y: H): H = h(x.ctx, Z3_mk_bvsub(x.ctx.raw, x.raw, y.raw))
  proc rangeFacts(t: H): seq[Z3Bool] =
    let v = wrap[Z3Int](t.ctx, t.ctx.checkErr Z3_mk_bv2int(t.ctx.raw, t.raw, true))
    bvViewRangeFacts(t.ctx, [v == v])

  test "a sum or difference at the edge of its width, where it cannot wrap":
    for w in [8, 16, 63, 64]:
      let iw = min(w - 2, 61)
      # zext(w-2) + zext(w-2) + 1 tops out at 2^(w-1) - 1, the top.
      let s = add(add(zx(ctx, "a", iw, w), zx(ctx, "b", iw, w)), num(ctx, "1", w))
      # sext(w-1) - (zext(w-2) + 1) bottoms out at -2^(w-1), the bottom.
      let d = sub(sx(ctx, "a", min(w - 1, 62), w),
                  add(zx(ctx, "c", iw, w), num(ctx, "1", w)))
      for t in [s, d]:
        let facts = rangeFacts(t)
        checkpoint "w=" & $w & " " & $facts
        check facts.len == 2
        check allValid(ctx, facts)

  test "a sum that reaches the sign bit of a 63- or 8-bit width has no range":
    # zext(62) + 1 can be 2^62, the sign bit of 63 bits: the sum wraps to
    # -2^62, so `[1, 2^62]` is not a range of its signed view.
    for (iw, w) in [(62, 63), (7, 8)]:
      let facts = rangeFacts(add(zx(ctx, "d", iw, w), num(ctx, "1", w)))
      checkpoint "w=" & $w & " " & $facts
      check allValid(ctx, facts)
      check facts.len == 0

  test "a cell read at another index than it was stored at has no range":
    let j = mkIntVar(ctx, "j")
    let cell = wrap[Z3BitVec[64]](ctx, ctx.checkErr Z3_mk_select(ctx.raw,
      ctx.checkErr(Z3_mk_store(ctx.raw, arr.raw, i.raw,
                               ext(ctx, true, 56, b.raw).raw)), j.raw))
    let v = view(cell)
    check bvViewRangeFacts(ctx, [v == v]).len == 0

  test "a negative numeral at a narrow width, read as signed":
    let facts = rangeFacts(add(sx(ctx, "e", 4, 8), num(ctx, "250", 8)))
    checkpoint $facts   # sx(4) - 6: [-14, 1]
    check facts.len == 2
    check allValid(ctx, facts)

  test "the facts refute an int addition's overflow side":
    let a = view(ext(ctx, true, 56, b.raw))
    let c = view(ext(ctx, false, 55, h.raw))
    let s = a + c + mkInt(ctx, 2)
    let side = s > mkBigInt(ctx, $high(int64))
    let facts = bvViewRangeFacts(ctx, [side])
    check facts.len == 4
    check allValid(ctx, facts)
    check querySolver(ctx, @[side] & facts, 0).check() == zsUnsat

suite "INT-62 (1b): the count-free abstraction":
  test "a count leaves the formula and keeps its range":
    let ctx = newContext()
    let k = cardOfFreeSet(ctx, 256)
    let b = mkBitVecVar[8](ctx, "b")
    let side = view(k) + view(ext(ctx, true, 56, b.raw)) + mkInt(ctx, 2) >
      mkBigInt(ctx, $high(int64))
    let abs = cardFreeAbstraction(ctx, [side])
    check abs.len > 0
    for f in abs: check "bvadd" notin $f   # no adder tree, no set
    # Refuted without the set's bit-blast, in a few thousand units.
    check querySolver(ctx, abs, 20_000'u).check() == zsUnsat

  test "a query that counts no set gets none":
    let ctx = newContext()
    let b = mkBitVecVar[8](ctx, "b")
    let v = view(ext(ctx, true, 56, b.raw))
    check cardFreeAbstraction(ctx, [v == v]).len == 0

# ---- (2) no structural range, no fact ------------------------------------------

suite "INT-62 (2): a view with no structural range gets no fact":
  test "an input, a sum with an input, a product, a full-width extension":
    let ctx = newContext()
    let x = mkBitVecVar[64](ctx, "x")
    let b = mkBitVecVar[8](ctx, "b")
    let w = mkBitVecVar[64](ctx, "w")
    let e = ext(ctx, true, 56, b.raw)
    let full = wrap[Z3BitVec[64]](ctx, ctx.checkErr Z3_mk_sign_ext(ctx.raw, 0,
                                                                  w.raw))
    for t in [x, e + x, e * e, full]:
      let v = view(t)
      check bvViewRangeFacts(ctx, [v == v]).len == 0

  test "a sum that may wrap its width":
    # Two 7-bit values zero-extended to 8 bits sum to at most 254, past
    # `int8`'s 127: the 8-bit `bvadd` may wrap, so its view has no range.
    let ctx = newContext()
    let p = mkBitVecVar[7](ctx, "p")
    let q = mkBitVecVar[7](ctx, "q")
    let s = wrap[Z3BitVec[8]](ctx, ctx.checkErr Z3_mk_bvadd(ctx.raw,
      ctx.checkErr(Z3_mk_zero_ext(ctx.raw, 1, p.raw)),
      ctx.checkErr(Z3_mk_zero_ext(ctx.raw, 1, q.raw))))
    let v = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, s.raw, true))
    check bvViewRangeFacts(ctx, [v == v]).len == 0

# ---- (3) the cost ------------------------------------------------------------

let int62Ratio =
  if z3FullVersion().startsWith("5."): 10 else: 30
  ## The packed program's walk, at most this many times the sum of its rows'
  ## own walks. Measured on c at walker 421 (the rows are fixed): rows
  ## 3,520 + 14,613 + 94,723 + 560 + 14,667 + 531 = 128,614 units; packed
  ## 827,151 (6.4 times), of which the target query, a model search over
  ## all six rows' terms at once, is 713,179 and each of the other 22
  ## queries at most 13k. 10 is that ratio with half again of margin for the
  ## target's search. Before the abstraction the packed walk was 2.35M
  ## with the view ranges in every query, and past 16.5M (128 times) with
  ## neither.
  ## The 4.13.4 row (the Windows legs' pin), 30: Z3 4.13.4 searches the
  ## packed target query harder; measured on the z3-4.13.4 dev image, the
  ## rows sum to 130,108 units and the packed walk is 2,586,033 (19.9
  ## times), and 30 is that ratio with the same half again of margin. The
  ## 5.1 bound is not loosened: the version the test sees selects the row.

import ./int62_rows

suite "INT-62 (3): a packed program walks in a bounded multiple of its rows":
  template walkUnits(fn: untyped; key: CellKey): int =
    # Each verdict is pinned (K9): the witness hits natively.
    let all = exhaustive(toSeq(low(int8) .. high(int8)))
    symexQueryStats.setLen 0
    let r = pinExact(fn, key, tLabel("hit"), all)
    var units = 0
    for q in symexQueryStats: units += q.rlimitDelta
    echo "INT62UNITS ", astToStr(fn), " ", units, " ", r.status,
      " trusted=", r.trusted
    if not r.trusted:
      echo "  errors: ", ($r.errors)[0 ..< min(600, ($r.errors).len)]
      echo "  soundness: ", ($r.soundness)[0 ..< min(600, ($r.soundness).len)]
    check r.status == sxSat
    check r.trusted
    units

  test "six type x memory-op rows in one accumulator":
    var sum = 0
    sum += walkUnits(p0, cellKey(axTypeOp, "letCursor/bool"))
    sum += walkUnits(p1, cellKey(axTypeOp, "letCursor/seq"))
    sum += walkUnits(p2, cellKey(axTypeOp, "letCursor/bitSet"))
    sum += walkUnits(p3, cellKey(axTypeOp, "fieldDefault/array"))
    sum += walkUnits(p4, cellKey(axTypeOp, "fieldDefault/seq"))
    sum += walkUnits(p5, cellKey(axTypeOp, "fieldDefault/variant"))
    let packed = walkUnits(pAll, cellKey(axTypeOp, "letCursor/bitSet"))
    checkpoint "packed=" & $packed & " sum=" & $sum
    check sum > 0
    check packed <= int62Ratio * sum

# ---- (4) the version floor ---------------------------------------------------

suite "INT-62 (4)":
  test "symexWalkerVersion >= 421":
    check parseInt(symexWalkerVersion) >= 421
