## RFC-0016 INT-74: a slice and an index over a rendering. Magic `Slice`'s
## axis fragment, `let s = ($t & "ab")[0 .. 1]; acc = acc + (s.len +
## ord(s[0]))`, against a value its first byte cannot give (`acc == 13`: the
## first byte is `-` or a digit, so `acc` is 47 or 50..59). Its query is
## unsat, and the sequence solver did not decide it: 15.5M units in 60 s on
## c (`sxUnknown`), at walker 425 and 428; under the pin settings the stall
## backstop ended it at about 619 s, `sxUnknown`.
##
## The walker now restates a fixed-index byte of a rendering, and of a slice
## or a concatenation over one, as a bit-vector formula (`strByteAt`), and
## the length of a slice by SMT-LIB's definition over its base's length
## (`strLenOf`), so the query holds no string. This file proves each
## restatement valid against the sequence theory, per digit band (each
## obligation has a fixed-length rendering), and pins the row exact.
import std/[unittest, times, strutils, options, sequtils, math]
import nelli
import nelli/symex
import z3
import nelli/smt/[types, symval, string_lower_support, runtime_strings, heap_model]
import ./s8cu_helpers

proc bvSortOf(ctx: Z3Context; w: int): auto =
  ctx.checkErr Z3_mk_bv_sort(ctx.raw, cuint(w))

proc bvLit(ctx: Z3Context; text: string; w: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring,
                                                bvSortOf(ctx, w)))

proc bvSV(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool): SymVal =
  if w == 8: SymVal(kind: svBV8, bv8: wrap[Z3BitVec[8]](ctx, v.raw), signed: signed)
  elif w == 16: SymVal(kind: svBV16, bv16: wrap[Z3BitVec[16]](ctx, v.raw), signed: signed)
  elif w == 32: SymVal(kind: svBV32, bv32: wrap[Z3BitVec[32]](ctx, v.raw), signed: signed)
  else: SymVal(kind: svBV64, bv64: wrap[Z3BitVec[64]](ctx, v.raw), signed: signed)

proc renderingOf(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool): Z3String =
  ## The walker's `iekIntToStr` term over `v` (`lowerStrArm`'s arm), registered
  ## as the walker registers it.
  setCurrentContext(ctx)
  var env: Env
  env["v"] = bvSV(ctx, v, w, signed)
  lowerStrArm(env, mkStrOp(iekIntToStr, "$", @[mkVar("v")])).str

const proofRLimit = 50_000_000'u
  ## Z3 `rlimit` units for each proof check, in place of a wall-clock
  ## `timeout` (a wall limit made the verdict depend on the host: a proof
  ## that fit in 120 s alone was `zsUnknown` under load). Source: the
  ## largest check of this file spends 4.56M units (`INT74RULES maxunits`,
  ## Z3 5.1; byte 5 of `substr(concat(x, "ab"), 2, 9)`; the proofs below
  ## are split into cases so that none is larger), and 50M is 11 times
  ## that. The margin is wide because a check's cost is not exactly the
  ## counted units: the `growStale` query counted 17.8M units when decided
  ## and was still cut off under a 20M budget (`tsymex_rfc0005_s8cn_step1d`).

var proofUnits = 0'u
  ## The rlimit units the last `proveUnsat` spent (Z3's `rlimit count` is
  ## the context's running total, so this is the difference).
var proofMaxUnits = 0'u
var proofCtxSeen: pointer
var proofCtxTotal = 0'u

proc proveUnsat(ctx: Z3Context; fs: openArray[Z3Bool]): Z3Status =
  let s = newSolver(ctx)
  let p = newParams(ctx)
  p.set("rlimit", proofRLimit)
  p.set("random_seed", 0'u)
  s.setParams(p)
  for f in fs: s.add f
  result = s.check()
  let st = s.getStatistics()
  var total = 0'u
  if st.contains("rlimit count"):
    total = if st.isInt("rlimit count"): uint(st.getInt("rlimit count"))
            else: uint(st.getFloat("rlimit count"))
  if proofCtxSeen != cast[pointer](ctx.raw):
    proofCtxSeen = cast[pointer](ctx.raw)
    proofCtxTotal = 0
  proofUnits = total - proofCtxTotal
  proofCtxTotal = total
  proofMaxUnits = max(proofMaxUnits, proofUnits)

proc lengthCases(ctx: Z3Context; parts: seq[Z3String]; k: int): seq[seq[Z3Bool]] =
  ## A partition of every assignment to `parts` by where byte `k` of their
  ## concatenation falls: each part's length is each of `0 .. rem` (`rem` the
  ## bytes left before `k`, so the next part starts that many bytes closer),
  ## or more than `rem`, and then `k` is inside that part (the later parts'
  ## lengths do not matter, and the last part is not split). Lengths are
  ## never negative, so the cases cover every model and an UNSAT in each is
  ## an UNSAT of the unsplit query. With no parts there is one case, the
  ## empty assumption.
  if parts.len == 0: return @[newSeq[Z3Bool]()]
  proc rec(ctx: Z3Context; parts: seq[Z3String]; i, rem: int;
           acc: seq[Z3Bool]; into: var seq[seq[Z3Bool]]) =
    if i == parts.high:
      into.add acc
      return
    for a in 0 .. rem:
      rec(ctx, parts, i + 1, rem - a, acc & (len(parts[i]) == mkInt(ctx, a)),
          into)
    into.add acc & (len(parts[i]) > mkInt(ctx, rem))
  rec(ctx, parts, 0, k, @[], result)

proc inBand(ctx: Z3Context; v: Z3AnyAst; signed: bool; lo, hi: string;
            w: int): Z3Bool =
  let a = bvLit(ctx, lo, w)
  let b = bvLit(ctx, hi, w)
  if signed:
    wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvsle(ctx.raw, a.raw, v.raw)) and
      wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvsle(ctx.raw, v.raw, b.raw))
  else:
    wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvule(ctx.raw, a.raw, v.raw)) and
      wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvule(ctx.raw, v.raw, b.raw))

proc bands(w: int; signed: bool): seq[tuple[lo, hi: string, len: int]] =
  ## Every digit band of the width, covering it with no gap: the
  ## non-negative ones, then (signed) the negative ones (one byte longer).
  let maxPos: uint64 =
    if signed: (1'u64 shl (w - 1)) - 1
    elif w == 64: high(uint64) else: (1'u64 shl w) - 1
  var lo = 0'u64
  var k = 1
  while true:
    let top = if k >= 20: high(uint64) else: 10'u64 ^ k - 1
    let hi = min(top, maxPos)
    result.add (lo: $lo, hi: $hi, len: k)
    if hi == maxPos: break
    lo = hi + 1
    inc k
  if signed:
    let maxNeg = 1'u64 shl (w - 1)
    lo = 1
    k = 1
    while true:
      let top = 10'u64 ^ k - 1
      let hi = min(top, maxNeg)
      result.add (lo: "-" & $hi, hi: "-" & $lo, len: k + 1)
      if hi == maxNeg: break
      lo = hi + 1
      inc k

proc walkerRead(s: Z3String; k: int): Z3BitVec[8] =
  ## The walker's own read of `s[k]`: the string term, not the restatement.
  intToBv[8](toCode(at(s, mkInt(s.ctx, k))), Z3BitVec[8])

const kinds = [(8, true), (8, false), (16, true), (16, false),
               (32, true), (32, false), (64, true), (64, false)]

template A(e: untyped): Z3AnyAst {.dirty.} = wrap[Z3AnyAst](ctx, ctx.checkErr e)
template B(e: untyped): Z3Bool {.dirty.} = wrap[Z3Bool](ctx, ctx.checkErr e)

proc fresh(ctx: Z3Context; n: string; w: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw,
    Z3_mk_string_symbol(ctx.raw, n.cstring), bvSortOf(ctx, w)))

proc digitsOf(w: int; signed: bool): int =
  let m = if signed: 1'u64 shl (w - 1)
          elif w == 64: high(uint64) else: (1'u64 shl w) - 1
  len($m)

proc nimBytes(ctx: Z3Context; v: Z3AnyAst; w: int; signed, neg: bool;
              l: int): tuple[fs: seq[Z3Bool], bytes: seq[Z3AnyAst]] =
  ## Nim's `$v` for `v` of sign `neg` with `l` digits, by definition: free
  ## digits (4 bits, at most 9, the leading one nonzero past one digit)
  ## whose decimal value, read from the left, is `|v|`; the bytes are `'-'`
  ## (0x2D) when negative, then `48 + d` per digit.
  const W = 72   # `|low(int64)|` and every 20-digit read fit
  let wide = if signed: A Z3_mk_sign_ext(ctx.raw, cuint(W - w), v.raw)
             else: A Z3_mk_zero_ext(ctx.raw, cuint(W - w), v.raw)
  let zero = bvLit(ctx, "0", W)
  result.fs.add (if neg: B Z3_mk_bvslt(ctx.raw, wide.raw, zero.raw)
                 else: B Z3_mk_bvsge(ctx.raw, wide.raw, zero.raw))
  let m = if neg: A Z3_mk_bvneg(ctx.raw, wide.raw) else: wide
  var read = zero
  if neg: result.bytes.add bvLit(ctx, "45", 8)
  for i in 0 ..< l:
    let d = fresh(ctx, "d" & $i, 4)
    result.fs.add B Z3_mk_bvule(ctx.raw, d.raw, bvLit(ctx, "9", 4).raw)
    if i == 0 and l > 1:
      result.fs.add B Z3_mk_bvuge(ctx.raw, d.raw, bvLit(ctx, "1", 4).raw)
    read = A Z3_mk_bvadd(ctx.raw,
      (A Z3_mk_bvmul(ctx.raw, bvLit(ctx, "10", W).raw, read.raw)).raw,
      (A Z3_mk_zero_ext(ctx.raw, cuint(W - 4), d.raw)).raw)
    result.bytes.add A Z3_mk_bvadd(ctx.raw,
      (A Z3_mk_zero_ext(ctx.raw, 4, d.raw)).raw, bvLit(ctx, "48", 8).raw)
  result.fs.add B Z3_mk_eq(ctx.raw, m.raw, read.raw)

proc numeral(ctx: Z3Context; a: RawZ3Ast): int =
  ## `a`'s value when it is a numeral, else -1.
  var u: uint64
  if not Z3_is_numeral_ast(ctx.raw, a): return -1
  if not Z3_get_numeral_uint64(ctx.raw, a, addr u): return -1
  int(u)

proc eq8(a: Z3BitVec[8]; b: Z3AnyAst): Z3Bool =
  let ctx = a.ctx
  B Z3_mk_eq(ctx.raw, a.raw, b.raw)

suite "INT-74: a rendering's bytes are Nim's (Z3 proves each band)":
  # Over each digit band the rendering has a fixed length `n`; for every
  # index `0 .. n` (the last one past the end, `0xFF`) the restated byte is
  # the byte Nim's `$` gives, by its definition (the decimal digits of
  # `|v|`, `-` first when negative), with `v` free in the band. A bit-vector
  # problem: Z3's sequence solver does not decide `str.at` over
  # `str.from_int` with `v` free (one 8-bit band was open at 120 s), so the
  # walker's string term is tied to the same definition by SMT-LIB
  # (`str.from_int` is the decimal digits, no leading zero) and checked
  # against it by evaluation below. The 32- and 64-bit kinds are not
  # restated (a 32-bit band of seven digits was open at 120 s): their byte
  # stays the walker's `str.at`.
  for (w, signed) in kinds:
    test "width " & $w & (if signed: " signed" else: " unsigned"):
      let ctx = newContext()
      let v = fresh(ctx, "v", w)
      let r = renderingOf(ctx, v, w, signed)
      if w > 16:
        check "str.at" in $strByteAt(r, mkInt(ctx, 0))
        continue
      let t0 = epochTime()
      var worst = 0.0
      let D = digitsOf(w, signed)
      for neg in (if signed: @[false, true] else: @[false]):
        for l in 1 .. D:
          let spec = nimBytes(ctx, v, w, signed, neg, l)
          var right = mkBool(ctx, true)
          for k in 0 .. spec.bytes.len:
            let f = strByteAt(r, mkInt(ctx, k))
            check "str.at" notin $f
            let want = if k < spec.bytes.len: spec.bytes[k]
                       else: bvLit(ctx, "255", 8)
            right = right and eq8(f, want)
          let t1 = epochTime()
          let st = proveUnsat(ctx, spec.fs & @[not right])
          worst = max(worst, epochTime() - t1)
          if st != zsUnsat:
            checkpoint "neg " & $neg & " digits " & $l & ": " & $st
          check st == zsUnsat
      echo "INT74BYTES maxunits ", proofMaxUnits
      echo "INT74BYTES w", w, " ", signed, " ",
        formatFloat(epochTime() - t0, ffDecimal, 2), " s (slowest ",
        formatFloat(worst, ffDecimal, 2), " s)"

  test "the walker's string term agrees, by evaluation":
    # every 8-bit value and the 16/32/64-bit extremes and powers of ten:
    # the restated byte and Z3's own `str.at` of the term, both simplified
    # to numerals
    for (w, signed) in kinds:
      let ctx = newContext()
      let v = fresh(ctx, "v", w)
      let r = renderingOf(ctx, v, w, signed)
      var vals: seq[string]
      if w == 8:
        if signed:
          for x in -128 .. 127: vals.add $x
        else:
          for x in 0 .. 255: vals.add $x
      else:
        let top = if signed: (1'u64 shl (w - 1)) - 1
                  elif w == 64: high(uint64) else: (1'u64 shl w) - 1
        for x in [0'u64, 1, 9, top - 1, top]: vals.add $x
        var p = 10'u64
        while p <= top:
          for x in [p - 1, p, p + 1]:
            if x <= top: vals.add $x
          if p > high(uint64) div 10: break
          p = p * 10
        if signed:
          for x in vals.deduplicate:
            if x != "0": vals.add "-" & x
          vals.add "-" & $(1'u64 shl (w - 1))
      var bad = 0
      for x in vals:
        let c = bvLit(ctx, x, w)
        for k in 0 .. x.len:
          let mine = numeral(ctx, simplify(substitute(strByteAt(r, mkInt(ctx, k)),
                                                      [(v, c)])).raw)
          let theirs = numeral(ctx, simplify(substitute(walkerRead(r, k),
                                                        [(v, c)])).raw)
          let nim = if k < x.len: ord(x[k]) else: 255
          if mine != nim or theirs != nim:
            inc bad
            if bad <= 3: checkpoint $w & " " & x & " byte " & $k & ": " & $mine &
                                    " / " & $theirs
      check bad == 0

suite "INT-74: the slice, concatenation and index rules (Z3 proves them)":
  # Each rule is a sequence identity over free strings, proved by the
  # sequence theory with every part free (no `str.from_int`): the
  # restatement of a part that is not a rendering is the walker's read of it.
  test "`len(str.substr(u, i, n))` for any `u`, `i`, `n`":
    let ctx = newContext()
    let u = mkStringVar(ctx, "u")
    let i = mkIntVar(ctx, "i")
    let n = mkIntVar(ctx, "n")
    check proveUnsat(ctx, [len(substr(u, i, n)) != substrLen(len(u), i, n)]) == zsUnsat

  test "a byte of a concatenation, a slice and an `ite`, at each index":
    let ctx = newContext()
    let x = mkStringVar(ctx, "x")
    let y = mkStringVar(ctx, "y")
    let z = mkStringVar(ctx, "z")
    let c = wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_const(ctx.raw,
      Z3_mk_string_symbol(ctx.raw, "c"), Z3_mk_bool_sort(ctx.raw)))
    let ab = mkString(ctx, "ab")
    var terms = @[concat(x, y), concat(x, concat(y, z)), concat(ab, x),
                  concat(x, ab), ite(c, x, ab)]
    # The free parts of each term, in order: the concatenations over several
    # free strings are proved by cases on those parts' lengths (below).
    var freeParts = @[@[x, y], @[x, y, z], @[], @[], @[]]
    for (i, n) in [(0, 2), (1, 3), (2, 9), (-1, 2), (0, 0), (3, -1)]:
      terms.add substr(concat(x, ab), mkInt(ctx, i), mkInt(ctx, n))
      freeParts.add @[]
    let t0 = epochTime()
    for ti, t in terms:
      for k in 0 .. 5:
        let f = strByteRewrite(t, k)
        let bad = not eq8(f, wrap[Z3AnyAst](ctx, walkerRead(t, k).raw))
        for cs in lengthCases(ctx, freeParts[ti], k):
          let st = proveUnsat(ctx, @[bad] & cs)
          if st != zsUnsat: checkpoint $t & " byte " & $k & ": " & $st
          check st == zsUnsat
    echo "INT74RULES maxunits ", proofMaxUnits
    echo "INT74RULES ", formatFloat(epochTime() - t0, ffDecimal, 2), " s"

  test "a term without a rendering keeps the walker's read":
    let ctx = newContext()
    let s = mkStringVar(ctx, "s")
    let t = concat(s, mkString(ctx, "ab"))
    check "str.at" in $strByteAt(t, mkInt(ctx, 1))
    let i = mkIntVar(ctx, "i")
    let v = fresh(ctx, "v", 8)
    let r = renderingOf(ctx, v, 8, true)
    # a symbolic index is read from the string
    check "str.at" in $strByteAt(r, i)

  test "a 32- or 64-bit rendering's byte is the walker's read (not proved)":
    # The bytes above are proved for the 8- and 16-bit bands only (a 32-bit
    # band past 6 digits was `zsUnknown` at 120 s), so a wider rendering's
    # byte, at a fixed index too, stays the sequence solver's `str.at`; so
    # does an extended 32-bit value, which narrows to its own 32 bits.
    let ctx = newContext()
    for (w, signed) in [(32, true), (32, false), (64, true), (64, false)]:
      let r = renderingOf(ctx, fresh(ctx, "w" & $w & $signed, w), w, signed)
      for k in 0 .. 2:
        let b = $strByteAt(r, mkInt(ctx, k))
        checkpoint $w & " " & $signed & " byte " & $k
        check "str.at" in b
        check "bvudiv" notin b and "bvurem" notin b
    let x = fresh(ctx, "x32", 32)
    let r = renderingOf(ctx, A Z3_mk_sign_ext(ctx.raw, 32, x.raw), 64, true)
    check renderKindOf(r).get.width == 32
    check "str.at" in $strByteAt(r, mkInt(ctx, 0))

suite "INT-74: an extended narrower value renders as its own kind":
  # `int(a)` for an `int8` `a` reaches `$` as `sign_extend(56, a)`, a 64-bit
  # rendering; `registerIntRender` records it as `a`'s own 8-bit kind, so the
  # 8-bit rewrites above apply. Two obligations per case, `x` free:
  #   (R) the recognizer: it narrows exactly a sign extension under a signed
  #       rendering and a zero extension under either (read unsigned), from
  #       8, 16 or 32 bits, through nested extensions; not a truncation, an
  #       arbitrary term, an operation over an extension, an extension from
  #       another width, or a sign extension read unsigned;
  #   (E) the walker's rendering term of the value as given equals the
  #       walker's rendering term of the kind recorded (Z3 proves it for all
  #       `x`), so every rewrite of the recorded kind is a rewrite of the
  #       term the program holds.
  type Case = tuple[name: string, v: Z3AnyAst, w: int, signed: bool,
                    want: tuple[w: int, signed: bool]]

  proc sext(ctx: Z3Context; x: Z3AnyAst; by: int): Z3AnyAst =
    A Z3_mk_sign_ext(ctx.raw, cuint(by), x.raw)
  proc zext(ctx: Z3Context; x: Z3AnyAst; by: int): Z3AnyAst =
    A Z3_mk_zero_ext(ctx.raw, cuint(by), x.raw)

  proc cases(ctx: Z3Context): seq[Case] =
    for (nw, nsigned) in [(8, true), (8, false), (16, true), (16, false),
                          (32, true), (32, false)]:
      let x = fresh(ctx, "x" & $nw & $nsigned, nw)
      for W in [16, 32, 64]:
        if W <= nw: continue
        let e = if nsigned: sext(ctx, x, W - nw) else: zext(ctx, x, W - nw)
        for rs in [true, false]:
          let narrows = (not nsigned) or rs
          result.add (($nw & (if nsigned: " sext " else: " zext ") & $W &
                       (if rs: " signed" else: " unsigned")), e, W, rs,
                      (if narrows: (nw, nsigned) else: (W, rs)))
    let x8 = fresh(ctx, "n8", 8)
    let y = fresh(ctx, "y64", 64)
    let s32 = sext(ctx, x8, 24)
    let trunc = A Z3_mk_extract(ctx.raw, 31, 0, y.raw)
    let four = fresh(ctx, "n4", 4)
    let one = bvLit(ctx, "1", 64)
    result.add @[
      ("zext 64 of sext 32 of 8, signed", zext(ctx, s32, 32), 64, true,
       (32, false)),
      ("sext 64 of sext 32 of 8, signed", sext(ctx, s32, 32), 64, true,
       (8, true)),
      ("sext 64 of sext 32 of 8, unsigned", sext(ctx, s32, 32), 64, false,
       (64, false)),
      ("sext 64 of zext 16 of 8, signed",
       sext(ctx, zext(ctx, x8, 8), 48), 64, true, (8, false)),
      ("a truncation to 32 bits", trunc, 32, true, (32, true)),
      ("sext 64 of a truncation", sext(ctx, trunc, 32), 64, true, (32, true)),
      ("an arbitrary 64-bit term, signed", y, 64, true, (64, true)),
      ("an arbitrary 64-bit term, unsigned", y, 64, false, (64, false)),
      ("the negation of an extension", A Z3_mk_bvneg(ctx.raw,
        sext(ctx, x8, 56).raw), 64, true, (64, true)),
      ("a sum over an extension", A Z3_mk_bvadd(ctx.raw,
        sext(ctx, x8, 56).raw, one.raw), 64, true, (64, true)),
      ("sext 64 of a 4-bit value", sext(ctx, four, 60), 64, true, (64, true))]

  test "(R) and (E) for every case":
    let ctx = newContext()
    let t0 = epochTime()
    for c in cases(ctx):
      let r = renderingOf(ctx, c.v, c.w, c.signed)
      let k = renderKindOf(r)
      checkpoint c.name
      check k.isSome
      if k.isNone: continue
      check (k.get.width, k.get.signed) == c.want
      check int(Z3_get_bv_sort_size(ctx.raw,
        Z3_get_sort(ctx.raw, k.get.v.raw))) == k.get.width
      let rn = renderingOf(ctx, k.get.v, k.get.width, k.get.signed)
      # (E) in two steps. The renderings are `ite(v < 0, "-" ++ from_int(-v),
      # from_int(v))` over `toZ3Int` of each value, so they are equal when
      # those Int terms are. Step 1 proves the Int terms equal for all `x`
      # (a bit-vector and arithmetic query, no string); step 2 asserts that
      # lemma and proves the renderings equal, which is congruence once the
      # two terms are one. Proved this way the sequence solver never has to
      # relate two `from_int` terms through a `bv2int` of each value.
      let lemma = toZ3Int(bvSV(ctx, c.v, c.w, c.signed)) ==
                  toZ3Int(bvSV(ctx, k.get.v, k.get.width, k.get.signed))
      let st1 = proveUnsat(ctx, [not lemma])
      let st = proveUnsat(ctx, [lemma, r != rn])
      if st1 != zsUnsat: checkpoint c.name & ": (E) lemma " & $st1
      check st1 == zsUnsat
      if st != zsUnsat: checkpoint c.name & ": (E) " & $st
      check st == zsUnsat
    echo "INT74NARROW maxunits ", proofMaxUnits
    echo "INT74NARROW ", formatFloat(epochTime() - t0, ffDecimal, 2), " s"

# ---- the row, pinned (K9) ----------------------------------------------------

const int74Budget = 2_000_000
  ## Units per walk; the string lowering spent its whole `queryRLimit`
  ## (15.5M units in 60 s) and did not decide.

proc p74Slice(a, b: int8) =
  ## magic `Slice`'s axis program 35: no input (47 or 50..59)
  let t = int(a)
  var acc = 0
  let s = ($t & "ab")[0 .. 1]
  acc = acc + (s.len + ord(s[0]))
  if acc == 13: symexTarget("hit")

proc p74SliceNeg(a, b: int8) =
  ## `-` first: any negative `t` (2 + 45)
  let t = int(a)
  let s = ($t & "ab")[0 .. 1]
  if s.len + ord(s[0]) == 47: symexTarget("hit")

proc p74SliceDigit(a, b: int8) =
  ## a lone digit then `a`: `t` in 0 .. 9 (the second byte is the literal's)
  let t = int(a)
  let s = ($t & "ab")[0 .. 1]
  if s[1] == 'a' and ord(s[0]) == 57: symexTarget("hit")

proc p74SliceDigitUnsat(a, b: int8) =
  ## a lone digit is never followed by `b`
  let t = int(a)
  let s = ($t & "ab")[0 .. 1]
  if s[1] == 'b': symexTarget("hit")

proc p74Lead(a, b: int8) =
  ## the leading digit of a three-digit magnitude after `-`: every `t` in
  ## -128 .. -100 (four bytes) has `1` there
  let t = int(a)
  let s = $t
  if s.len == 4 and s[1] == '1': symexTarget("hit")

proc p74LeadUnsat(a, b: int8) =
  ## no `int8` has `2` as the leading digit of three
  let t = int(a)
  let s = $t
  if s.len == 3 and s[0] == '2': symexTarget("hit")

suite "INT-74: the row, pinned exact in bounded units":
  template walkUnits(fn: untyped; want: SymexStatusKind) =
    let all = exhaustive(toSeq(low(int8) .. high(int8)))
    symexQueryStats.setLen 0
    let t0 = epochTime()
    let r = pinExact(fn, cellKey(axMagic, "Slice"), tLabel("hit"), all)
    var units = 0
    for q in symexQueryStats: units += q.rlimitDelta
    echo "INT74UNITS ", astToStr(fn), " ", units, " ",
      formatFloat(epochTime() - t0, ffDecimal, 2), " s"
    checkpoint $r.status & " trusted=" & $r.trusted & " units=" & $units
    check r.status == want
    check r.trusted
    check units <= int74Budget

  test "magic Slice: `($t & \"ab\")[0 .. 1]`, `len + ord(s[0]) == 13` (unsat)":
    walkUnits(p74Slice, sxUnsat)
  test "the slice's `-` first (sat)":
    walkUnits(p74SliceNeg, sxSat)
  test "a lone digit then the literal's `a` (sat)":
    walkUnits(p74SliceDigit, sxSat)
  test "a lone digit then `b` (unsat)":
    walkUnits(p74SliceDigitUnsat, sxUnsat)
  test "a leading digit of a rendering (sat)":
    walkUnits(p74Lead, sxSat)
  test "a leading digit no `int8` gives (unsat)":
    walkUnits(p74LeadUnsat, sxUnsat)

suite "INT-74: walker version":
  test "symexWalkerVersion >= 431":
    check parseInt(symexWalkerVersion) >= 431
