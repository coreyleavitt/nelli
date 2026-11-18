## RFC-0016 INT-57: the order of two renderings, proved. `renderCmp`
## replaces `$a op $b` (`op` in `==`, `<`, `<=`; `!=`, `>`, `>=` are those
## negated or swapped) by a bit-vector formula, not an over-approximation: if
## it were wrong at any width, both verdicts could be. Z3's sequence theory
## does not decide the claim with both values free (an 8-bit `<` was open at
## 120 s), and neither does a bit-vector restatement over free digits once
## the magnitudes are wide (two 5-digit magnitudes took up to 14 s an
## obligation, 10 digits did not finish): a numeric order against a
## digit-wise one is a carry chain the SAT search re-derives. So the claim is
## cut into obligations, each one Z3 discharges, over fixed-length digits:
##
##   (A) per kind (8/16/32/64, signed and unsigned) and per key size `L` it
##       is compared at: `renderSignMag` is `v`'s sign and `|v|` (exact at
##       `low`, no negation overflow);
##   (K) per `L` and digit count `l`: `renderKey` of a magnitude of `l`
##       digits is `(10^(L-l) * m, L - l)`: the digit string padded right
##       with zeros to `L` digits, as a number, and the pad (the pad by the
##       band, the scale at that pad for every `m`);
##   (S) per `L` and position `t < L`, a step of reading digits from the
##       left: for `x, y < 10^t` and digits `p, q`, `10x + p < 10^(t+1)`,
##       `10x + p < 10y + q` iff `x < y`, or `x = y` and `p < q`, and
##       `10x + p = 10y + q` iff `x = y` and `p = q`; and for every `j <= L`
##       the `j`-fold `10 * (...)` of any `x` is `10^j * x`;
##   (B) per `L`, pair of digit counts `(la, lb)` and pair of signs: with the
##       digits free (4 bits, at most 9, the leading one nonzero past one
##       digit), each key the padded digits read from the left (`V(t+1) =
##       10 V(t) + P(t)`, an instance of (S) asserted per step),
##       `renderOrder` is Nim's `cmp` over the rendered BYTES: `'-'` (0x2D)
##       when negative, then `48 + d` per digit, the first differing byte
##       deciding (unsigned), else the shorter first.
##
## Together: `renderCmp(a, b, op)` is, by its definition, `renderOrder` over
## (A)'s signs and (K)'s keys of `|a|` and `|b|` at `L = max(renderDigits)`.
## `|a|` is the number its decimal digits read to (`V(l)`), and by (S) the
## padded read is `V(L) = 10^(L-l) V(l)`, (K)'s key; so (B) applies to the
## digits of `|a|` and `|b|`, and the formula is Nim's `cmp` of `$a` and
## `$b`. Every instance of (S) asserted in (B) is proved for all values in
## (S), so it adds nothing false. (C) cross-checks `renderCmp` end to end per
## band for the 8-bit kinds. The byte strings are the walker's own term's
## (`"-" ++ str.from_int(-v)`): `tsymex_0016_int74_renderslice` proves each
## byte of the term per band, `tsymex_0016_int57_strlenstall` its length.
## A value extended from a narrower kind (`int(a)`, `a: int8`) is compared
## at its own kind's key size: `tsymex_0016_int74_renderslice` proves the
## walker's term of the extended value is the narrower kind's term.
import std/[unittest, times, strutils, options, math]
import nelli
import nelli/symex
import z3
import nelli/smt/[types, symval, string_lower_support, runtime_strings]

import int57_orderproof_common

suite "INT-57 (A): a rendering's sign and magnitude":
  test "every kind, at every key size it is compared at":
    let ctx = newContext()
    const W = 72
    for k in kinds:
      let v = fresh(ctx, "v" & $k.w & $k.signed, k.w)
      let r = renderingOf(ctx, v, k.w, k.signed)
      check renderDigits(r) == digitsOf(k)
      let wide = if k.signed: A Z3_mk_sign_ext(ctx.raw, cuint(W - k.w), v.raw)
                 else: zext(ctx, v, W - k.w)
      let isNeg = B Z3_mk_bvslt(ctx.raw, wide.raw, lit(ctx, "0", W).raw)
      let absW = A Z3_mk_ite(ctx.raw, isNeg.raw,
                             (A Z3_mk_bvneg(ctx.raw, wide.raw)).raw, wide.raw)
      for L in keySizes():
        if L < digitsOf(k): continue
        let width = renderKeyWidth(L)
        # every magnitude of `L` digits fits the key width
        check pow(10.0, float(L)) < pow(2.0, float(width - 1))
        let sm = renderSignMag(r, width)
        let st = prove(ctx, [(sm.neg != isNeg) or
                             not eqB(ctx, zext(ctx, sm.m, W - width), absW)])
        checkpoint $k & " L=" & $L & ": " & $st
        check st == zsUnsat

suite "INT-57 (K): the padded key of a magnitude":
  # `renderKey(m) = (renderScale(m, renderPad(m)), renderPad(m))` (checked
  # on the terms: Z3 shares structurally equal terms); the pad of a
  # magnitude of `l` digits is `L - l` (a chain of threshold comparisons);
  # and the scale at a fixed pad `j` is `10^j * m` for every `m` (each
  # multiplication's guard folds). One obligation over both, the pad left
  # free, is the multiplier equivalence the SAT search re-derives (10 digits
  # did not finish in 120 s).
  for L in keySizes():
    test "key size " & $L & ", every digit count":
      let ctx = newContext()
      let w = renderKeyWidth(L)
      let m = fresh(ctx, "m", w)
      let k = renderKey(ctx, m, L)
      let pad = renderPad(ctx, m, L)
      check $k.pad == $pad
      check $k.key == $renderScale(ctx, m, pad, L)
      let t0 = epochTime()
      for l in 1 .. L:
        let lo = if l == 1: "0" else: pow10(l - 1)
        let band = ule(ctx, lit(ctx, lo, w), m) and ult(ctx, m, lit(ctx, pow10(l), w))
        let st = prove(ctx, [band, not eqB(ctx, pad, lit(ctx, $(L - l), 8))])
        checkpoint "L=" & $L & " l=" & $l & " pad: " & $st
        check st == zsUnsat
        let sc = renderScale(ctx, m, lit(ctx, $(L - l), 8), L)
        let st2 = prove(ctx, [not eqB(ctx, sc, scaled(ctx, m, L - l, w))])
        checkpoint "L=" & $L & " l=" & $l & " scale: " & $st2
        check st2 == zsUnsat
      echo "INT57KEY L=", L, " ", formatFloat(epochTime() - t0, ffDecimal, 2), " s"

suite "INT-57 (S): reading digits from the left (key sizes 3, 5, 10)":
  # key sizes 19 and 20 are in `tsymex_0016_int57_orderproof_s19` and `tsymex_0016_int57_orderproof_s20`
  for L in [3, 5, 10]:
    test "key size " & $L & ", every step":
      proveSteps(L)

suite "INT-57 (B): the order over two magnitudes is Nim's byte order":
  # key sizes 19 and 20 are in `tsymex_0016_int57_orderproof_b19_same`, `tsymex_0016_int57_orderproof_b19_mixed` and
  # `tsymex_0016_int57_orderproof_b20_*`
  for L in [3, 5, 10]:
    test "key size " & $L & ", every pair of digit counts and signs":
      proveOrder(L, allPairs)

  test "the obligations refute a wrong order":
    # mutation guards: each order below is wrong in some band and (B) finds
    # it there, so (B) is not vacuous
    let ctx = newContext()
    proc noTie(ctx: Z3Context; nx: Z3Bool; kx, px: Z3AnyAst; ny: Z3Bool;
               ky, py: Z3AnyAst; op: IRBinop): Z3Bool =
      # the prefix tie dropped: "1" < "10" is lost
      let lex = if op == bLt: ult(ctx, kx, ky)
                elif op == bLe: ule(ctx, kx, ky)
                else: eqB(ctx, kx, ky)
      ite(nx and not ny, mkBool(ctx, true),
          ite(ny and not nx, mkBool(ctx, false), lex))
    proc unpadded(ctx: Z3Context; nx: Z3Bool; kx, px: Z3AnyAst; ny: Z3Bool;
                  ky, py: Z3AnyAst; op: IRBinop): Z3Bool =
      # the keys read unpadded (the numeric order): "9" > "10" is lost
      let w = renderKeyWidth(3)
      proc unpad(k, p: Z3AnyAst): Z3AnyAst =
        let pw = zext(ctx, p, w - 8)
        var r = k
        for j in 1 .. 2:
          let more = ule(ctx, lit(ctx, $j, w), pw)
          let cut = A Z3_mk_bvudiv(ctx.raw, r.raw, lit(ctx, "10", w).raw)
          r = A Z3_mk_ite(ctx.raw, more.raw, cut.raw, r.raw)
        r
      renderOrder(ctx, nx, unpad(kx, px), px, ny, unpad(ky, py), py, op)
    proc minusLast(ctx: Z3Context; nx: Z3Bool; kx, px: Z3AnyAst; ny: Z3Bool;
                   ky, py: Z3AnyAst; op: IRBinop): Z3Bool =
      # `-` sorted after the digits
      renderOrder(ctx, not nx, kx, px, not ny, ky, py, op)
    check bandPair(ctx, noTie, 3, 1, 2, false, false) == zsSat
    check bandPair(ctx, unpadded, 3, 1, 2, false, false) == zsSat
    check bandPair(ctx, minusLast, 3, 1, 1, true, false) == zsSat
    # the walker's order holds on the same bands
    check bandPair(ctx, walkerOrder, 3, 1, 2, false, false) == zsUnsat
    check bandPair(ctx, walkerOrder, 3, 1, 1, true, false) == zsUnsat

suite "INT-57 (C): renderCmp end to end, per band (8-bit kinds)":
  proc bandsOf(k: Kind): seq[(bool, int)] =
    for l in 1 .. digitsOf(k): result.add (false, l)
    if k.signed:
      for l in 1 .. digitsOf(k): result.add (true, l)

  proc endToEnd(ka, kb: Kind): int =
    ## The band pairs where `renderCmp` over two registered renderings is
    ## not Nim's `cmp` of their bytes (any op).
    let ctx = newContext()
    let a = fresh(ctx, "a", ka.w)
    let b = fresh(ctx, "b", kb.w)
    let ra = renderingOf(ctx, a, ka.w, ka.signed)
    let rb = renderingOf(ctx, b, kb.w, kb.signed)
    var fs: seq[(IRBinop, Z3Bool)]
    for op in [bLt, bLe, bEq, bNe, bGt, bGe]: fs.add (op, renderCmp(ra, rb, op).get)
    const W = 16
    const L = 3
    proc tie(v: Z3AnyAst; k: Kind; s: Spelled; neg: bool; l: int): seq[Z3Bool] =
      ## `v` is the signed number `s` spells
      let wide = if k.signed: A Z3_mk_sign_ext(ctx.raw, cuint(W - k.w), v.raw)
                 else: zext(ctx, v, W - k.w)
      let m = if neg: A Z3_mk_bvneg(ctx.raw, wide.raw) else: wide
      result = s.fs
      result.add (if neg: B Z3_mk_bvslt(ctx.raw, wide.raw, lit(ctx, "0", W).raw)
                  else: B Z3_mk_bvsge(ctx.raw, wide.raw, lit(ctx, "0", W).raw))
      result.add eqB(ctx, m, zext(ctx, s.reads[l], W - renderKeyWidth(L)))
    for (na, la) in bandsOf(ka):
      for (nb, lb) in bandsOf(kb):
        let sa = spell(ctx, "da", na, la, L)
        let sb = spell(ctx, "db", nb, lb, L)
        let c = nimCmp(ctx, sa.bytes, sb.bytes)
        let le = c.lt or c.eq
        var wrong = mkBool(ctx, false)
        for (op, f) in fs:
          let want = case op
            of bLt: c.lt
            of bLe: le
            of bEq: c.eq
            of bNe: not c.eq
            of bGt: not le
            else: not c.lt  # k2: n/a: the six ops above, bGe last
          wrong = wrong or (f != want)
        if prove(ctx, tie(a, ka, sa, na, la) & tie(b, kb, sb, nb, lb) &
                      @[wrong]) != zsUnsat:
          inc result

  for (ka, kb) in [((8, true), (8, true)), ((8, false), (8, false)),
                   ((8, true), (8, false)), ((8, false), (8, true))]:
    test $ka & " against " & $kb:
      check endToEnd(ka, kb) == 0

suite "INT-57: walker version":
  test "symexWalkerVersion >= 431":
    check parseInt(symexWalkerVersion) >= 431
