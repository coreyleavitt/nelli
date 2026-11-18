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

type Kind = tuple[w: int, signed: bool]

const kinds: array[8, Kind] = [(8, true), (8, false), (16, true), (16, false),
                               (32, true), (32, false), (64, true), (64, false)]

proc bvSortOf(ctx: Z3Context; w: int): auto =
  ctx.checkErr Z3_mk_bv_sort(ctx.raw, cuint(w))
proc lit(ctx: Z3Context; text: string; w: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring,
                                                bvSortOf(ctx, w)))
proc fresh(ctx: Z3Context; n: string; w: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw,
    Z3_mk_string_symbol(ctx.raw, n.cstring), bvSortOf(ctx, w)))
template A(e: untyped): Z3AnyAst {.dirty.} = wrap[Z3AnyAst](ctx, ctx.checkErr e)
template B(e: untyped): Z3Bool {.dirty.} = wrap[Z3Bool](ctx, ctx.checkErr e)

proc pow10(k: int): string = "1" & repeat('0', k)
proc eqB(ctx: Z3Context; a, b: Z3AnyAst): Z3Bool = B Z3_mk_eq(ctx.raw, a.raw, b.raw)
proc ult(ctx: Z3Context; a, b: Z3AnyAst): Z3Bool = B Z3_mk_bvult(ctx.raw, a.raw, b.raw)
proc ule(ctx: Z3Context; a, b: Z3AnyAst): Z3Bool = B Z3_mk_bvule(ctx.raw, a.raw, b.raw)
proc plus(ctx: Z3Context; a, b: Z3AnyAst): Z3AnyAst = A Z3_mk_bvadd(ctx.raw, a.raw, b.raw)
proc zext(ctx: Z3Context; x: Z3AnyAst; by: int): Z3AnyAst =
  if by == 0: x else: A Z3_mk_zero_ext(ctx.raw, cuint(by), x.raw)
proc times10(ctx: Z3Context; x: Z3AnyAst; w: int): Z3AnyAst =
  A Z3_mk_bvmul(ctx.raw, lit(ctx, "10", w).raw, x.raw)
proc scaled(ctx: Z3Context; x: Z3AnyAst; j, w: int): Z3AnyAst =
  A Z3_mk_bvmul(ctx.raw, lit(ctx, pow10(j), w).raw, x.raw)

proc bvSV(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool): SymVal =
  if w == 8: SymVal(kind: svBV8, bv8: wrap[Z3BitVec[8]](ctx, v.raw), signed: signed)
  elif w == 16: SymVal(kind: svBV16, bv16: wrap[Z3BitVec[16]](ctx, v.raw), signed: signed)
  elif w == 32: SymVal(kind: svBV32, bv32: wrap[Z3BitVec[32]](ctx, v.raw), signed: signed)
  else: SymVal(kind: svBV64, bv64: wrap[Z3BitVec[64]](ctx, v.raw), signed: signed)

proc renderingOf(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool): Z3String =
  ## The walker's `iekIntToStr` term over `v` (`lowerIntToStr`), registered
  ## as the walker registers it.
  setCurrentContext(ctx)
  lowerIntToStr(bvSV(ctx, v, w, signed)).str

proc digitsOf(k: Kind): int =
  let m = if k.signed: 1'u64 shl (k.w - 1)
          elif k.w == 64: high(uint64) else: (1'u64 shl k.w) - 1
  len($m)

proc keySizes(): seq[int] =
  ## Every `L` `renderCmp` uses: the larger digit count of two kinds.
  for k in kinds:
    if digitsOf(k) notin result: result.add digitsOf(k)

proc prove(ctx: Z3Context; fs: openArray[Z3Bool]): Z3Status =
  let s = newSolver(ctx)
  let p = newParams(ctx)
  p.set("timeout", 120_000'u)
  s.setParams(p)
  for f in fs: s.add f
  s.check()

proc step(ctx: Z3Context; x, y, p, q: Z3AnyAst; t, w: int): Z3Bool =
  ## Obligation (S) at position `t` in `w` bits, as an implication: the
  ## premises (`x, y < 10^t`; `p, q` 4-bit digits at most 9) give the
  ## conclusions. Proved for free `x, y, p, q`; asserted in (B) per step.
  let nine = lit(ctx, "9", 4)
  let bound = lit(ctx, pow10(t), w)
  let premise = ult(ctx, x, bound) and ult(ctx, y, bound) and
                ule(ctx, p, nine) and ule(ctx, q, nine)
  let X = plus(ctx, times10(ctx, x, w), zext(ctx, p, w - 4))
  let Y = plus(ctx, times10(ctx, y, w), zext(ctx, q, w - 4))
  let next = lit(ctx, pow10(t + 1), w)
  let ltR = ult(ctx, x, y) or (eqB(ctx, x, y) and ult(ctx, p, q))
  let eqR = eqB(ctx, x, y) and eqB(ctx, p, q)
  let concl = ult(ctx, X, next) and ult(ctx, Y, next) and
              (ult(ctx, X, Y) == ltR) and (eqB(ctx, X, Y) == eqR)
  (not premise) or concl

type Spelled = object
  fs: seq[Z3Bool]        ## the digits' range constraints
  digits: seq[Z3AnyAst]  ## the `L` padded digits, from the left (4 bits)
  reads: seq[Z3AnyAst]   ## `V(0) .. V(L)`: the first `t` digits as a number
  bytes: seq[Z3AnyAst]   ## Nim's `$`: `'-'` when negative, then the digits

proc spell(ctx: Z3Context; tag: string; neg: bool; l, L: int): Spelled =
  ## A magnitude of exactly `l` digits (free, the leading one nonzero past
  ## one digit), padded right with zero digits to `L`, read from the left in
  ## `renderKeyWidth(L)` bits; and the bytes Nim renders it as.
  let w = renderKeyWidth(L)
  for i in 0 ..< l:
    let d = fresh(ctx, tag & $i, 4)
    result.digits.add d
    result.fs.add ule(ctx, d, lit(ctx, "9", 4))
  if l > 1:
    result.fs.add ule(ctx, lit(ctx, "1", 4), result.digits[0])
  for i in l ..< L: result.digits.add lit(ctx, "0", 4)
  result.reads.add lit(ctx, "0", w)
  for t in 0 ..< L:
    result.reads.add plus(ctx, times10(ctx, result.reads[t], w),
                          zext(ctx, result.digits[t], w - 4))
  if neg: result.bytes.add lit(ctx, "45", 8)
  for i in 0 ..< l:
    result.bytes.add plus(ctx, zext(ctx, result.digits[i], 4), lit(ctx, "48", 8))

proc nimCmp(ctx: Z3Context; a, b: seq[Z3AnyAst]): tuple[lt, eq: Z3Bool] =
  ## Nim's `cmp` over two byte strings of fixed lengths (`system.cmp`:
  ## `memcmp` over the shorter, then the lengths): the first differing byte
  ## decides, unsigned; a string equal to the other's prefix is the smaller.
  let n = min(a.len, b.len)
  var lt = mkBool(ctx, a.len < b.len)
  var eq = mkBool(ctx, a.len == b.len)
  for i in countdown(n - 1, 0):
    let e = eqB(ctx, a[i], b[i])
    lt = ult(ctx, a[i], b[i]) or (e and lt)
    eq = e and eq
  (lt, eq)

type OrderFn = proc (ctx: Z3Context; nx: Z3Bool; kx, px: Z3AnyAst; ny: Z3Bool;
                     ky, py: Z3AnyAst; op: IRBinop): Z3Bool {.closure.}

proc bandPair(ctx: Z3Context; order: OrderFn; L, la, lb: int;
              sa, sb: bool): Z3Status =
  ## Obligation (B) for one band pair: unsat when `order` is Nim's `cmp`
  ## for every pair of magnitudes of `la` and `lb` digits, signs `sa`, `sb`.
  let w = renderKeyWidth(L)
  let a = spell(ctx, "a", sa, la, L)
  let b = spell(ctx, "b", sb, lb, L)
  var facts = a.fs & b.fs
  for t in 0 ..< L:
    facts.add step(ctx, a.reads[t], b.reads[t], a.digits[t], b.digits[t], t, w)
  let want = nimCmp(ctx, a.bytes, b.bytes)
  let na = mkBool(ctx, sa)
  let nb = mkBool(ctx, sb)
  let pa = lit(ctx, $(L - la), 8)
  let pb = lit(ctx, $(L - lb), 8)
  let lt = order(ctx, na, a.reads[L], pa, nb, b.reads[L], pb, bLt)
  let le = order(ctx, na, a.reads[L], pa, nb, b.reads[L], pb, bLe)
  let eq = order(ctx, na, a.reads[L], pa, nb, b.reads[L], pb, bEq)
  let wrong = (lt != want.lt) or (le != (want.lt or want.eq)) or (eq != want.eq)
  prove(ctx, facts & @[wrong])

proc walkerOrder(ctx: Z3Context; nx: Z3Bool; kx, px: Z3AnyAst; ny: Z3Bool;
                 ky, py: Z3AnyAst; op: IRBinop): Z3Bool =
  renderOrder(ctx, nx, kx, px, ny, ky, py, op)

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

suite "INT-57 (S): reading digits from the left":
  for L in keySizes():
    test "key size " & $L & ", every step":
      let ctx = newContext()
      let w = renderKeyWidth(L)
      let x = fresh(ctx, "x", w)
      let y = fresh(ctx, "y", w)
      let p = fresh(ctx, "p", 4)
      let q = fresh(ctx, "q", 4)
      let t0 = epochTime()
      var worst = 0.0
      for t in 0 ..< L:
        let t1 = epochTime()
        let st = prove(ctx, [not step(ctx, x, y, p, q, t, w)])
        worst = max(worst, epochTime() - t1)
        checkpoint "L=" & $L & " t=" & $t & ": " & $st
        check st == zsUnsat
      # past the last digit the read multiplies by ten: `j` times is
      # `10^j * x`, for every `x`
      var r = x
      for j in 1 .. L:
        r = times10(ctx, r, w)
        check prove(ctx, [not eqB(ctx, r, scaled(ctx, x, j, w))]) == zsUnsat
      echo "INT57STEP L=", L, " ", formatFloat(epochTime() - t0, ffDecimal, 2),
        " s (slowest ", formatFloat(worst, ffDecimal, 2), " s)"

suite "INT-57 (B): the order over two magnitudes is Nim's byte order":
  for L in keySizes():
    test "key size " & $L & ", every pair of digit counts and signs":
      let ctx = newContext()
      let t0 = epochTime()
      var n, bad = 0
      var worst = 0.0
      for la in 1 .. L:
        for lb in 1 .. L:
          for (sa, sb) in [(false, false), (true, true), (false, true),
                           (true, false)]:
            let t1 = epochTime()
            let st = bandPair(ctx, walkerOrder, L, la, lb, sa, sb)
            worst = max(worst, epochTime() - t1)
            inc n
            if st != zsUnsat:
              inc bad
              if bad <= 3:
                checkpoint "L=" & $L & " digits " & $la & "/" & $lb &
                  " neg " & $sa & "/" & $sb & ": " & $st
      echo "INT57ORDER L=", L, " ", n, " obligations ",
        formatFloat(epochTime() - t0, ffDecimal, 1), " s (slowest ",
        formatFloat(worst, ffDecimal, 2), " s)"
      check bad == 0

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
