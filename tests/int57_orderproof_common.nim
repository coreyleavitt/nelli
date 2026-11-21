## Shared helpers of the INT-57 rendering-order proof (`renderCmp`), split
## across `tsymex_0016_int57_orderproof_*` so each suite finishes well under
## the 900 s per-test limit. The obligations (A) sign/magnitude, (K) padded
## key, (S) reading digits from the left, (B) order over free digits and (C)
## end to end are described in `tsymex_0016_int57_orderproof_small`. Not a
## test (no `t` prefix): the sweep does not run it.
import std/[unittest, times, strutils, options, math]
import nelli
import nelli/symex
import z3
import nelli/smt/[types, symval, string_lower_support, runtime_strings]

type Kind* = tuple[w: int, signed: bool]

const kinds*: array[8, Kind] = [(8, true), (8, false), (16, true), (16, false),
                               (32, true), (32, false), (64, true), (64, false)]

proc bvSortOf*(ctx: Z3Context; w: int): auto =
  ctx.checkErr Z3_mk_bv_sort(ctx.raw, cuint(w))
proc lit*(ctx: Z3Context; text: string; w: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring,
                                                bvSortOf(ctx, w)))
proc fresh*(ctx: Z3Context; n: string; w: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw,
    Z3_mk_string_symbol(ctx.raw, n.cstring), bvSortOf(ctx, w)))
template A*(e: untyped): Z3AnyAst {.dirty.} = wrap[Z3AnyAst](ctx, ctx.checkErr e)
template B*(e: untyped): Z3Bool {.dirty.} = wrap[Z3Bool](ctx, ctx.checkErr e)

proc pow10*(k: int): string = "1" & repeat('0', k)
proc eqB*(ctx: Z3Context; a, b: Z3AnyAst): Z3Bool = B Z3_mk_eq(ctx.raw, a.raw, b.raw)
proc ult*(ctx: Z3Context; a, b: Z3AnyAst): Z3Bool = B Z3_mk_bvult(ctx.raw, a.raw, b.raw)
proc ule*(ctx: Z3Context; a, b: Z3AnyAst): Z3Bool = B Z3_mk_bvule(ctx.raw, a.raw, b.raw)
proc plus*(ctx: Z3Context; a, b: Z3AnyAst): Z3AnyAst = A Z3_mk_bvadd(ctx.raw, a.raw, b.raw)
proc zext*(ctx: Z3Context; x: Z3AnyAst; by: int): Z3AnyAst =
  if by == 0: x else: A Z3_mk_zero_ext(ctx.raw, cuint(by), x.raw)
proc times10*(ctx: Z3Context; x: Z3AnyAst; w: int): Z3AnyAst =
  A Z3_mk_bvmul(ctx.raw, lit(ctx, "10", w).raw, x.raw)
proc scaled*(ctx: Z3Context; x: Z3AnyAst; j, w: int): Z3AnyAst =
  A Z3_mk_bvmul(ctx.raw, lit(ctx, pow10(j), w).raw, x.raw)

proc bvSV*(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool): SymVal =
  if w == 8: SymVal(kind: svBV8, bv8: wrap[Z3BitVec[8]](ctx, v.raw), signed: signed)
  elif w == 16: SymVal(kind: svBV16, bv16: wrap[Z3BitVec[16]](ctx, v.raw), signed: signed)
  elif w == 32: SymVal(kind: svBV32, bv32: wrap[Z3BitVec[32]](ctx, v.raw), signed: signed)
  else: SymVal(kind: svBV64, bv64: wrap[Z3BitVec[64]](ctx, v.raw), signed: signed)

proc renderingOf*(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool): Z3String =
  ## The walker's `iekIntToStr` term over `v` (`lowerStrArm`'s arm), registered
  ## as the walker registers it.
  setCurrentContext(ctx)
  var env: Env
  env["v"] = bvSV(ctx, v, w, signed)
  lowerStrArm(env, mkStrOp(iekIntToStr, "$", @[mkVar("v")])).str

proc digitsOf*(k: Kind): int =
  let m = if k.signed: 1'u64 shl (k.w - 1)
          elif k.w == 64: high(uint64) else: (1'u64 shl k.w) - 1
  len($m)

proc keySizes*(): seq[int] =
  ## Every `L` `renderCmp` uses: the larger digit count of two kinds.
  for k in kinds:
    if digitsOf(k) notin result: result.add digitsOf(k)

proc prove*(ctx: Z3Context; fs: openArray[Z3Bool]): Z3Status =
  let s = newSolver(ctx)
  let p = newParams(ctx)
  # rlimit, not a wall `timeout`: a wall limit made the verdict depend on the
  # host's load. Worst check measured 60,616,685 units (Z3 5.1; s20) and
  # 47,815,794 (Z3 4.13.4, the Windows legs' pin; s20), so budget 650M.
  p.set("rlimit", 650_000_000'u)
  p.set("random_seed", 0'u)
  s.setParams(p)
  for f in fs: s.add f
  s.check()

proc step*(ctx: Z3Context; x, y, p, q: Z3AnyAst; t, w: int): Z3Bool =
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

type Spelled* = object
  fs*: seq[Z3Bool]        ## the digits' range constraints
  digits*: seq[Z3AnyAst]  ## the `L` padded digits, from the left (4 bits)
  reads*: seq[Z3AnyAst]   ## `V(0) .. V(L)`: the first `t` digits as a number
  bytes*: seq[Z3AnyAst]   ## Nim's `$`: `'-'` when negative, then the digits

proc spell*(ctx: Z3Context; tag: string; neg: bool; l, L: int): Spelled =
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

proc nimCmp*(ctx: Z3Context; a, b: seq[Z3AnyAst]): tuple[lt, eq: Z3Bool] =
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

type OrderFn* = proc (ctx: Z3Context; nx: Z3Bool; kx, px: Z3AnyAst; ny: Z3Bool;
                     ky, py: Z3AnyAst; op: IRBinop): Z3Bool {.closure.}

proc bandPair*(ctx: Z3Context; order: OrderFn; L, la, lb: int;
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

proc walkerOrder*(ctx: Z3Context; nx: Z3Bool; kx, px: Z3AnyAst; ny: Z3Bool;
                 ky, py: Z3AnyAst; op: IRBinop): Z3Bool =
  renderOrder(ctx, nx, kx, px, ny, ky, py, op)

proc proveSteps*(L: int) =
  ## Obligation (S) for key size `L`, every step, and the `j`-fold scale.
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

proc proveOrder*(L: int; signs: openArray[(bool, bool)];
                 las: Slice[int] = 1 .. 1000) =
  ## Obligation (B) for key size `L`, every pair of digit counts, over the
  ## given sign pairs. `las` restricts the first operand's digit count (the
  ## default is all of them), so a suite can take one slice of the pairs;
  ## the slices of one `L` and sign set partition its obligations.
  let ctx = newContext()
  let t0 = epochTime()
  var n, bad = 0
  var worst = 0.0
  for la in max(1, las.a) .. min(L, las.b):
    for lb in 1 .. L:
      for (sa, sb) in signs:
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

const
  samePairs* = [(false, false), (true, true)]
  mixedPairs* = [(false, true), (true, false)]
  allPairs* = [(false, false), (true, true), (false, true), (true, false)]
