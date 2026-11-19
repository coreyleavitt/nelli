## RFC-0016 INT-57 (green at walker 428: renderings lower to bit-vector
## formulas, `strLenOf` / `renderCmp`): an `int` built from `$n` (`iekIntToStr`, Z3
## `str.from_int`) and added to an `int`. The query that asks whether the
## addition overflows (the `OverflowDefect` path) is one on which Z3 stops
## advancing its step counter, so `queryRLimit` never ends it; only the wall
## clock does, and the pin settings (`pinSettingsConst`) turn the wall clock
## off so a loaded machine cannot turn a pin into a decline. Under those
## settings the walk does not terminate (killed at 900 s), which breaks the
## engine's "never hang, always classify" invariant on two modelled exact
## rows: magic `IntToStr` and typeop `letCursor/string`. A string ORDER over
## two such strings (magic `LeStr`) beside a set's `card` stalls the query on
## the target's own path the same way, or ends `incomplete (theory seq)`.
##
## K8b's axis suites found it (INT-56): the typeclass, typeop and magic axis
## programs that pack a `$n` fragment with any arithmetic beside it. Alone,
## `len($t) + t <= 3` is exact in about 9 s; `len($t) + t + 129 <= 3` and
## `acc = acc + len($t)` are not.
##
## This file runs each shape under a 20 s wall-clock bound so it terminates,
## and checks what a fix must give: a trusted, exact verdict, reached in under
## `checkBoundS` seconds, with no query ended by the wall clock, and confirmed
## natively (a sat witness reaches the target when run; an unsat shape over a
## small domain reaches it for no input in the domain). A sat verdict can
## stand beside a stalled query (the witness came from another path), so the
## stall is checked on its own: an error naming it ("Z3 stopped advancing its
## step count", or the seq theory's "incomplete") is the hang the pin settings
## turn into a 900 s kill.
import std/[unittest, times, strutils, options, math, sequtils]
import nelli
import nelli/symex
import z3
import nelli/smt/[types, string_lower_support, runtime, admission]
import ./s8cu_helpers

const checkBoundS = 5.0
  ## Per-check wall bound. RFC-0016 §10 runs exact pins on resource limits
  ## alone (`pinSettingsConst`, no wall clock), so a pinned check must end on
  ## its own, promptly: the engine's "never hang, always classify" invariant,
  ## and §12 item 7's suite wall-time budget. Each shape here decides in well
  ## under a second once the renderings lower to bit-vector formulas; at the
  ## 330 s the string lowering took (or the 900 s kill under the pin
  ## settings) the check is the regression this row closed, and a time over
  ## 5 s is the first sign of it returning.

proc i57LetCursor(a, b: int8) =
  ## typeop `letCursor/string` as K8b generated it (typeop program 6)
  let t = int(a)
  var acc = 0
  var x: string = $t
  let c = x
  acc = acc + c.len
  if acc <= 7: symexTarget("hit")

proc i57Offset(a, b: int8) =
  ## the smallest arithmetic shape: no input reaches the target
  ## (`$(-128)` has four characters, -128 + 4 + 129 = 5)
  let t = int(a)
  if len($t) + t + 129 <= 3: symexTarget("hit")

proc i57Scaled(a, b: int8) =
  ## the typeclass shape (`string` packed with five other rows): `t = 0` hits
  let t = int(a)
  if len($t) + 10 * t <= 3: symexTarget("hit")

type I57E = enum i57e0, i57e1

proc i57Order(a, b: int8) =
  ## the magic shape (program 0 of the magic stream, three of its six rows):
  ## a string order over `$t` and `$u` beside a set's `card`; the query on
  ## the target's own path stalls or ends `incomplete (theory seq)`. `a = b`
  ## hits (the sum is then at most 2)
  let t = int(a)
  let u = int(b)
  var acc = 0
  acc = acc + ord(I57E(t and 1) < I57E(u and 1))
  acc = acc + ord($t <= $u)
  acc = acc + card({a} + {b})
  if acc <= 3: symexTarget("hit")

proc i57Eq(a, b: int8) =
  ## two renderings equal, beside arithmetic: `a = b = 5` hits
  let t = int(a)
  let u = int(b)
  if $t == $u and t + u == 10: symexTarget("hit")

proc i57EqUnsat(a, b: int8) =
  ## equal renderings are equal values
  let t = int(a)
  let u = int(b)
  if $t == $u and t != u: symexTarget("hit")

proc i57Ne(a, b: int8) =
  ## two renderings differ: `$t != $u` with `t - u == 1` hits
  let t = int(a)
  let u = int(b)
  if $t != $u and t - u == 1: symexTarget("hit")

proc i57NeUnsat(a, b: int8) =
  ## equal values render equal
  let t = int(a)
  let u = int(b)
  if $t != $u and t == u: symexTarget("hit")

proc i57Bool(a, b: int8) =
  ## a merged `$bool` beside arithmetic: `t = 4` ("false", 5 + 4) hits
  let t = int(a)
  let s = $(t > 5)
  if len(s) + t == 9: symexTarget("hit")

proc i57BoolUnsat(a, b: int8) =
  ## "true" + 5 needs t = 5, which is not > 5; "false" + 4 is excluded
  let t = int(a)
  let s = $(t > 5)
  if len(s) + t == 9 and t > 0 and t != 4: symexTarget("hit")

proc i57BoolOrder(a, b: int8) =
  ## "true" sorts after "false", so `$(t > 0) < $(u > 0)` needs t <= 0 < u
  let t = int(a)
  let u = int(b)
  if $(t > 0) < $(u > 0) and t + u == 3: symexTarget("hit")

proc i57BoolOrderUnsat(a, b: int8) =
  ## nothing sorts below "true" among "true"/"false" but "false"
  let t = int(a)
  let u = int(b)
  if $(t > 0) < $(u > 0) and t > 0: symexTarget("hit")

proc i57LowLen(a, b: int) =
  ## `$low(int)` is `-9223372036854775808`, 20 characters
  if a < -9223372036854775807 and len($a) != 20: symexTarget("hit")

proc i57HighLen(a, b: int) =
  ## `$high(int)` is `9223372036854775807`, 19 characters
  if a > 9223372036854775806 and len($a) != 19: symexTarget("hit")

proc i57LowOrder(a, b: int) =
  ## `$low(int) < $b` with `b < 0`: past the shared `-`, `b`'s digits must
  ## sort after `9223372036854775808` (`b = -93` does)
  if a == low(int) and b < 0 and $a < $b: symexTarget("hit")

proc i57HighOrderUnsat(a, b: int) =
  ## no rendering of a positive `int` with as many digits as `$high(int)`
  ## sorts after it with a smaller value
  if a == high(int) and b > 0 and $b > $a and b < a and len($b) == 19:
    symexTarget("hit")

proc i57IntOrder(a, b: int) =
  ## the byte order of two free `int` renderings, against the numeric one:
  ## `a = 10, b = 9` hits ("10" < "9")
  if $a < $b and a > b: symexTarget("hit")

proc i57IntOrderUnsat(a, b: int) =
  ## single digits order as their values
  if $a <= $b and b < a and a < 10 and b >= 0: symexTarget("hit")

proc i57U64Len(a, b: uint64) =
  ## `$high(uint64)` is `18446744073709551615`, 20 characters
  if a == high(uint64) and len($a) != 20: symexTarget("hit")

proc i57U64LenSat(a, b: uint64) =
  ## twenty digits: `a >= 10^19`
  if len($a) == 20 and b == 0: symexTarget("hit")

proc i57ConStr(a, b: int8) =
  ## magic `ConStrStr` as the axis stream packs it: `len("ab" & $t)` added
  ## to the accumulator (killed at 900 s alone, INT-56 item 10)
  let t = int(a)
  var acc = 0
  acc = acc + len("ab" & $t)
  if acc <= 3: symexTarget("hit")

proc i57ConStrUnsat(a, b: int8) =
  ## `len("ab" & $t) + t + 131 <= 5` has no input (`$(-128)` gives 6 + 3)
  let t = int(a)
  if len("ab" & $t) + t + 131 <= 5: symexTarget("hit")

proc i57AppendStr(a, b: int8) =
  ## magic `AppendStrStr`: `s.add $t; s.len` added to the accumulator
  let t = int(a)
  var acc = 0
  var s = "ab"
  s.add $t
  acc = acc + s.len
  if acc <= 3: symexTarget("hit")

proc i57ParamLen(s: string): int = s.len

proc i57Param(a, b: int8) =
  ## typeclass `string`: the rendering passed to a routine that reads its
  ## length
  let t = int(a)
  var acc = 0
  acc = acc + i57ParamLen($t)
  if acc + t <= 1: symexTarget("hit")

proc mkBounded(): SymexSettings =
  result = pinSettingsConst
  result.budget.queryTimeoutMs = 20_000
const bounded = mkBounded()

const smallInts = block:
  var v: seq[int8]
  for x in low(int8) .. high(int8): v.add x
  v

template decideRun(f: untyped; want: SymexStatusKind): untyped =
  let t0 = epochTime()
  let r = symexFind(f, tLabel("hit"), bounded)
  let secs = epochTime() - t0
  checkpoint astToStr(f) & ": " & $r.status & " trusted=" & $r.trusted &
    " in " & formatFloat(secs, ffDecimal, 2) & " s; errors " & $r.errors
  echo "INT-57 timing ", astToStr(f), " ", formatFloat(secs, ffDecimal, 2), " s"
  check r.trusted
  check r.status == want
  check secs < checkBoundS
  # the stall itself: under the pin settings this query never returns
  for e in r.errors:
    check "stopped advancing" notin e.msg
    check "incomplete (theory seq)" notin e.msg
  r

template decide(f: untyped; want: SymexStatusKind) =
  ## a sat shape: the witness, run natively, reaches the target
  let r = decideRun(f, want)
  if r.status == sxSat:
    check native(f(r.witness[0], r.witness[1])) == "hit"

template decide(f: untyped; want: SymexStatusKind; domain: untyped) =
  ## an unsat shape: no pair from `domain`, run natively, reaches the target
  let r = decideRun(f, want)
  var hits = 0
  for x in domain:
    for y in domain:
      if native(f(x, y)) == "hit": inc hits
  check hits == 0

suite "INT-57: a string length's overflow query stalls Z3":
  test "typeop letCursor/string: `acc = acc + len($t)` is exact (sat)":
    decide(i57LetCursor, sxSat)
  test "`len($t) + t + 129 <= 3` is exact (unsat)":
    decide(i57Offset, sxUnsat, smallInts)
  test "`len($t) + 10 * t <= 3` is exact (sat)":
    decide(i57Scaled, sxSat)
  test "magic: `ord($t <= $u)` beside `card` and an enum order is exact (sat)":
    decide(i57Order, sxSat)

suite "INT-57: renderings compared, merged `$bool`, int64 extremes":
  test "`$t == $u` beside arithmetic (sat)":
    decide(i57Eq, sxSat)
  test "`$t == $u and t != u` (unsat)":
    decide(i57EqUnsat, sxUnsat, smallInts)
  test "`$t != $u` beside arithmetic (sat)":
    decide(i57Ne, sxSat)
  test "`$t != $u and t == u` (unsat)":
    decide(i57NeUnsat, sxUnsat, smallInts)
  test "`len($(t > 5)) + t == 9` (sat)":
    decide(i57Bool, sxSat)
  test "`len($(t > 5)) + t == 9`, `t = 4` excluded (unsat)":
    decide(i57BoolUnsat, sxUnsat, smallInts)
  test "`$(t > 0) < $(u > 0)` beside arithmetic (sat)":
    decide(i57BoolOrder, sxSat)
  test "`$(t > 0) < $(u > 0) and t > 0` (unsat)":
    decide(i57BoolOrderUnsat, sxUnsat, smallInts)
  test "`len($low(int)) == 20` (unsat)":
    decide(i57LowLen, sxUnsat, [low(int), low(int) + 1, -1, 0, high(int)])
  test "`len($high(int)) == 19` (unsat)":
    decide(i57HighLen, sxUnsat, [low(int), -1, 0, high(int) - 1, high(int)])
  test "`$low(int) < $b` for a negative `b` (sat)":
    decide(i57LowOrder, sxSat)
  test "`$b > $high(int)`, 19 digits, `b < high(int)` (unsat)":
    decide(i57HighOrderUnsat, sxUnsat,
           [1, 999999999999999999, 8999999999999999999, high(int) - 1, high(int)])
  test "`$a < $b and a > b` over two `int`s (sat)":
    decide(i57IntOrder, sxSat)
  test "`$a <= $b and b < a` over single digits (unsat)":
    decide(i57IntOrderUnsat, sxUnsat, [low(int), -1, 0, 1, 5, 9, 10, high(int)])
  test "`len($high(uint64)) == 20` (unsat)":
    decide(i57U64Len, sxUnsat,
           [0'u64, 1, 9999999999999999999'u64, high(uint64) - 1, high(uint64)])
  test "`len($a) == 20` for a `uint64` (sat)":
    decide(i57U64LenSat, sxSat)

suite "INT-57: a concatenation over a rendering (magic ConStrStr, AppendStrStr)":
  test "`acc + len(\"ab\" & $t) <= 3` (sat)":
    decide(i57ConStr, sxSat)
  test "`len(\"ab\" & $t) + t + 131 <= 5` (unsat)":
    decide(i57ConStrUnsat, sxUnsat, smallInts)
  test "`s.add $t; acc + s.len <= 3` (sat)":
    decide(i57AppendStr, sxSat)
  test "typeclass `string`: `len` of a `$t` parameter beside `t` (sat)":
    decide(i57Param, sxSat)

suite "INT-57: a merged `$bool` takes the exact path":
  # The `ite` tree over literals a merged `$b` lowers to is recognised by its
  # declaration kind (`isIteApp`, `Z3_OP_ITE`). Were that test to miss, its
  # length would fall back to `str.len` and its order to the sequence solver:
  # still exact, so no verdict above would move, and only these checks see it.
  test "the length and order of `ite(c, \"true\", \"false\")` are by cases":
    let ctx = newContext()
    let c = mkBoolVar(ctx, "c")
    let t = ite(c, mkString(ctx, "true"), mkString(ctx, "false"))
    check isIteApp(ctx, t.raw)
    check not isIteApp(ctx, mkString(ctx, "true").raw)
    let n = strLenOf(t)
    checkpoint $n
    check "str.len" notin $n
    check "len" notin $n
    check litCmp(t, mkString(ctx, "false"), bLt).isSome
    check litCmp(t, ite(c, mkString(ctx, "a"), mkString(ctx, "b")), bEq).isSome

# ---- the facts the lowering states, proved valid by Z3 ----------------------
#
# `strLenOf` restates `len($v)` as an `ite` chain over `v`'s powers-of-ten
# thresholds. Its facts, piecewise: over each digit band of `v` (`0 .. 9`,
# `10 .. 99`, ..., up to the width's extreme, and the mirrored negative bands,
# one character longer for the `-`), the length is that band's figure. Each
# band is proved twice with `v` free in the band: the rendering's own
# `str.len`, over the walker's encoding of Nim's `$` (`ite(v < 0, "-" ++
# str.from_int(-v), str.from_int(v))`, not Z3's primitive, which gives `""`
# for a negative), is the figure (the sequence theory's answer), and the
# chain is the figure (a bit-vector formula). The bands cover the width's
# whole range (checked here), so the chain is the length for every value.

proc bvSortOf(ctx: Z3Context; w: int): auto =
  ctx.checkErr Z3_mk_bv_sort(ctx.raw, cuint(w))

proc bvLit(ctx: Z3Context; text: string; w: int): Z3AnyAst =
  wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_numeral(ctx.raw, text.cstring,
                                                bvSortOf(ctx, w)))

proc renderingOf(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool): Z3String =
  ## The walker's `iekIntToStr` term over `v` (`runtime_strings.nim`),
  ## registered as the walker registers it.
  let vi = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, v.raw, signed))
  result =
    if signed:
      ite(vi < mkInt(ctx, 0),
          concat(mkString(ctx, "-"), toStr(mkInt(ctx, 0) - vi)), toStr(vi))
    else: toStr(vi)
  registerIntRender(result, v, w, signed)

proc proveUnsat(ctx: Z3Context; fs: openArray[Z3Bool]): Z3Status =
  let s = newSolver(ctx)
  let p = newParams(ctx)
  p.set("timeout", 120_000'u)
  s.setParams(p)
  for f in fs: s.add f
  s.check()

proc inBand(ctx: Z3Context; v: Z3AnyAst; w: int; signed: bool;
            lo, hi: string): Z3Bool =
  ## `lo <= v <= hi`, both numerals of `v`'s width (two's complement text
  ## for a negative bound, Z3 reads `-n`).
  let a = bvLit(ctx, lo, w)
  let b = bvLit(ctx, hi, w)
  if signed:
    wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvsle(ctx.raw, a.raw, v.raw)) and
      wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvsle(ctx.raw, v.raw, b.raw))
  else:
    wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvule(ctx.raw, a.raw, v.raw)) and
      wrap[Z3Bool](ctx, ctx.checkErr Z3_mk_bvule(ctx.raw, v.raw, b.raw))

proc bands(w: int; signed: bool): seq[tuple[lo, hi: string, len: int]] =
  ## Every digit band of the width, in order, covering it with no gap: the
  ## non-negative ones, then (signed) the negative ones.
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
    let maxNeg = 1'u64 shl (w - 1)    # |low|
    lo = 1
    k = 1
    while true:
      let top = 10'u64 ^ k - 1
      let hi = min(top, maxNeg)
      result.add (lo: "-" & $hi, hi: "-" & $lo, len: k + 1)
      if hi == maxNeg: break
      lo = hi + 1
      inc k

suite "INT-57: the digit-count facts are valid (Z3 proves each band)":
  for (w, signed) in [(8, true), (8, false), (16, true), (16, false),
                      (32, true), (32, false), (64, true), (64, false)]:
    test "width " & $w & (if signed: " signed" else: " unsigned"):
      let ctx = newContext()
      let v = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw,
        Z3_mk_string_symbol(ctx.raw, "v"), bvSortOf(ctx, w)))
      let r = renderingOf(ctx, v, w, signed)
      let chain = strLenOf(r)
      check "str.len" notin $chain
      let bs = bands(w, signed)
      # the bands cover the width: the first starts at 0 and the
      # non-negative run ends at the width's top; each band starts one past
      # the last (checked on the numerals' text, wide as uint64)
      check bs[0].lo == "0"
      for b in bs:
        let t0 = epochTime()
        let band = inBand(ctx, v, w, signed, b.lo, b.hi)
        let byChain = proveUnsat(ctx, [band, chain != mkInt(ctx, b.len)])
        let byTheory = proveUnsat(ctx, [band, len(r) != mkInt(ctx, b.len)])
        checkpoint b.lo & " .. " & b.hi & " -> " & $b.len & ": chain " &
          $byChain & ", theory " & $byTheory & " in " &
          formatFloat(epochTime() - t0, ffDecimal, 2) & " s"
        check byChain == zsUnsat
        check byTheory == zsUnsat

suite "INT-57: a concatenation's length is its parts' (Z3 proves it)":
  test "`len(\"ab\" & $t)` and `len(s & $t)` take the chain, exactly":
    let ctx = newContext()
    let v = wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw,
      Z3_mk_string_symbol(ctx.raw, "v"), bvSortOf(ctx, 64)))
    let r = renderingOf(ctx, v, 64, true)
    let s = mkStringVar(ctx, "s")
    for t in [concat(mkString(ctx, "ab"), r), concat(s, r),
              concat(r, concat(s, r))]:
      let l = strLenOf(t)
      checkpoint $l
      # the rendering's part is the chain, a free part keeps `str.len`
      check "str.from_int" notin $l
      # and the restatement is the length: with `v` free, `len(t) != l` is
      # unsat given the chain's own validity above (here per the bands of
      # one width, the 8-bit slice `0 .. 99`, where Z3 answers fast)
      let small = inBand(ctx, v, 64, true, "-99", "99")
      check proveUnsat(ctx, [small, len(t) != l]) == zsUnsat

suite "INT-57: the order of two renderings is Nim's (every 8-bit pair)":
  # `renderCmp` restates `$a op $b` (Nim's byte order) as a bit-vector
  # formula over `a` and `b`. The sequence theory does not decide the
  # restatement's validity with `a` and `b` free (an 8-bit `<` was still
  # open at 120 s: string order over `str.from_int` is the very search this
  # row avoids), so it is checked by evaluation instead: the formula, with
  # both values substituted and simplified, is Nim's `cmp($a, $b)` for EVERY
  # pair at 8 bits, signed and unsigned (each op), and for the boundary
  # values of 16, 32 and 64 bits (each power of ten and its neighbours, the
  # extremes). The lengths above are proved by Z3 for every width.
  proc edges(w: int; signed: bool): seq[string] =
    var s: seq[string]
    let top = if signed: (1'u64 shl (w - 1)) - 1
              elif w == 64: high(uint64) else: (1'u64 shl w) - 1
    for x in [0'u64, 1, 2, top - 1, top]: s.add $x
    var p = 10'u64
    while p <= top:
      for x in [p - 1, p, p + 1]:
        if x <= top: s.add $x
      if p > high(uint64) div 10: break
      p = p * 10
    if signed:
      let n = s
      for x in n:
        if x != "0": s.add "-" & x
      s.add "-" & $(1'u64 shl (w - 1))
    s.deduplicate

  proc evalOrder(w: int; signed: bool; vals: seq[string]): int =
    ## The number of (pair, op) the formula gets wrong.
    let ctx = newContext()
    proc fresh(n: string): Z3AnyAst =
      wrap[Z3AnyAst](ctx, ctx.checkErr Z3_mk_const(ctx.raw,
        Z3_mk_string_symbol(ctx.raw, n.cstring), bvSortOf(ctx, w)))
    let a = fresh("a")
    let b = fresh("b")
    let ra = renderingOf(ctx, a, w, signed)
    let rb = renderingOf(ctx, b, w, signed)
    var fs: seq[(IRBinop, Z3Bool)]
    for op in [bLt, bLe, bEq]:
      let f = renderCmp(ra, rb, op)
      doAssert f.isSome
      fs.add (op, f.get)
    var lits: seq[Z3AnyAst]
    for v in vals: lits.add bvLit(ctx, v, w)
    for i, x in vals:
      for j, y in vals:
        let c = cmp(x, y)  # the decimal text is Nim's `$`
        for (op, f) in fs:
          let want = case op
            of bLt: c < 0
            of bLe: c <= 0
            else: c == 0
          let got = simplify(substitute(f, [(a, lits[i]), (b, lits[j])]))
          let gotS = $got
          if gotS != (if want: "true" else: "false"):
            inc result
            if result <= 3:
              checkpoint "w" & $w & " " & $op & " " & x & " vs " & y &
                ": " & gotS

  for (w, signed) in [(8, true), (8, false)]:
    test "width " & $w & (if signed: " signed" else: " unsigned") &
         ", every pair":
      var vals: seq[string]
      if signed:
        for x in -128 .. 127: vals.add $x
      else:
        for x in 0 .. 255: vals.add $x
      let t0 = epochTime()
      check evalOrder(w, signed, vals) == 0
      echo "INT-57 order eval w", w, " ", signed, " ",
        formatFloat(epochTime() - t0, ffDecimal, 2), " s"

  for (w, signed) in [(16, true), (16, false), (32, true), (32, false),
                      (64, true), (64, false)]:
    test "width " & $w & (if signed: " signed" else: " unsigned") &
         ", the boundary values":
      check evalOrder(w, signed, edges(w, signed)) == 0

# ---- the twelve axis rows, pinned (K9) ---------------------------------------
#
# Each row the axis stream blocked against INT-57, in the shape its fragment
# adds to the accumulator, pinned exact through the K9 helper (`pinExact`:
# the witness hits natively, an unsat shape has no hit over every `int8`
# pair) and walked in a bounded number of units. Before: each was killed at
# 900 s under the pin settings, or ended `sxUnknown` under a 20 s clock.

const int57Budget = 1_000_000
  ## Units per walk. The twelve walk in at most about 375k units (the
  ## packed magic shape above, beside a set's `card`, about 3M); the string
  ## lowering spent its whole `queryRLimit` (250M) or stalled.

type I57O = object
  n: int
  w: string

proc p57IntToStr(a, b: int8) =
  let t = int(a)
  var acc = 0
  acc = acc + len($t)
  if acc + t <= 1: symexTarget("hit")

proc p57LengthStr(a, b: int8) =
  ## no input: `$(-128)` has four characters, -128 + 4 + 129 = 5
  let t = int(a)
  var acc = 0
  acc = acc + len($t)
  if acc + t + 129 <= 3: symexTarget("hit")

proc p57Int64ToStr(a, b: int8) =
  let t = int(a)
  var acc = 0
  acc = acc + len($int64(t))
  if acc + 10 * t <= 3: symexTarget("hit")

proc p57BoolToStr(a, b: int8) =
  let t = int(a)
  let u = int(b)
  var acc = 0
  acc = acc + len($(t > u))
  if acc + t == 9: symexTarget("hit")

proc p57EqStr(a, b: int8) =
  let t = int(a)
  let u = int(b)
  var acc = 0
  acc = acc + ord($t == $u)
  if acc + t == 4: symexTarget("hit")

proc p57LeStr(a, b: int8) =
  let t = int(a)
  let u = int(b)
  var acc = 0
  acc = acc + ord($t <= $u)
  if acc + t <= -127: symexTarget("hit")

proc p57LtStr(a, b: int8) =
  let t = int(a)
  let u = int(b)
  var acc = 0
  acc = acc + ord($t < $u)
  if acc + t <= -127: symexTarget("hit")

proc p57ConStrStr(a, b: int8) =
  let t = int(a)
  var acc = 0
  acc = acc + len("ab" & $t)
  if acc + t <= 3: symexTarget("hit")

proc p57AppendStrStr(a, b: int8) =
  let t = int(a)
  var acc = 0
  var s = "ab"
  s.add $t
  acc = acc + s.len
  if acc + t <= 3: symexTarget("hit")

proc p57FieldDefault(a, b: int8) =
  let t = int(a)
  var acc = 0
  let o = I57O(n: t)
  acc = acc + o.n + o.w.len
  if acc <= -100: symexTarget("hit")

suite "INT-57: the twelve axis rows, pinned exact in bounded units":
  template walkUnits(fn: untyped; key: CellKey; want: SymexStatusKind) =
    let all = exhaustive(toSeq(low(int8) .. high(int8)))
    symexQueryStats.setLen 0
    let t0 = epochTime()
    let r = pinExact(fn, key, tLabel("hit"), all)
    var units = 0
    for q in symexQueryStats: units += q.rlimitDelta
    echo "INT57UNITS ", astToStr(fn), " ", units, " ",
      formatFloat(epochTime() - t0, ffDecimal, 2), " s"
    checkpoint $r.status & " trusted=" & $r.trusted & " units=" & $units
    check r.status == want
    check r.trusted
    check units <= int57Budget

  test "magic IntToStr: `acc + len($t) + t <= 1` (sat)":
    walkUnits(p57IntToStr, cellKey(axMagic, "IntToStr"), sxSat)
  test "magic LengthStr: `len($t) + t + 129 <= 3` (unsat)":
    walkUnits(p57LengthStr, cellKey(axMagic, "LengthStr"), sxUnsat)
  test "magic Int64ToStr: `len($int64(t)) + 10 * t <= 3` (sat)":
    walkUnits(p57Int64ToStr, cellKey(axMagic, "Int64ToStr"), sxSat)
  test "magic BoolToStr: `len($(t > u)) + t == 9` (sat)":
    walkUnits(p57BoolToStr, cellKey(axMagic, "BoolToStr"), sxSat)
  test "magic EqStr: `ord($t == $u) + t == 4` (sat)":
    walkUnits(p57EqStr, cellKey(axMagic, "EqStr"), sxSat)
  test "magic LeStr: `ord($t <= $u) + t <= -127` (sat)":
    walkUnits(p57LeStr, cellKey(axMagic, "LeStr"), sxSat)
  test "magic LtStr: `ord($t < $u) + t <= -127` (sat)":
    walkUnits(p57LtStr, cellKey(axMagic, "LtStr"), sxSat)
  test "magic ConStrStr: `len(\"ab\" & $t) + t <= 3` (sat)":
    walkUnits(p57ConStrStr, cellKey(axMagic, "ConStrStr"), sxSat)
  test "magic AppendStrStr: `s.add $t; s.len + t <= 3` (sat)":
    walkUnits(p57AppendStrStr, cellKey(axMagic, "AppendStrStr"), sxSat)
  test "typeclass string: a `$t` parameter's `len` beside `t` (sat)":
    walkUnits(i57Param, cellKey(axTypeClass, "string"), sxSat)
  test "typeop letCursor/string: `acc = acc + len($t)` (sat)":
    walkUnits(i57LetCursor, cellKey(axTypeOp, "letCursor/string"), sxSat)
  test "typeop fieldDefault/string: `o.n + o.w.len <= -100` (sat)":
    walkUnits(p57FieldDefault, cellKey(axTypeOp, "fieldDefault/string"), sxSat)

suite "INT-57: walker version":
  test "symexWalkerVersion >= 428":
    check parseInt(symexWalkerVersion) >= 428
