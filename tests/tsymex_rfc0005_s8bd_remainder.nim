## RFC-0005 (soundness channels) slice S8bd -- S8ba's remainder.
##
## Pinned here (the RFC's "As landed (S8bd)" note has the design and the
## measurements):
##   (1) a string index `i` that is a bit-vector, compared with `s.len`
##       both as itself and as `i + 1`, decides: the two Int views of `i`
##       and `i + 1` are linked by an exact theorem of two's complement
##       (`bvOffsetLinks`). It ran ~41M units to `sxUnknown`;
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8bd_remainder_b`, `tsymex_rfc0005_s8bd_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 69 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

const exact = SymexSettings(integerSemantics: isExact)

# ---- (1) a bit-vector string index against the length ------------------------

proc sIdx(s: string, i: int) =
  ## `i` is a bit-vector (`i + 1` can overflow); `i < s.len` reads its Int
  ## view, `i + 1 > s.len` the Int view of `i + 1`.
  if i >= 0 and i < s.len and s[i] == 'a' and i + 1 > s.len:
    symexTarget("si_dead")
  if i >= 0 and i < s.len and s[i] == 'a' and i + 1 == s.len:
    symexTarget("si")

proc sIdxNoAt(s: string, i: int) =
  if i >= 0 and i < s.len and i + 1 > s.len: symexTarget("sn_dead")

proc sIdxPrev(s: string, i: int) =
  ## The subtraction twin: `s[i - 1]` with `i - 1 >= s.len`.
  if i >= 1 and i <= s.len and s[i - 1] == 'b' and i - 1 >= s.len:
    symexTarget("sp_dead")
  if i >= 1 and i <= s.len and s[i - 1] == 'b' and i == s.len:
    symexTarget("sp")

suite "S8bd (1): a bit-vector string index against the length decides":

  test "nim":
    let s = "xa"
    check s[1] == 'a' and 1 + 1 == s.len

  test "s[i] with i + 1 > s.len is refuted":
    ## RED: `sxUnknown` (`beSolverUndef`, "no model with every string / seq
    ## at most 128 elements"), ~41M units, on both Z3 versions.
    discard clean(sIdx, "si_dead", sxUnsat)
    let r = clean(sIdx, "si", sxSat)
    if r.status == sxSat:
      let i = r.witness[1]
      check i + 1 == r.witness[0].len and r.witness[0][i] == 'a'

  test "the same without the character read":
    discard clean(sIdxNoAt, "sn_dead", sxUnsat)

  test "the subtraction twin":
    discard clean(sIdxPrev, "sp_dead", sxUnsat)
    let r = clean(sIdxPrev, "sp", sxSat)
    if r.status == sxSat:
      check r.witness[0][r.witness[1] - 1] == 'b'

  test "the bit-vector encoding (isExact)":
    discard clean(sIdx, "si_dead", sxUnsat, exact)
    discard clean(sIdxNoAt, "sn_dead", sxUnsat, exact)

  test "the links are theorems":
    ## Every link `bvOffsetLinks` states, at width 8 over a grid of `x` and
    ## `c` (both signs, the wrap at both ends), is valid: with `x` fixed,
    ## its negation is UNSAT.
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bd_x")
    proc view(b: Z3BitVec[8], signed: bool): Z3Int =
      wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, b.raw, signed))
    var n = 0
    for xv in [0, 1, 2, 126, 127, 128, 129, 200, 254, 255]:
      for cv in [1, 2, 127, 128, 129, 255]:
        let c = mkBitVec[8](ctx, cv)
        for signed in [false, true]:
          for t in [x + c, c + x, x - c]:
            let facts = bvOffsetLinks(ctx, [view(t, signed) == view(t, signed),
                                            view(x, signed) == view(x, signed)])
            checkpoint $xv & " " & $cv & " " & $signed
            check facts.len == 1
            for f in facts:
              let s = querySolver(ctx, [x == mkBitVec[8](ctx, xv), not f], 0)
              check s.check() == zsUnsat
              inc n
    check n == 10 * 6 * 2 * 3

  test "a view the query does not hold is not linked":
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bd_y")
    let t = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw,
      (x + mkBitVec[8](ctx, 1)).raw, false))
    check bvOffsetLinks(ctx, [t > mkInt(ctx, 3)]).len == 0

# ---- (2) a seq[distinct] parameter -------------------------------------------

type Meters = distinct int
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}
type Grams = distinct int32
type Secs = distinct float
type Km = distinct Meters    # a distinct of a distinct

proc dParam(s: seq[Meters]) =
  if s.len > 1 and s[0] == Meters(3) and s[1] < Meters(-5): symexTarget("dp")
  if s.len > 0 and s[0] == Meters(3) and int(s[0]) != 3: symexTarget("dp_dead")

proc dParam32(s: seq[Grams]) =
  if s.len == 2 and int32(s[1]) == 70000'i32: symexTarget("d32")

proc dParamF(s: seq[Secs]) =
  if s.len == 1 and float(s[0]) > 2.5: symexTarget("df")

proc dParamNested(s: seq[Km]) =
  if s.len == 1 and int(Meters(s[0])) == 11: symexTarget("dn")

suite "S8bd (2): a seq[distinct] parameter has a witness":

  test "nim":
    let s = @[Meters(3), Meters(-6)]
    check s[0] == Meters(3) and s[1] < Meters(-5)

  test "seq[Meters]":
    ## RED: `sxUnknown`, `feUnsupportedWitnessType` (S8ba pinned it so).
    let r = clean(dParam, "dp", sxSat)
    if r.status == sxSat:
      let w: seq[Meters] = r.witness[0]
      check w.len > 1 and int(w[0]) == 3 and int(w[1]) < -5
      check replayWitness(dParam, r.witness, tLabel("dp"), {}).outcome == roConfirmed
    discard clean(dParam, "dp_dead", sxUnsat)

  test "other widths, a float base, a nested distinct":
    let a = clean(dParam32, "d32", sxSat)
    if a.status == sxSat:
      let w: seq[Grams] = a.witness[0]
      check w.len == 2 and int32(w[1]) == 70000'i32
      check replayWitness(dParam32, a.witness, tLabel("d32"), {}).outcome == roConfirmed
    # A distinct of a float carries S8ba's `geDistinctBijectivitySkipped`
    # hint (sevHint): the sort is modelled without the round-trip axiom. A
    # distinct of a distinct over a DECIDABLE base (`Km` here) does not,
    # since RFC-0005 S8bg: the hint used to fire for it too (the immediate
    # base's own representative is a nested `svDistinct`, never a
    # bijectivity-primitive kind, regardless of what its real base is),
    # wrongly naming the chain's base non-decidable when it is `int`. See
    # `tsymex_rfc0005_s8bg_remainder.nim` for the dedicated pins (one
    # level, two levels, a genuinely non-decidable base).
    template hinted(fn: typed, lbl: string): untyped =
      block:
        let r = symexFind(fn, tLabel(lbl))
        checkpoint lbl & " " & $r.status & " " & show(r.errors)
        check r.status == sxSat
        for e in r.errors: check e.severity == sevHint
        r
    let b = hinted(dParamF, "df")
    if b.status == sxSat:
      let w: seq[Secs] = b.witness[0]
      check float(w[0]) > 2.5
      check replayWitness(dParamF, b.witness, tLabel("df"), {}).outcome == roConfirmed
    let c = hinted(dParamNested, "dn")
    # RFC-0005 S8bg: `Km`'s real base (`int`, through `Meters`) is
    # decidable, so no hint fires for it any more (unlike `dParamF`'s
    # `Secs` above, over an actually non-decidable `float`).
    check c.errors.len == 0
    if c.status == sxSat:
      let w: seq[Km] = c.witness[0]
      check int(Meters(w[0])) == 11
      check replayWitness(dParamNested, c.witness, tLabel("dn"), {}).outcome == roConfirmed

# ---- (3) the heap-depth budget bounds a chain, not a count -------------------

type Box = ref object
  x: int
type Box2 = ref object
  x: int
  y: int16
