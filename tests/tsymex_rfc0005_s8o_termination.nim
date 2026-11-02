## RFC-0005 (soundness channels) slice S8o -- S8k's termination remainder.
##
## S8k (walker 161) bounded every string / seq query (`maxSeqLen`,
## `seqQueryRLimit`) and decided byte tests in character form. This slice
## closes what it left:
##   (0) the character-form rewrite matched Z3's `int2bv` by its printed
##       NAME, `int_to_bv`, which is Z3 5.x's spelling. The Windows leg's
##       Z3 4.13.4 names it `int2bv`, so the rewrite never fired there, and
##       the lowered byte tests ran out of the new budget: B7R-6, B7r2-1a
##       and its trip-wire went `sxUnknown` on symex-mingw. Operators are
##       now matched by decl kind, read off terms built in the running Z3;
##   (1) byte tests other than an equality with a constant (`s[i] ==
##       s[j]`, a byte against a symbolic value) take the character form
##       too;
##   (2) a constant string index reaches Z3 as a numeral;
##   (3) the concolic `pcSatByConcreteInputs` check is bounded;
##   (4) no model or verdict comes from Z3's incremental core over a
##       `seq.last_indexof` query.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build); the probe is quoted beside the test.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/choice
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- (0) the character form does not depend on Z3's operator names --------
#
# Probe: `q20(repeat('q', 20))` reaches its label.

proc q20(s: string) =
  if s.len == 20 and s[19] == 'q':
    symexTarget("s8o_q20")

const tightSeqBudget = SymexSettings(
  budget: ResourceBudget(seqQueryRLimit: 1_000_000))

suite "S8o (0): byte tests take the character form on every Z3 build":

  test "oracle: the q20 label is reachable in Nim":
    var reached = false
    let s = repeat('q', 20)
    if s.len == 20 and s[19] == 'q': reached = true
    check reached

  test "s.len == 20 and s[19] == 'q' is decided within 1M units":
    ## In the lowered form (`int2bv8(str.to_code(str.at(s, 19))) == 0x71`)
    ## this query needs about 2.3M units; in character form it is
    ## immediate. RED on Z3 4.13.4 (the symex-mingw leg's build), where
    ## the rewrite matched no operator: `sxUnknown` under this budget.
    let r = symexFind(q20, tLabel("s8o_q20"), tightSeqBudget)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 20
      check r.witness[0][19] == 'q'

# ---- (1) byte against byte, and byte against a char parameter ------------
#
# Probes: `pairs(s)` reaches its label for `s = repeat('q', 40)`;
# `withChar(s, 'q')` for the same `s`; `clash("ab")` never does (no string
# has `s[0] == s[1]`, `s[0] == 'a'` and `s[1] == 'b'`).

proc pairs(s: string) =
  if s.len == 40 and s[39] == s[3] and s[3] == s[20] and s[20] != 'a':
    symexTarget("s8o_pairs")

proc withChar(s: string, c: char) =
  if s.len == 40 and s[39] == c and s[2] == c and c != 'a':
    symexTarget("s8o_char")

proc clash(s: string) =
  if s.len == 2 and s[0] == s[1] and s[0] == 'a' and s[1] == 'b':
    symexTarget("s8o_clash")

suite "S8o (1): every byte equality takes the character form":

  test "oracle: the pairs and withChar labels are reachable in Nim":
    let s = repeat('q', 40)
    check s.len == 40 and s[39] == s[3] and s[3] == s[20] and s[20] != 'a'
    let c = 'q'
    check s[39] == c and s[2] == c and c != 'a'

  test "s[39] == s[3] and s[3] == s[20] is decided within 1M units":
    ## Lowered, the pair equalities needed 2.5M units from their own text
    ## (Z3 4.13.4) and ran past 20M in the walker on 5.1 (`sxUnknown`);
    ## as `str.at(s, 39) == str.at(s, 3)`, 51k.
    let r = symexFind(pairs, tLabel("s8o_pairs"), tightSeqBudget)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let w = r.witness[0]
      check w.len == 40 and w[39] == w[3] and w[3] == w[20] and w[20] != 'a'

  test "s[39] == c and s[2] == c for a char parameter c, within 1M units":
    ## Lowered: 8.5M units from its own text, past 20M in the walker.
    ## `str.at(s, 39) == str.from_code(bv2nat(c))`: 185k.
    let r = symexFind(withChar, tLabel("s8o_char"), tightSeqBudget)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (w, cb) = r.witness   # a char witness is carried as its byte
      let c = char(cb)
      check w.len == 40 and w[39] == c and w[2] == c and c != 'a'

  test "the character form keeps a byte contradiction UNSAT":
    let r = symexFind(clash, tLabel("s8o_clash"), tightSeqBudget)
    checkpoint show(r.errors)
    check r.status == sxUnsat

# ---- (2) a constant string index reaches Z3 as a numeral -------------------
#
# `s[3]` lowers its index through `bvTermToZ3Int`: Z3's signed `bv2int` of the
# constant `#x0000000000000003` is `ite(bvslt c 0, bv2int c - 2^64,
# bv2int c)`, which reached every query unevaluated. A numeral is folded
# first; a symbolic operand keeps the conversion.

suite "S8o (2): a constant bit-vector reaches Z3 as an Int numeral":

  test "signed and unsigned constants fold to their Nim values":
    let ctx = newContext()
    setCurrentContext(ctx)
    let three = bvTermToZ3Int(mkBitVec[64](ctx, 3), true)
    check isNumeralAst(ctx, three.raw)
    check getNumeralString(three) == "3"
    let minusOne = bvTermToZ3Int(mkBitVec[64](ctx, -1'i64), true)
    check isNumeralAst(ctx, minusOne.raw)
    check getNumeralString(minusOne) == "-1"
    let low64 = bvTermToZ3Int(mkBitVec[64](ctx, low(int64)), true)
    check getNumeralString(low64) == "-9223372036854775808"
    let big = bvTermToZ3Int(mkBitVec[64](ctx, high(uint64)), false)
    check isNumeralAst(ctx, big.raw)
    check getNumeralString(big) == "18446744073709551615"
    let byteFF = bvTermToZ3Int(mkBitVec[8](ctx, 255), true)
    check getNumeralString(byteFF) == "-1"
    let ubyteFF = bvTermToZ3Int(mkBitVec[8](ctx, 255), false)
    check getNumeralString(ubyteFF) == "255"

  test "a symbolic bit-vector keeps its conversion":
    let ctx = newContext()
    setCurrentContext(ctx)
    let x = bvTermToZ3Int(mkBitVecVar[64](ctx, "x"), true)
    check not isNumeralAst(ctx, x.raw)

# ---- (3) the concolic soundness check is bounded ---------------------------
#
# `runConcolicCollectImpl` checks that every collected path condition is
# satisfied by the concrete draws (`pcSatByConcreteInputs`). That check ran
# with no `rlimit` at all; it now runs under `concreteBranchRLimit`, like the
# branch-outcome solves beside it. An exhausted bound is `false` (not
# proven), never a claim.

proc concolicGate(x: int) =
  if x * x == 49:
    symexTarget("sq")

suite "S8o (3): pcSatByConcreteInputs runs under the concolic budget":

  test "oracle: 7 * 7 == 49":
    check 7 * 7 == 49

  test "under the default budget the check proves the draws satisfy the pc":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(concolicGate, trace, bindings)
    check r.pcSatByConcreteInputs

  test "a caller's queryRLimit bounds it: an exhausted check is not a proof":
    ## Was: `true` -- the check ignored every budget.
    const oneUnit = SymexSettings(budget: ResourceBudget(queryRLimit: 1))
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(concolicGate, trace, bindings, oneUnit)
    check not r.pcSatByConcreteInputs

# ---- (4) no verdict from the incremental core over seq.last_indexof -------
#
# The only incremental check any walker query takes is `checkCapped`'s step
# 2 (a check under the cap's assumption literal, for its unsat core); every
# other check, and every model, is a one-shot `check()` of a fresh solver,
# and the walker builds no quantifier. Z3's incremental core evaluates
# `seq.last_indexof` over a term fixed to a constant wrongly (-4294967292
# for `"abc".rfind("bc")`), so step 2 is skipped for such a query. This
# pins that skip: the capped query below is UNSAT only because `t` must be
# longer than the cap, so step 2 would run -- and, without the skip, read
# its core from the wrong value (probed: removing the `not lastIndex`
# guard turns this `sxSat` into `sxUnsat`).
#
# RFC-0005 S8au: `rfind` now lowers to an index split (a fresh Int with
# `s = pre ++ c ++ post` axioms), so this query holds no `seq.last_indexof`
# term. `seqLenCaps` still marks it `lastIndex` (the split stands for the
# term), so it keeps this regime and its `sxSat`: without that it is a cap
# decline (probed).
#
# Probe: `lastIdx("abc", repeat('x', 11))` reaches its label.
#
# RFC-0005 batch 6: S8bl folds a split whose haystack is pinned to a
# literal (`symexAssume(s == "abc")`) to its numeral, so `lastIdx`'s query
# holds no split and is an ordinary capped query: `t.len > 10` under a cap
# of 8 declines, as any query SAT only past the cap does (sound: never a
# definite verdict). `lastIdxFree` keeps the regime this pins -- its
# haystack is not a literal, so its `rfind` is a split, marked `lastIndex`.
# Probe: `lastIdxFree("abc", repeat('x', 11))` reaches its label.

proc lastIdx(s, t: string) =
  symexAssume(s == "abc")
  if t.len > 10 and s.rfind("bc") == 1:
    symexTarget("s8o_rfind")

proc lastIdxFree(s, t: string) =
  if t.len > 10 and s.len == 3 and s.rfind("bc") == 1:
    symexTarget("s8o_rfind_free")

suite "S8o (4): seq.last_indexof never reaches the incremental core":

  test "oracle: \"abc\".rfind(\"bc\") == 1":
    check "abc".rfind("bc") == 1

  test "oracle: lastIdxFree's condition holds in Nim":
    let (s, t) = ("abc", repeat('x', 11))
    check t.len > 10 and s.len == 3 and s.rfind("bc") == 1

  test "a capped-out rfind query is decided by the one-shot solver":
    const smallCap = SymexSettings(budget: ResourceBudget(maxSeqLen: 8))
    let r = symexFind(lastIdxFree, tLabel("s8o_rfind_free"), smallCap)
    checkpoint show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      let (s, t) = r.witness
      check t.len > 10 and s.len == 3 and s.rfind("bc") == 1

  test "a literal haystack's rfind folds, and the cap declines the query":
    # RFC-0005 batch 6 (S8bl's fold): no split, so the cap's own regime --
    # an in-band decline, never sxUnsat.
    const smallCap = SymexSettings(budget: ResourceBudget(maxSeqLen: 8))
    let r = symexFind(lastIdx, tLabel("s8o_rfind"), smallCap)
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var capDecline = false
    for e in r.errors:
      if e.kind == beSolverUndef and "maxSeqLen" in e.msg: capDecline = true
    check capDecline

suite "S8o: walker version floor":

  test "walker version >= 163":
    check parseInt(symexWalkerVersion) >= 163
