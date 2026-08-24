## N14 (RFC-chapulin-hardening bucket-2, walker v121) — modeling the
## previously-unmodeled seq mutation/query operations: element ASSIGNMENT
## (`xs[i] = v`), `.pop()`, `.del(i)`, `.insert(v, i)`, `in`/`.contains()`,
## and `seq == seq`.
##
## Doctrine recap (see `docs/RFC-chapulin-hardening.handoff.md`'s N14 entry
## and this repo's quantifier-free discipline — `canonicalize.nim`/
## `dsl_parser.nim` cite it repeatedly as "the G4 hang lesson"): every op
## below is either MODELED FAITHFULLY (a real Z3 encoding, SAT + UNSAT +
## defect-fork pins) or DECLINED HONESTLY (classified, never a crash, never
## a silent wrong verdict) — a lossy approximation is never acceptable.
##
## ---- MODELED (3 ops) ----
##
## 1. Element ASSIGN `xs[i] = v` — new `isIndexAssign` statement (mirrors
##    `isIndex`'s own OOB fork exactly), `store(data, i, v)` via the
##    PRE-EXISTING `storeSeqElem` helper (already used by seq-literal
##    construction and `.map`/`.filter` — this slice just wires it to a
##    direct element write for the first time).
## 2. `.pop()` — new `isSeqPop` statement (needs a FRESH return-value bind
##    ALONGSIDE the receiver rebind, a shape neither `isIndex` nor
##    `isIndexAssign` carries): `result = data[len-1]; len' = len-1`;
##    `IndexDefect` on an empty seq (real Nim semantics — see the stdlib
##    doc: "Raises IndexDefect if `s` is empty").
## 3. `.del(i)` — Nim's O(1) unordered removal (swap-with-last):
##    `data' = store(data, i, data[len-1]); len' = len-1`; `IndexDefect` on
##    `i` outside `[0, len)`. Modeled via a NEW raise-fork sink
##    (`seqOobConds`/`drainSeqOobRaises`, mirroring `strIndexOobConds`'s own
##    SND-4 pattern exactly) rather than a dedicated statement kind — `.del`
##    was ALREADY an ordinary `isAssign` (`mkAssign(recv, mkSeqDel(...))`),
##    a single env rebind with no extra return value, so the lighter sink
##    route applies cleanly (unlike `.pop()`).
##
## ---- DECLINED WITH DOCTRINE (3 ops) ----
##
## 4. `.insert(v, i)` — a SYMBOLIC-length shift of every element at
##    `[i, len)` up by one position has no quantifier-free closed form: Z3
##    arrays are functions, and "every index past `i` moves" is exactly the
##    shape that needs either a universal quantifier (banned — this
##    codebase's recurring "G4 hang" lesson: `∀`/lambda-array encodings over
##    a Sequence/Array theory MBQI-hang this Z3 build) or an UNBOUNDED
##    per-index unroll keyed off a genuinely symbolic `len` (no static
##    bound to unroll TO — unlike the k-unroll while-loop machinery, which
##    unrolls a bounded STRUCTURAL constant, `maxLoopUnwind`, not a
##    data-dependent one). Adjudicated: stays classified-declined
##    (`feUnsupportedOp`, pre-existing, unchanged by this slice) — pinned
##    below to prove it stays classified rather than regressing to a crash.
## 5. `in` / `.contains()` on a seq — genuinely modelable in principle as a
##    k-bounded existential (`OR_{j<k} (j<len and data[j]==needle)`, gated
##    by a structural fork on `len <= k` vs. the N20 k-unroll route for
##    `len > k`) — but that is architecturally the SAME closed-form-scan
##    machinery investment as `iekStrInOptionRegion`/the B-series
##    recognizers (a parse-time shape recognizer + a NEW walker encoding),
##    which is out of proportion for a slice sharing a round with 5 other
##    ops. Adjudicated: decline-with-doctrine. HOWEVER: this slice found and
##    fixed a REAL crash one layer up the same op — `v in xs`/`xs.contains(v)`
##    on a bare `seq[int]` parameter did not merely decline, it CRASHED AT
##    MACRO-EXPANSION TIME (`dsl_typebridge.nim:413 "node has no type"`, the
##    A5 hard-crash class) because the parse-time `contains(c,k)` recognizer
##    only ever routed `itTable`/`itSet` receivers to the (already-existing,
##    already-safe) `iekContains` IR node — an `itSeq` receiver fell through
##    into ordinary callee resolution, attempting to walk `system.contains`'s
##    generic `openArray` body. Fixed (dsl_parser.nim, the `contains`/
##    `hasKey` recognizer): widened the receiver-kind gate to include
##    `itSeq`, with the same `nnkHiddenStdConv`-unwrap the `[]`-slice arm
##    already needed (`system.contains[T](a: openArray[T], item: T)` takes
##    its seq argument through an implicit seq->openArray conversion, so the
##    bare receiver classifies `itUninterp`-ish/non-itSeq without the
##    unwrap). `iekContains`'s own runtime dispatch already declined
##    `feUnsupportedOp` cleanly for any non-svTable/svSet receiver — only the
##    PARSE-TIME gate was missing the route into it. Net effect: crash ->
##    honest classified decline (verdict-affecting: a SUT containing `x in
##    mySeq` no longer aborts the whole macro expansion).
## 6. `seq == seq` — sound modeling needs `len_a == len_b AND (pointwise
##    equality over [0, len))`, which is the SAME symbolic-length
##    quantifier-free obstacle as items 4/5 (a conjunction over a
##    data-dependent range, not a structural one) — plain Z3 array
##    EXTENSIONALITY (`data_a == data_b` as arrays) would be WRONG regardless
##    (garbage beyond `len` may differ while the seqs are still equal, or
##    coincide while lengths differ — either direction is unsound). Already
##    declines honestly and totally: `lowerCmp`'s catch-all routes svSeq
##    operands to `eqBV`/`neBV`, whose `else` arm classifies
##    `feUnsupportedOp` (unchanged by this slice, confirmed via direct
##    probe before writing this suite). Pinned below to prove it stays
##    classified.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# 1. Element ASSIGN `xs[i] = v`
# =============================================================================

proc assignThenReadBack(xs: seq[int], i: int, v: int) =
  symexAssume(i >= 0 and i < xs.len)
  var ys = xs
  ys[i] = v
  if ys[i] == v:
    symexTarget("assign_readback")

proc assignThenMismatch(xs: seq[int], i: int, v: int) =
  ## UNSAT companion: a just-written slot can NEVER read back a DIFFERENT
  ## value — store-then-select at the SAME index is definitionally `v`.
  symexAssume(i >= 0 and i < xs.len)
  var ys = xs
  ys[i] = v
  if ys[i] != v:
    symexTarget("assign_mismatch")

proc assignLenUnchanged(xs: seq[int], i: int, v: int) =
  ## Soundness companion: element assignment must NEVER change `.len`.
  symexAssume(i >= 0 and i < xs.len)
  let oldLen = xs.len
  var ys = xs
  ys[i] = v
  if ys.len != oldLen:
    symexTarget("assign_len_changed")

proc assignOob(xs: seq[int], i: int, v: int) =
  var ys = xs
  ys[i] = v
  discard ys

suite "N14 — seq element assign `xs[i] = v`":
  test "SAT: a freshly-written slot reads back the written value":
    let r = symexFind(assignThenReadBack, tLabel("assign_readback"))
    check r.status == sxSat
    let xs = r.witness[0]
    let i = r.witness[1]
    let v = r.witness[2]
    check i >= 0 and i < xs.len
    # Real-Nim cross-check: replay the exact mutation the SUT performed.
    var ys = xs
    ys[i] = v
    check ys[i] == v

  test "UNSAT: a freshly-written slot can never read back a different value":
    let r = symexFind(assignThenMismatch, tLabel("assign_mismatch"))
    check r.status == sxUnsat

  test "UNSAT: element assign never changes .len (soundness)":
    let r = symexFind(assignLenUnchanged, tLabel("assign_len_changed"))
    check r.status == sxUnsat

  test "defect: OOB index forks IndexDefect on assignment":
    let r = symexFind(assignOob, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
    let xs = r.raisedWitness[0]
    let i = r.raisedWitness[1]
    check (i < 0 or i >= xs.len)

  test "walker version floor >= 121 (N14 element assign)":
    check parseInt(symexWalkerVersion) >= 121

# =============================================================================
# 2. `.pop()`
# =============================================================================

proc popShrinksLen(xs: seq[int]) =
  symexAssume(xs.len > 0)
  let oldLen = xs.len
  var ys = xs
  discard ys.pop()
  if ys.len == oldLen - 1:
    symexTarget("pop_len_ok")

proc popLenMismatch(xs: seq[int]) =
  ## UNSAT companion.
  symexAssume(xs.len > 0)
  let oldLen = xs.len
  var ys = xs
  discard ys.pop()
  if ys.len != oldLen - 1:
    symexTarget("pop_len_bad")

proc popReturnsLastElem(xs: seq[int]) =
  symexAssume(xs.len > 0)
  let expected = xs[xs.len - 1]
  var ys = xs
  let popped = ys.pop()
  if popped == expected:
    symexTarget("pop_val_ok")

proc popReturnsWrongElem(xs: seq[int]) =
  ## UNSAT companion: the popped value can never differ from the
  ## pre-pop last element.
  symexAssume(xs.len > 0)
  let expected = xs[xs.len - 1]
  var ys = xs
  let popped = ys.pop()
  if popped != expected:
    symexTarget("pop_val_bad")

proc popEmpty(xs: seq[int]) =
  var ys = xs
  let v = ys.pop()
  discard v

suite "N14 — seq `.pop()`":
  test "SAT: pop shrinks .len by exactly one":
    let r = symexFind(popShrinksLen, tLabel("pop_len_ok"))
    check r.status == sxSat
    let xs = r.witness[0]
    check xs.len > 0
    var ys = xs
    discard ys.pop()
    check ys.len == xs.len - 1

  test "UNSAT: pop's post-length can never differ from len-1":
    let r = symexFind(popLenMismatch, tLabel("pop_len_bad"))
    check r.status == sxUnsat

  test "SAT: pop returns the pre-pop last element":
    let r = symexFind(popReturnsLastElem, tLabel("pop_val_ok"))
    check r.status == sxSat
    let xs = r.witness[0]
    check xs.len > 0
    var ys = xs
    let popped = ys.pop()
    check popped == xs[xs.len - 1]

  test "UNSAT: pop can never return a value other than the pre-pop last element":
    let r = symexFind(popReturnsWrongElem, tLabel("pop_val_bad"))
    check r.status == sxUnsat

  test "defect: pop on a possibly-empty seq forks IndexDefect":
    let r = symexFind(popEmpty, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
    let xs = r.raisedWitness[0]
    check xs.len == 0

  test "walker version floor >= 121 (N14 pop)":
    check parseInt(symexWalkerVersion) >= 121

# =============================================================================
# 3. `.del(i)` — Nim's O(1) unordered removal (swap-with-last)
# =============================================================================

proc delShrinksLen(xs: seq[int], i: int) =
  symexAssume(i >= 0 and i < xs.len)
  let oldLen = xs.len
  var ys = xs
  ys.del(i)
  if ys.len == oldLen - 1:
    symexTarget("del_len_ok")

proc delLenMismatch(xs: seq[int], i: int) =
  ## UNSAT companion.
  symexAssume(i >= 0 and i < xs.len)
  let oldLen = xs.len
  var ys = xs
  ys.del(i)
  if ys.len != oldLen - 1:
    symexTarget("del_len_bad")

proc delSwapsLastIn(xs: seq[int], i: int) =
  ## For `i` STRICTLY before the last element: `del` swaps the last
  ## element into slot `i`.
  symexAssume(i >= 0 and i < xs.len - 1)
  let lastVal = xs[xs.len - 1]
  var ys = xs
  ys.del(i)
  if ys[i] == lastVal:
    symexTarget("del_swap_ok")

proc delSwapsWrong(xs: seq[int], i: int) =
  ## UNSAT companion.
  symexAssume(i >= 0 and i < xs.len - 1)
  let lastVal = xs[xs.len - 1]
  var ys = xs
  ys.del(i)
  if ys[i] != lastVal:
    symexTarget("del_swap_bad")

proc delOob(xs: seq[int], i: int) =
  var ys = xs
  ys.del(i)
  discard ys

suite "N14 — seq `.del(i)` (swap-with-last)":
  test "SAT: del shrinks .len by exactly one":
    let r = symexFind(delShrinksLen, tLabel("del_len_ok"))
    check r.status == sxSat
    let xs = r.witness[0]
    let i = r.witness[1]
    check i >= 0 and i < xs.len
    var ys = xs
    ys.del(i)
    check ys.len == xs.len - 1

  test "UNSAT: del's post-length can never differ from len-1":
    let r = symexFind(delLenMismatch, tLabel("del_len_bad"))
    check r.status == sxUnsat

  test "SAT: del(i) swaps the last element into slot i (i before the end)":
    let r = symexFind(delSwapsLastIn, tLabel("del_swap_ok"))
    check r.status == sxSat
    let xs = r.witness[0]
    let i = r.witness[1]
    check i >= 0 and i < xs.len - 1
    var ys = xs
    ys.del(i)
    check ys[i] == xs[xs.len - 1]

  test "UNSAT: del(i) can never fail to swap the last element into slot i":
    let r = symexFind(delSwapsWrong, tLabel("del_swap_bad"))
    check r.status == sxUnsat

  test "defect: OOB index forks IndexDefect on del":
    let r = symexFind(delOob, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
    let xs = r.raisedWitness[0]
    let i = r.raisedWitness[1]
    check (i < 0 or i >= xs.len)

  test "walker version floor >= 121 (N14 del)":
    check parseInt(symexWalkerVersion) >= 121

# =============================================================================
# 4. `.insert(v, i)` — DECLINED WITH DOCTRINE (see header doc, item 4)
# =============================================================================

proc insertUnbounded(xs: seq[int], v: int, i: int) =
  symexAssume(i >= 0 and i <= xs.len)
  var ys = xs
  ys.insert(v, i)
  symexTarget("insert_reached")

suite "N14 — seq `.insert(v, i)` (decline-with-doctrine)":
  test "decline stays CLASSIFIED (feUnsupportedOp), never a crash":
    let r = symexFind(insertUnbounded, tLabel("insert_reached"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == feUnsupportedOp

# =============================================================================
# 5. `in` / `.contains()` on a seq — DECLINED WITH DOCTRINE, crash fixed
#    (see header doc, item 5)
# =============================================================================

proc seqInMembership(xs: seq[int], v: int) =
  if v in xs:
    symexTarget("in_reached")

proc seqContainsMethod(xs: seq[int], v: int) =
  if xs.contains(v):
    symexTarget("contains_reached")

suite "N14 — seq `in` / `.contains()` (decline-with-doctrine, ex-crash)":
  test "`v in xs` no longer crashes at macro-expansion time; declines classified":
    let r = symexFind(seqInMembership, tLabel("in_reached"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == feUnsupportedOp

  test "`xs.contains(v)` method-call form: same decline route":
    let r = symexFind(seqContainsMethod, tLabel("contains_reached"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == feUnsupportedOp

# =============================================================================
# 6. `seq == seq` — DECLINED WITH DOCTRINE (see header doc, item 6)
# =============================================================================

proc seqEquality(xs: seq[int], ys: seq[int]) =
  if xs == ys:
    symexTarget("eq_reached")

suite "N14 — seq `==` (decline-with-doctrine)":
  test "decline stays CLASSIFIED (feUnsupportedOp), never a crash":
    let r = symexFind(seqEquality, tLabel("eq_reached"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == feUnsupportedOp

# =============================================================================
# 7. Item 1 audit pin (round-6 fix round 3) -- element-assign/pop/del reaching
#    a PLACEHOLDER-ized seq (variant-arm unbacked-elem field, same
#    construction as tsymex_r6_n13_reassign_seqarm.nim's `Rec`/`opts`).
#    `isIndexAssign`/`isSeqPop`'s own `isUnsupportedFieldPlaceholder` guard
#    (runtime.nim ~8665/~8727, the R1 chokepoint) exists precisely to make
#    this classify sxUnknown rather than crash or silently mis-store into
#    the placeholder's inert backing array. `.del(i)` shares the same guard
#    (`iekSeqDel`, runtime.nim ~5285). Reading `v.opts` itself already
#    declines (N13-3) and binds a placeholder `SymVal` to the local copy —
#    these pins confirm the SUBSEQUENT mutation on that already-placeholder
#    value stays classified too, never a wrong verdict, never a crash.
# =============================================================================

type
  MKind = enum mkA, mkB
  MRec = object
    case kind: MKind
    of mkA: a: int
    of mkB:
      opts: seq[(string, string)]   ## unbacked elem (itTuple) -> placeholder

proc mkPlaceholderRec(v: var MRec) =
  v.kind = mkB

proc mutIndexAssignOnPlaceholder(v: var MRec, i: int) =
  mkPlaceholderRec(v)
  var o = v.opts
  o[i] = ("k", "v")
  symexTarget("mut_indexassign_placeholder")

proc mutPopOnPlaceholder(v: var MRec) =
  mkPlaceholderRec(v)
  var o = v.opts
  discard o.pop()
  symexTarget("mut_pop_placeholder")

proc mutDelOnPlaceholder(v: var MRec, i: int) =
  mkPlaceholderRec(v)
  var o = v.opts
  o.del(i)
  symexTarget("mut_del_placeholder")

suite "N14 — mutation on a placeholder-ized seq (item 1 audit pin, round-6 fix round 3)":
  test "index-assign on a placeholder receiver classifies sxUnknown, never a crash":
    let r = symexFind(mutIndexAssignOnPlaceholder, tLabel("mut_indexassign_placeholder"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.severity == sevError)

  test "pop on a placeholder receiver classifies sxUnknown, never a crash":
    let r = symexFind(mutPopOnPlaceholder, tLabel("mut_pop_placeholder"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.severity == sevError)

  test "del on a placeholder receiver classifies sxUnknown, never a crash":
    let r = symexFind(mutDelOnPlaceholder, tLabel("mut_del_placeholder"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.severity == sevError)
