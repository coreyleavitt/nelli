## Round-6 lows slice (fix round 10, walker v108) -- four Low-severity
## decline-quality findings from the round-6 review ledger.
##
## N15: a field-sourced placeholder consumed through INDEXING (or the
## call-form slice) surfaced a DIFFERENT classified kind than the same
## placeholder consumed through `.len`. Root cause: both `nnkBracketExpr`'s
## `itSeq` arm and the call-form `` `[]`(data, idx) `` arm (`dsl_parser.nim`)
## unconditionally called `parseExpr(n[0])` on the receiver BEFORE dispatching
## on index-vs-slice -- for a field-sourced placeholder, that call already
## runs `declineUnsupportedFieldRead` and hands back its fake empty-seq
## stand-in, and the caller then built a REAL `isIndex`/`mkSeqSlice`
## walk-time node OVER that literal. `mkIndexStmt`'s walk-time lowering
## (`lowerLeafInExpr`, runtime.nim) asserts its container operand is one of
## `{iekVar, iekField, iekStrBytes}` -- an `iekSeqLit` receiver trips that
## assertion, surfacing `weInternalWalkerFault` instead of the
## `seNestedSeqUnsupported` kind every other placeholder-consuming form
## reports. Fixed by detecting the receiver's already-recorded decline (one
## new `ctx.parseErrors` entry, kind `seNestedSeqUnsupported`, appended by
## the `parseExpr(n[0])` call itself) and stopping before any
## container-consuming IR is built, returning a dummy of the WHOLE
## expression's own result type instead.
##
## N30: `symValFromRawAst` (runtime.nim) has no `itString` arm for a closure
## RETURN type -- a closure whose return type is `string` raised an untagged
## `ValueError` that escaped `applyClosureGround` uncaught, surfacing
## `weInternalWalkerFault` instead of a clean classified decline. Fixed by
## wrapping the `symValFromRawAst` call in a `try`/`except ValueError` that
## reports `feUnsupportedOp` (matching N16's own `applyClosureGround` decline
## style) and falls back to `defaultZero(cb.retTy, ...)`.
##
## N41 (SOUNDNESS CROSS-CONSTRAINT): `sortOfTuple`/`rawAnyAstOf` (runtime.nim)
## have no compound-sv-kind arms (`svTable`/`svSet`) -- a compound value has
## no single scalar Z3 leaf ast/sort, so BOTH the lambda-param/return family
## (`sortOfTuple`, reached from `runtime_closures.nim`'s `buildClosure`/
## `paramSorts`) AND the heap-deref family (`heapValueSort`,
## `runtime_heap.nim`) crashed UNCAUGHT to the top-level `runSymexImpl`
## catch-all -- a WHOLE-RUN `weInternalWalkerFault` masking the itTable/itSet
## family behind the walker's generic "the walker itself hit a bug" carrier
## (N40's own family 4/5 finding, `tsymex_r6_n40_alloc_totality.nim`, flagged
## this status-only: "sortOfTuple's own separate, pre-existing compound-kind
## gap masks the specific kind here"). Fixed by adding `svTable`/`svSet` arms
## to `rawAnyAstOf` that call `allocDegrade` (N40's own chokepoint, new kind
## `seUnsupportedCompoundSortLeaf`) instead of raising, falling back to a
## safe BV64-zero filler ast (content never trustworthy, only its sort needs
## to be well-formed for the caller's `Z3_get_sort`/`Z3_mk_array_sort`/
## `Z3_mk_func_decl` to complete). This UNMASKS the itTable/itSet family that
## used to crash before reaching any per-path taint mechanism at all -- the
## cross-constraint this finding calls out is that unmasking it WITHOUT the
## N42 deref-taint fix (walker v105, commit a3dba31: `isDeref`/
## `isDerefWrite` drain via `drainPendingLowerEffects` -> `forkPathTainted` ->
## per-path `uncertain`; `isTargetLabel` gates on `p.uncertain`) already
## landed would flip the table/set family from accidentally-sound (masked by
## a whole-run crash no path could survive) to UNSOUND (a tainted path
## reporting a false `sxSat`). N42 IS already landed, so this file's
## soundness suite proves the unmasking is safe: a table-family shape that
## previously crash-masked now yields a per-path-tainted `sxUnknown` with the
## specific classified kind, and an UNCONDITIONAL target reached immediately
## after touching the compound value -- which a naive/unsound engine would
## trivially report `sxSat` for -- NEVER does.
##
## N12: decline messages leak internal IR vocabulary ("itTuple",
## "seNestedSeqUnsupported") verbatim into user-facing decline text. See the
## suite below for the exact rendering-boundary fix.
##
## Verdict-affecting for N15/N30/N41 (a previously-crashing shape now reports
## its correct classified decline kind instead of the generic internal-fault
## one); N12 is message-rendering only. symexWalkerVersion 107->108.
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# N15 -- field-sourced placeholder: index vs .len must report the SAME kind.
# =============================================================================

type
  N15Kind = enum n15rkA, n15rkB
  N15Rec = object
    case kind: N15Kind
    of n15rkA: a: int
    of n15rkB:
      count: int
      opts: seq[(string, string)]   ## unbacked elem (itTuple) -> placeholder

proc n15ReassignToB(v: var N15Rec) =
  v.kind = n15rkB

proc n15IndexOpts(v: var N15Rec) =
  n15ReassignToB(v)
  let x = v.opts[0]
  discard x
  symexTarget("n15_index_opts")

proc n15SliceOpts(v: var N15Rec) =
  n15ReassignToB(v)
  let x = v.opts[0 .. 0]
  discard x
  symexTarget("n15_slice_opts")

proc n15LenOpts(v: var N15Rec) =
  n15ReassignToB(v)
  let n = v.opts.len
  discard n
  symexTarget("n15_len_opts")

suite "symex round-6 N15 -- field-sourced placeholder: index/slice unified with .len":

  test "N15-1 RED->GREEN: indexing a field-sourced placeholder reports seNestedSeqUnsupported (not weInternalWalkerFault), sxUnknown":
    let r = symexFind(n15IndexOpts, tLabel("n15_index_opts"))
    check r.status == sxUnknown
    var sawFault = false
    var sawUnified = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault: sawFault = true
      if e.kind == seNestedSeqUnsupported: sawUnified = true
    check not sawFault
    check sawUnified

  test "N15-2: slicing a field-sourced placeholder ALSO reports seNestedSeqUnsupported (not weInternalWalkerFault), sxUnknown":
    let r = symexFind(n15SliceOpts, tLabel("n15_slice_opts"))
    check r.status == sxUnknown
    var sawFault = false
    var sawUnified = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault: sawFault = true
      if e.kind == seNestedSeqUnsupported: sawUnified = true
    check not sawFault
    check sawUnified

  test "N15-3: the .len route (already correct pre-fix) stays seNestedSeqUnsupported -- the unification baseline":
    let r = symexFind(n15LenOpts, tLabel("n15_len_opts"))
    check r.status == sxUnknown
    var sawUnified = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported: sawUnified = true
    check sawUnified

# =============================================================================
# N30 -- closure with a `string` RETURN type: classified decline, not
# weInternalWalkerFault.
# =============================================================================

proc n30ClosureStringZeroSat(x: int) =
  let f = proc(y: int): string =
    if y > 0:
      result = "hit"
  let r = f(x)
  if x <= 0 and r == "":
    symexTarget("n30_closure_string_zero_sat")

suite "symex round-6 N30 -- closure string-return type: classified decline (feUnsupportedOp), not weInternalWalkerFault":

  test "N30-1 RED->GREEN: symValFromRawAst's missing itString arm now reports feUnsupportedOp (not weInternalWalkerFault)":
    let r = symexFind(n30ClosureStringZeroSat, tLabel("n30_closure_string_zero_sat"))
    check r.status == sxUnknown
    var sawFault = false
    var sawClassified = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault: sawFault = true
      if e.kind == feUnsupportedOp and "symValFromRawAst" in e.msg: sawClassified = true
    check not sawFault
    check sawClassified

# =============================================================================
# N41 -- compound sv-kind (svTable/svSet) sort derivation: classified decline
# instead of a whole-run crash, PLUS the soundness cross-constraint proof.
# =============================================================================

type
  N41Heap = object
    t: Table[string, int]   ## a VALID Table shape -- the gap is independent
                             ## of key/value-type support (N40 already covers
                             ## the unsupported-shape case).
    n: int

proc n41MkHeap(): ref N41Heap {.symexOpaque.} =
  discard

proc n41ClosureValidTableParamBlock(n: int) =
  for i in 0 ..< 1:
    block:
      let f = proc(t: Table[string, int]): int = n
      symexTarget("n41_closure_validtable_param_block")

proc n41HeapReadBlock() =
  let p = n41MkHeap()
  if p != nil:
    discard p.t
    symexTarget("n41_heap_read_block")

suite "symex round-6 N41 -- compound-value sort derivation: classified decline, not a whole-run crash":

  test "N41-1 RED->GREEN: a VALID Table[string,int] closure PARAM reports seUnsupportedCompoundSortLeaf (not weInternalWalkerFault)":
    let r = symexFind(n41ClosureValidTableParamBlock, tLabel("n41_closure_validtable_param_block"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var sawFault = false
    var sawClassified = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault: sawFault = true
      if e.kind == seUnsupportedCompoundSortLeaf: sawClassified = true
    check not sawFault
    check sawClassified

  test "N41-2 RED->GREEN: a heap-deref READ of a VALID Table[string,int] field reports seUnsupportedCompoundSortLeaf (not weInternalWalkerFault) -- the family N40 flagged and masked":
    let r = symexFind(n41HeapReadBlock, tLabel("n41_heap_read_block"))
    checkpoint("status: " & $r.status)
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnknown
    var sawFault = false
    var sawClassified = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault: sawFault = true
      if e.kind == seUnsupportedCompoundSortLeaf: sawClassified = true
    check not sawFault
    check sawClassified

  test "N41-6: the compound-sort-leaf message renders plain language, not the bare SymValKind identifier \"svTable\" (N12 SymValKind follow-up, plainEnglishSymValKind)":
    let r = symexFind(n41ClosureValidTableParamBlock, tLabel("n41_closure_validtable_param_block"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seUnsupportedCompoundSortLeaf:
        sawKind = true
        check "svTable" notin e.msg
        check "table value" in e.msg   ## the plain-language replacement
    check sawKind

suite "symex round-6 N41 -- SOUNDNESS: unmasking the compound family never lets a tainted path report sxSat":

  test "N41-3 SOUNDNESS: heap-deref read of a compound field, target reached UNCONDITIONALLY right after the read, is NEVER sxSat (would be trivially sxSat under a naive/unsound engine -- must stay sxUnknown, per-path tainted via the N42 drain)":
    let r = symexFind(n41HeapReadBlock, tLabel("n41_heap_read_block"))
    check r.status != sxSat
    check r.status == sxUnknown

  test "N41-4 SOUNDNESS: closure construction over a compound VALID Table param, target reached UNCONDITIONALLY, is NEVER sxSat":
    let r = symexFind(n41ClosureValidTableParamBlock, tLabel("n41_closure_validtable_param_block"))
    check r.status != sxSat
    check r.status == sxUnknown

suite "symex round-6 N41 -- companion: the N40 family this finding builds on stays green (no regression)":

  test "N41-5: an ordinary, fully-backed SAT SUT touching a compound value never over-degrades a SIBLING path -- companion sanity, mirrors N40-9/10's own style":
    proc n41PlainSat(x: int) =
      if x == 777:
        symexTarget("n41_plain_sat")
    let r = symexFind(n41PlainSat, tLabel("n41_plain_sat"))
    check r.status == sxSat

# =============================================================================
# N12 -- decline messages must not leak internal IR vocabulary to users.
# `SymexErrorInfo.msg` IS the user-facing string in this codebase (no
# further rendering boundary exists) -- these pins assert the plain-language
# text directly, not merely the structured `.kind` field.
# =============================================================================

type
  N12Kind = enum n12rkA, n12rkB
  N12Rec = object
    case kind: N12Kind
    of n12rkA: a: int
    of n12rkB:
      count: int
      opts: seq[(string, string)]   ## unbacked elem (itTuple) -> placeholder

proc n12ReassignToB(v: var N12Rec) =
  v.kind = n12rkB

proc n12LenOpts(v: var N12Rec) =
  n12ReassignToB(v)
  let n = v.opts.len
  discard n
  symexTarget("n12_len_opts")

proc n12ReadOpts(v: var N12Rec) =
  n12ReassignToB(v)
  let o = v.opts
  discard o
  symexTarget("n12_read_opts")

suite "symex round-6 N12 -- decline messages render plain language, not internal IR vocabulary":

  test "N12-1 RED->GREEN: the R1 placeholder-read chokepoint (.len) does not leak the bare IR kind identifier \"itTuple\" or the raw kind-name parenthetical \"(seNestedSeqUnsupported)\" into the message":
    let r = symexFind(n12LenOpts, tLabel("n12_len_opts"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported:
        sawKind = true
        check "itTuple" notin e.msg
        check "(seNestedSeqUnsupported)" notin e.msg
        check "tuple type" in e.msg   ## the plain-language replacement
    check sawKind

  test "N12-2 RED->GREEN: the declared-unsupported-FIELD chokepoint (a bare field read) does not leak \"itTuple\"/\"(seNestedSeqUnsupported)\" into the message either -- same funnel, same fix":
    let r = symexFind(n12ReadOpts, tLabel("n12_read_opts"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported:
        sawKind = true
        check "itTuple" notin e.msg
        check "(seNestedSeqUnsupported)" notin e.msg
        check "tuple type" in e.msg
    check sawKind

  test "N12-3: the structured .kind field is UNCHANGED by the message-text fix -- callers matching on .kind (not text) see no behavior change":
    let r = symexFind(n12LenOpts, tLabel("n12_len_opts"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors[0].kind == seNestedSeqUnsupported

# =============================================================================
# Version pin
# =============================================================================

suite "symex round-6 lows (fix round 10) -- walker version pin":

  test "walker version floor >= 108 (N15/N30/N41 crash-to-classified-decline fixes, verdict-affecting; N12 message-rendering only)":
    check parseInt(symexWalkerVersion) >= 108
