## Round-6 Bucket-2 opening fix-slice -- N29 root-cause pin, walker v120.
##
## ---- Background ---------------------------------------------------------
## The ledger long carried N29 as "HOF lambda Z3 domain-sort mismatch" --
## every investigation since N16 observed the failure surface only inside a
## HOF-shaped test file (`tsymex_phase15_C4_hof.nim`'s C4-1/C4-1b) and
## inferred a closure-funcSym cause without tracing the actual raise site.
##
## Direct stack instrumentation (this slice, reverted before landing) proved
## the real mechanism has NOTHING to do with closures: `lowerSeqLit`'s
## empty-literal branch (Round-6 B6 rider, `84213d9`) built an inert
## `Z3Array[Int, Bool]`-sorted placeholder for EVERY empty `@[]` literal,
## INCLUDING backed element types like `seq[int]`. The rider's own
## soundness argument ("a length-0 seq's data is never READ") holds for
## reads but not for a subsequent `.add`/`.insert` MUTATION:
## `iekSeqAdd` (and its siblings) unconditionally `wrap()` `seqDataRaw` as
## `Z3Array[Z3Int, <elemTy's declared sort>]` with NO validation, so the
## ordinary `var xs: seq[int] = @[]; xs.add(a)` idiom reinterpreted the
## Bool-sorted placeholder as a BitVec64-ranged array and Z3 rejected the
## resulting `store()`: "domain sort (_ BitVec 64) and parameter sort Bool
## do not match". This file pins the root cause DIRECTLY -- no closures, no
## HOF dispatch, no `filter`/`map` anywhere -- to prove the fix belongs at
## the seq-literal chokepoint, not the closure machinery.
##
## See `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
## fix itself (`lowerSeqLit` now allocates a REAL backed-sort empty array
## for a BACKED `elemTy`, falling back to the inert placeholder only for a
## genuinely unbacked one).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# 1. Root-cause isolation: `seq[int]`, no closures at all.
# =============================================================================

proc sutIntLitAdd(a: int) =
  var xs: seq[int] = @[]
  xs.add a
  if xs.len == 1 and xs[0] == 5:
    symexTarget("intlit_add_sat")

proc sutIntLitAddUnsat(a: int) =
  var xs: seq[int] = @[]
  xs.add a
  if xs.len == 1 and xs[0] == 5 and xs[0] == 6:
    symexTarget("intlit_add_unsat")

suite "symex N29 -- seq[int] literal-then-add, root cause isolated (no closures)":

  test "N29-1: `var xs: seq[int] = @[]; xs.add(a)` then index-read proves sxSat, witness a == 5":
    let r = symexFind(sutIntLitAdd, tLabel("intlit_add_sat"))
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.witness[0] == 5

  test "N29-2 UNSAT companion: a contradictory post-add read stays unreachable":
    let r = symexFind(sutIntLitAddUnsat, tLabel("intlit_add_unsat"))
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnsat
    check r.errors.len == 0

# =============================================================================
# 2. Second backed element kind: `seq[bool]` -- proves the fix is not
#    itInt-width-specific (the `itBool` arm of `iekSeqAdd`/`allocateSeqDataRaw`
#    exercises a completely different Z3Array instantiation).
# =============================================================================

proc sutBoolLitAdd(a: bool) =
  var xs: seq[bool] = @[]
  xs.add a
  if xs.len == 1 and xs[0] == true:
    symexTarget("boollit_add_sat")

suite "symex N29 -- seq[bool] literal-then-add":

  test "N29-3: `var xs: seq[bool] = @[]; xs.add(a)` then index-read proves sxSat, witness a == true":
    let r = symexFind(sutBoolLitAdd, tLabel("boollit_add_sat"))
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.witness[0] == true

# =============================================================================
# 3. Multiple sequential `.add` calls -- the ORIGINAL C4-1/C4-1b shape
#    (three `.add`s before any read), pinned independent of the HOF/closure
#    machinery those files layer on top.
# =============================================================================

proc sutThreeAdds(a, b, c: int) =
  var xs: seq[int] = @[]
  xs.add a
  xs.add b
  xs.add c
  if xs.len == 3 and xs[0] == 1 and xs[1] == 2 and xs[2] == 3:
    symexTarget("three_adds_sat")

suite "symex N29 -- three sequential .add calls off an empty literal":

  test "N29-4: `xs.add a; xs.add b; xs.add c` then a full-content read proves sxSat":
    let r = symexFind(sutThreeAdds, tLabel("three_adds_sat"))
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.witness[0] == 1
    check r.witness[1] == 2
    check r.witness[2] == 3

# =============================================================================
# 4. Regression guard: a genuinely UNBACKED element type (`seq[(string,
#    string)]`) still declines classified on mutation -- the B6 rider's
#    placeholder is UNCHANGED for this case, and `iekSeqAdd`'s own unbacked-
#    elem `else` arm (not the unchecked-wrap fast path) must still catch it.
#    Never a crash, never the raw Z3 sort-mismatch.
# =============================================================================

proc sutUnbackedLitAdd(a: string, b: string) =
  var pairs: seq[(string, string)] = @[]
  pairs.add (a, b)
  if pairs.len > 0:
    symexTarget("unbacked_add")

suite "symex N29 -- unbacked seq[(string,string)] literal-then-add: unaffected, still declines classified":

  test "N29-5: `.add` on an unbacked-element empty literal stays an honest classified decline, never a crash":
    let r = symexFind(sutUnbackedLitAdd, tLabel("unbacked_add"))
    check r.status == sxUnknown
    var sawClassified = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.severity == sevError:
        sawClassified = true
    check sawClassified

# =============================================================================
# 5. Sanity: an empty literal that is NEVER mutated behaves exactly as
#    before (the B6 rider's original scope, untouched by this fix).
# =============================================================================

proc sutEmptyNeverMutated(a: int) =
  var xs: seq[int] = @[]
  discard a
  if xs.len == 0:
    symexTarget("empty_never_mutated")

suite "symex N29 -- empty literal never mutated: unaffected by this fix":

  test "N29-6: an unmutated empty seq[int] literal still proves sxSat on .len == 0":
    let r = symexFind(sutEmptyNeverMutated, tLabel("empty_never_mutated"))
    for e in r.errors: checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

# =============================================================================
# Version pin
# =============================================================================

suite "symex N29 -- walker version pin":

  test "walker version floor >= 120 (N29: lowerSeqLit empty-literal backed-sort fix)":
    check parseInt(symexWalkerVersion) >= 120
