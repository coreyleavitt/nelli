## RFC-parser-normalization (#146), Cluster N, slice N1 — resolution
## helpers + `symex.nim` migration.
##
## N1 introduces the shared nil-core `resolveRoutineImpl` (`getImpl` +
## `kind in walkableRoutineKinds`, never errors) and two policy wrappers
## over it: `resolveEntryImpl` (hard-error) and `parseEntryImpl`
## (`resolveEntryImpl` + `parseProc`). All NINE `symex.nim` entry macros
## (`symexForAll`, `symexFind`, `assertCoveredBy`, `symexCacheKeyForFn`,
## `saveSymexWitness`, `loadSymexWitnesses`, `saveSymexVerdict`,
## `loadSymexVerdict`, `symexFindAllWitnesses`) now route through one of
## these two wrappers instead of nine separate `getImpl` + bare-kind-gate +
## `error(...)` copies.
##
## This is a behavior-identical consolidation refactor (no `symexWalkerVersion`
## bump) with ONE deliberate exception (RFC round-2 §Resolved forks F4):
## `symexForAll`'s historical `" for \`fn\`"` error-text suffix is dropped so
## all nine macros share identical error text. No test or downstream harness
## depends on the exact compile-error string, so this file — like the
## pre-existing `not compiles(...)` idiom used elsewhere in the suite (see
## `tsymex_phase12_witnesses.nim`) — pins BEHAVIOR (rejected vs accepted),
## never the message text.
##
## This file is written FIRST (TDD cycle 1) and is green against BOTH the
## pre-refactor base (`3994272`, N0) and the post-refactor tree: every
## assertion here pins pre-existing hard-error POLICY (Invariant-3's
## `resolveEntryImpl`-class wrapper), not new behavior N1 introduces. If a
## future slice's migration changes what gets rejected here, that is a
## regression, not an update.
##
## Negative coverage (excluded-kind behavior — an explicit RFC N1
## acceptance criterion, not an assumption): a `template` symbol, a
## `let`-bound closure/lambda variable, and a first-class `{.closure.}`
## `iterator` symbol are each non-`{nnkProcDef, nnkFuncDef}` impls, so
## `resolveRoutineImpl` returns `nil` for all three and the hard-error
## wrapper rejects them at macro-expansion time — a genuine compile
## failure, pinned via `not compiles(...)`.
##
## Review finding M4 (RFC #146 round 1): the original slice pinned this
## only against two representative entry macros (`symexFind`, a bare
## `resolveEntryImpl` consumer, and `symexCacheKeyForFn`, a
## `parseEntryImpl` consumer). All NINE entry macros route through one
## of the same two wrappers over the same nil-core, so this file now
## pins the identical rejection against the remaining seven:
## `symexForAll`, `assertCoveredBy`, `saveSymexWitness`,
## `loadSymexWitnesses`, `saveSymexVerdict`, `loadSymexVerdict`, and
## `symexFindAllWitnesses`. `resolveEntryImpl` hard-errors before any of
## these macros emits code that touches the (real, in-memory) database —
## rejection fires at macro-expansion time, so `not compiles(...)` never
## runs the emitted body, making these assertions side-effect-free even
## for the save/load macros.
##
## Positive coverage: an ordinary `proc` AND an ordinary `func` are BOTH
## still accepted (behavior identical to pre-N1) by `symexFind` and
## `symexCacheKeyForFn`. A `func` cannot call the side-effectful
## `symexTarget`/`symexAssert` markers (`{.noSideEffect.}`), so — mirroring
## `tests/tsymex_funcdef_callee.nim`'s established pattern — the `func` SUT
## uses a raw `doAssert`, which the walker surfaces as a reachable
## `AssertionDefect` raise (`sxRaised`) when targeted with
## `tAssertionViolation()`.

import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/canonicalize

# ============================================================================
# Fixtures — one non-routine symbol per excluded kind, module scope so
# `getImpl` can resolve them.
# ============================================================================

template doubleTemplate(x: int): int = x * 2
  ## A `template` symbol. Templates are not `{nnkProcDef, nnkFuncDef}` —
  ## `getImpl` on this symbol yields `nnkTemplateDef`.

iterator twoElemsIter(): int {.closure.} =
  ## A first-class (`{.closure.}`) `iterator` symbol — referenceable bare as
  ## a value (the same shape `tsymex_a3_closure_iterators.nim`'s T7 case
  ## uses: `let it = countUpIter`), so it reaches macro-argument
  ## typechecking as a real symbol whose `getImpl` yields `nnkIteratorDef`.
  yield 1
  yield 2

let letBoundLambda = proc(x: int): int = x * 2
  ## A `let`-bound closure/lambda variable. `letBoundLambda`'s `getImpl`
  ## yields the `let` binding's `nnkIdentDefs`, not a routine def — the
  ## exact C3 proc-as-value distinction `dsl_parser.nim`'s `symKind(n) in
  ## {nskProc, nskFunc}` gate exists to draw (this symbol is `nskLet`).

proc sutPlainProc(n: int) =
  doAssert n != 7, "reachable for exactly one input"

func sutPlainFunc(n: int) =
  doAssert n != 7, "reachable for exactly one input"

# ============================================================================
# Negative: excluded-kind rejection (resolveEntryImpl's hard-error policy).
# ============================================================================

suite "symex N1 — excluded-kind rejection via symexFind (bare resolveEntryImpl)":

  test "a template symbol is rejected by symexFind":
    check not compiles(symexFind(doubleTemplate, tLabel("x")))

  test "a let-bound closure/lambda var is rejected by symexFind":
    check not compiles(symexFind(letBoundLambda, tLabel("x")))

  test "an iterator symbol is rejected by symexFind":
    check not compiles(symexFind(twoElemsIter, tLabel("x")))

suite "symex N1 — excluded-kind rejection via symexCacheKeyForFn (parseEntryImpl)":

  test "a template symbol is rejected by symexCacheKeyForFn":
    check not compiles(symexCacheKeyForFn(doubleTemplate, tLabel("x")))

  test "a let-bound closure/lambda var is rejected by symexCacheKeyForFn":
    check not compiles(symexCacheKeyForFn(letBoundLambda, tLabel("x")))

  test "an iterator symbol is rejected by symexCacheKeyForFn":
    check not compiles(symexCacheKeyForFn(twoElemsIter, tLabel("x")))

suite "symex N1 — excluded-kind rejection via symexForAll (bare resolveEntryImpl)":

  test "a template symbol is rejected by symexForAll":
    check not compiles(symexForAll(integers(0, 1000), doubleTemplate,
                                    inMemoryDatabase()))

  test "a let-bound closure/lambda var is rejected by symexForAll":
    check not compiles(symexForAll(integers(0, 1000), letBoundLambda,
                                    inMemoryDatabase()))

  test "an iterator symbol is rejected by symexForAll":
    check not compiles(symexForAll(integers(0, 1000), twoElemsIter,
                                    inMemoryDatabase()))

suite "symex N1 — excluded-kind rejection via assertCoveredBy (parseEntryImpl)":

  test "a template symbol is rejected by assertCoveredBy":
    check not compiles(assertCoveredBy(doubleTemplate, tLabel("x")))

  test "a let-bound closure/lambda var is rejected by assertCoveredBy":
    check not compiles(assertCoveredBy(letBoundLambda, tLabel("x")))

  test "an iterator symbol is rejected by assertCoveredBy":
    check not compiles(assertCoveredBy(twoElemsIter, tLabel("x")))

suite "symex N1 — excluded-kind rejection via saveSymexWitness (parseEntryImpl)":

  test "a template symbol is rejected by saveSymexWitness":
    check not compiles(saveSymexWitness(inMemoryDatabase(), doubleTemplate,
                          tLabel("x"), defaultSymexSettings(),
                          SymexFinding(status: sfUnsat, z3Version: z3FullVersion())))

  test "a let-bound closure/lambda var is rejected by saveSymexWitness":
    check not compiles(saveSymexWitness(inMemoryDatabase(), letBoundLambda,
                          tLabel("x"), defaultSymexSettings(),
                          SymexFinding(status: sfUnsat, z3Version: z3FullVersion())))

  test "an iterator symbol is rejected by saveSymexWitness":
    check not compiles(saveSymexWitness(inMemoryDatabase(), twoElemsIter,
                          tLabel("x"), defaultSymexSettings(),
                          SymexFinding(status: sfUnsat, z3Version: z3FullVersion())))

suite "symex N1 — excluded-kind rejection via loadSymexWitnesses (parseEntryImpl)":

  test "a template symbol is rejected by loadSymexWitnesses":
    check not compiles(loadSymexWitnesses(inMemoryDatabase(), doubleTemplate,
                          tLabel("x"), defaultSymexSettings()))

  test "a let-bound closure/lambda var is rejected by loadSymexWitnesses":
    check not compiles(loadSymexWitnesses(inMemoryDatabase(), letBoundLambda,
                          tLabel("x"), defaultSymexSettings()))

  test "an iterator symbol is rejected by loadSymexWitnesses":
    check not compiles(loadSymexWitnesses(inMemoryDatabase(), twoElemsIter,
                          tLabel("x"), defaultSymexSettings()))

suite "symex N1 — excluded-kind rejection via saveSymexVerdict (parseEntryImpl)":

  test "a template symbol is rejected by saveSymexVerdict":
    check not compiles(saveSymexVerdict(inMemoryDatabase(), doubleTemplate,
                          tLabel("x"), defaultSymexSettings(), sfUnsat))

  test "a let-bound closure/lambda var is rejected by saveSymexVerdict":
    check not compiles(saveSymexVerdict(inMemoryDatabase(), letBoundLambda,
                          tLabel("x"), defaultSymexSettings(), sfUnsat))

  test "an iterator symbol is rejected by saveSymexVerdict":
    check not compiles(saveSymexVerdict(inMemoryDatabase(), twoElemsIter,
                          tLabel("x"), defaultSymexSettings(), sfUnsat))

suite "symex N1 — excluded-kind rejection via loadSymexVerdict (parseEntryImpl)":

  test "a template symbol is rejected by loadSymexVerdict":
    check not compiles(loadSymexVerdict(inMemoryDatabase(), doubleTemplate,
                          tLabel("x"), defaultSymexSettings()))

  test "a let-bound closure/lambda var is rejected by loadSymexVerdict":
    check not compiles(loadSymexVerdict(inMemoryDatabase(), letBoundLambda,
                          tLabel("x"), defaultSymexSettings()))

  test "an iterator symbol is rejected by loadSymexVerdict":
    check not compiles(loadSymexVerdict(inMemoryDatabase(), twoElemsIter,
                          tLabel("x"), defaultSymexSettings()))

suite "symex N1 — excluded-kind rejection via symexFindAllWitnesses (parseEntryImpl)":

  test "a template symbol is rejected by symexFindAllWitnesses":
    check not compiles(symexFindAllWitnesses(doubleTemplate, inMemoryDatabase()))

  test "a let-bound closure/lambda var is rejected by symexFindAllWitnesses":
    check not compiles(symexFindAllWitnesses(letBoundLambda, inMemoryDatabase()))

  test "an iterator symbol is rejected by symexFindAllWitnesses":
    check not compiles(symexFindAllWitnesses(twoElemsIter, inMemoryDatabase()))

# ============================================================================
# Positive smoke: proc AND func still accepted (behavior identical).
# ============================================================================

suite "symex N1 — positive smoke: proc and func both still accepted":

  test "symexFind still accepts a plain proc":
    let r = symexFind(sutPlainProc, tAssertionViolation())
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check r.raisedWitness[0] == 7

  test "symexFind still accepts a plain func":
    let r = symexFind(sutPlainFunc, tAssertionViolation())
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check r.raisedWitness[0] == 7

  test "symexCacheKeyForFn still accepts a plain proc":
    let k = symexCacheKeyForFn(sutPlainProc, tAssertionViolation())
    check k.len > 0

  test "symexCacheKeyForFn still accepts a plain func":
    let k = symexCacheKeyForFn(sutPlainFunc, tAssertionViolation())
    check k.len > 0

# ============================================================================
# Version-pin discipline
# ============================================================================

suite "symex N1 — walker version floor":
  test "walker version floor: symexWalkerVersion >= 71 (N1 is behavior-identical, no bump)":
    check parseInt(symexWalkerVersion) >= 71
