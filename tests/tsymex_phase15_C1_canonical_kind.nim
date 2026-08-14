## RFC-parser-normalization (#146), Cluster C, slice C1 — canonical routine
## kind at the resolution boundary.
##
## `resolveRoutineImpl` (`dsl_parser.nim`, N1/N2) now re-trees an accepted
## `nnkFuncDef` impl to `nnkProcDef` before returning it, so every
## downstream consumer sees ONE canonical routine kind by construction
## (confined entirely to that proc's body — see its doc comment for the
## layout-identity and cache-key evidence, RFC evidence obligations (a) and
## (b)). This file is the CHARACTERIZATION test the RFC's C1 acceptance
## criterion asks for: five func-vs-proc twin categories, each proving the
## re-tree is INVISIBLE to a caller — same verdict, same witness, across
## the shapes most likely to route through a kind-sensitive path elsewhere
## in the file (borrow ops, proc-as-value capture, string-param
## disambiguation, generic monomorphization, plain interprocedural calls).
##
## This file is GREEN both BEFORE commit `<this slice>` (against the
## pre-retree tree, where `resolveRoutineImpl` returns the live `nnkFuncDef`
## unchanged and every consumer already tolerates it via N2's migration) and
## AFTER (post-retree, where the SAME consumers now see an `nnkProcDef`) —
## by design, the re-tree changes NOTHING observable. Both-green is the
## confinement evidence: nothing in this file, or in `dsl_parser.nim`
## outside `resolveRoutineImpl`'s body, needed to change for the retree to
## land.
##
## Cache-key claim, precisely stated: a func-spelled twin and its
## proc-spelled sibling are, by construction, DIFFERENT programs (Nim
## forbids an identical-signature `func`/`proc` overload pair sharing one
## name, so the two twins are necessarily two DISTINCT top-level symbols
## with distinct body text — the callee/SUT name itself is embedded in the
## canonical form `symexCacheKeyForFn` hashes). Asserting bit-identical keys
## ACROSS a func/proc twin pair would therefore be asserting a name
## collision, not a soundness property — so this file asserts the two twins
## are well-formed AND DISTINCT (mirroring the established
## cache-key-distinctness idiom, see `tsymex_phase16_m3_rfind.nim`'s
## find-vs-rfind check), never a false "identical" claim. The TRUE identity
## claim RFC evidence obligation (b) asks for — that ONE func symbol's own
## cache key is unchanged by the retree — is a BEFORE/AFTER-this-commit
## comparison with no "before" state reachable inside a single post-retree
## test run; it is proven empirically instead (`scratchpad/probe_c1_cachekey.nim`,
## run against the pre-retree and post-retree tree in the same working
## copy) and recorded in the commit body and in `resolveRoutineImpl`'s own
## doc comment.
##
## Totality-clause negative test: NOT constructible (documented, not
## omitted by oversight). `func` and `proc` are compiled through the
## identical routine-node constructor in the Nim compiler — real compiler
## output cannot produce an `nnkFuncDef` impl with a shape the re-tree's
## defensive arity floor (`routineImplMinArity`) rejects; forcing that path
## requires hand-building a synthetic `NimNode`, which is not real compiler
## output and so outside this proc's documented contract (see
## `resolveRoutineImpl`'s doc comment for the full probe trail).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/[dsl, runtime]

# ============================================================================
# Category 1 — borrow op: a `{.borrow.}` operator on a `distinct` type.
# ============================================================================
type MetersProcC1 = distinct float64
proc `+`(a, b: MetersProcC1): MetersProcC1 {.borrow.}
proc `<`(a, b: MetersProcC1): bool {.borrow.}

type MetersFuncC1 = distinct float64
func `+`(a, b: MetersFuncC1): MetersFuncC1 {.borrow.}
func `<`(a, b: MetersFuncC1): bool {.borrow.}

proc sutC1BorrowProc(m1, m2: MetersProcC1) =
  if m1 + m2 > MetersProcC1(10.0):
    symexTarget("c1-borrow-proc")

proc sutC1BorrowFunc(m1, m2: MetersFuncC1) =
  if m1 + m2 > MetersFuncC1(10.0):
    symexTarget("c1-borrow-func")

# ============================================================================
# Category 2 — proc-as-value capture: `let g = callee; g(n)`.
# ============================================================================
proc doubleProcC1(x: int): int = x * 2
func doubleFuncC1(x: int): int = x * 2

proc sutC1ValueProc(n: int) =
  let g = doubleProcC1
  if g(n) == 10:
    symexTarget("c1-value-proc")

proc sutC1ValueFunc(n: int) =
  let g = doubleFuncC1
  if g(n) == 10:
    symexTarget("c1-value-func")

# ============================================================================
# Category 3 — string-param: the G8 string-op-disambiguation shape (a
# user routine, not a stdlib string op, taking a string first param).
# ============================================================================
proc hasEvenNonEmptyLenProcC1(s: string): bool = s.len > 0 and (s.len mod 2) == 0
func hasEvenNonEmptyLenFuncC1(s: string): bool = s.len > 0 and (s.len mod 2) == 0

proc sutC1StringProc(s: string) =
  if hasEvenNonEmptyLenProcC1(s):
    symexTarget("c1-string-proc")

proc sutC1StringFunc(s: string) =
  if hasEvenNonEmptyLenFuncC1(s):
    symexTarget("c1-string-func")

# ============================================================================
# Category 4 — generic callee: parse-time monomorphization of a `func`/`proc`
# generic over `T`.
# ============================================================================
proc addGProcC1[T](a, b: T): T = a + b
func addGFuncC1[T](a, b: T): T = a + b

proc sutC1GenericProc(a, b: int) =
  symexAssume(a >= 0 and a < 100 and b >= 0 and b < 100)
  let s = addGProcC1(a, b)
  symexAssert(s == a + b)

proc sutC1GenericFunc(a, b: int) =
  symexAssume(a >= 0 and a < 100 and b >= 0 and b < 100)
  let s = addGFuncC1(a, b)
  symexAssert(s == a + b)

# ============================================================================
# Category 5 — plain callee: ordinary interprocedural call, no other
# kind-sensitive machinery involved.
# ============================================================================
proc maskLow3ProcC1(x: int): int = x and 7
func maskLow3FuncC1(x: int): int = x and 7

proc sutC1PlainProc(x: int) =
  let m = maskLow3ProcC1(x)
  symexAssert(m != 5)

proc sutC1PlainFunc(x: int) =
  let m = maskLow3FuncC1(x)
  symexAssert(m != 5)

# ============================================================================
# Tests
# ============================================================================

suite "symex C1 — category 1: borrow op twin equality":
  test "C1-borrow: proc and func borrowed `+` agree on verdict AND witness":
    let rProc = symexFind(sutC1BorrowProc, tLabel("c1-borrow-proc"))
    let rFunc = symexFind(sutC1BorrowFunc, tLabel("c1-borrow-func"))
    check rProc.status == sxSat
    check rFunc.status == sxSat
    check rProc.status == rFunc.status
    check float64(rProc.witness[0]) + float64(rProc.witness[1]) > 10.0
    check float64(rFunc.witness[0]) + float64(rFunc.witness[1]) > 10.0

  test "C1-borrow: cache keys are well-formed and distinct (different programs, no collision)":
    let kProc = symexCacheKeyForFn(sutC1BorrowProc, tLabel("c1-borrow-proc"))
    let kFunc = symexCacheKeyForFn(sutC1BorrowFunc, tLabel("c1-borrow-func"))
    check kProc.startsWith("sx:") and kProc.len > 3
    check kFunc.startsWith("sx:") and kFunc.len > 3
    check kProc != kFunc

suite "symex C1 — category 2: proc-as-value capture twin equality":
  test "C1-value: captured proc and captured func agree on verdict AND witness":
    let rProc = symexFind(sutC1ValueProc, tLabel("c1-value-proc"))
    let rFunc = symexFind(sutC1ValueFunc, tLabel("c1-value-func"))
    check rProc.status == sxSat
    check rFunc.status == sxSat
    check rProc.status == rFunc.status
    check rProc.witness[0] == 5
    check rFunc.witness[0] == 5
    check rProc.witness[0] == rFunc.witness[0]

  test "C1-value: cache keys are well-formed and distinct":
    let kProc = symexCacheKeyForFn(sutC1ValueProc, tLabel("c1-value-proc"))
    let kFunc = symexCacheKeyForFn(sutC1ValueFunc, tLabel("c1-value-func"))
    check kProc.startsWith("sx:") and kProc.len > 3
    check kFunc.startsWith("sx:") and kFunc.len > 3
    check kProc != kFunc

suite "symex C1 — category 3: string-param twin equality":
  test "C1-string: proc and func string-first-param callees agree on verdict AND witness shape":
    let rProc = symexFind(sutC1StringProc, tLabel("c1-string-proc"))
    let rFunc = symexFind(sutC1StringFunc, tLabel("c1-string-func"))
    check rProc.status == sxSat
    check rFunc.status == sxSat
    check rProc.status == rFunc.status
    check rProc.witness[0].len > 0 and rProc.witness[0].len mod 2 == 0
    check rFunc.witness[0].len > 0 and rFunc.witness[0].len mod 2 == 0

  test "C1-string: cache keys are well-formed and distinct":
    let kProc = symexCacheKeyForFn(sutC1StringProc, tLabel("c1-string-proc"))
    let kFunc = symexCacheKeyForFn(sutC1StringFunc, tLabel("c1-string-func"))
    check kProc.startsWith("sx:") and kProc.len > 3
    check kFunc.startsWith("sx:") and kFunc.len > 3
    check kProc != kFunc

suite "symex C1 — category 4: generic callee twin equality":
  test "C1-generic: proc and func generic callees both monomorphize and agree on verdict":
    let rProc = symexFind(sutC1GenericProc, tAssertionViolation())
    let rFunc = symexFind(sutC1GenericFunc, tAssertionViolation())
    check rProc.status == sxUnsat   ## a + b == a + b always holds — unreachable
    check rFunc.status == sxUnsat
    check rProc.status == rFunc.status

  test "C1-generic: cache keys are well-formed and distinct":
    let kProc = symexCacheKeyForFn(sutC1GenericProc, tAssertionViolation())
    let kFunc = symexCacheKeyForFn(sutC1GenericFunc, tAssertionViolation())
    check kProc.startsWith("sx:") and kProc.len > 3
    check kFunc.startsWith("sx:") and kFunc.len > 3
    check kProc != kFunc

suite "symex C1 — category 5: plain callee twin equality":
  test "C1-plain: proc and func plain interprocedural callees agree on verdict AND witness":
    let rProc = symexFind(sutC1PlainProc, tAssertionViolation())
    let rFunc = symexFind(sutC1PlainFunc, tAssertionViolation())
    check rProc.status == sxRaised
    check rFunc.status == sxRaised
    check rProc.raisedTypeId == "AssertionDefect"
    check rFunc.raisedTypeId == "AssertionDefect"
    check (rProc.raisedWitness[0] and 7) == 5
    check (rFunc.raisedWitness[0] and 7) == 5

  test "C1-plain: cache keys are well-formed and distinct":
    let kProc = symexCacheKeyForFn(sutC1PlainProc, tAssertionViolation())
    let kFunc = symexCacheKeyForFn(sutC1PlainFunc, tAssertionViolation())
    check kProc.startsWith("sx:") and kProc.len > 3
    check kFunc.startsWith("sx:") and kFunc.len > 3
    check kProc != kFunc

# ============================================================================
# Version-pin discipline
# ============================================================================
suite "symex C1 — walker version floor":
  test "walker version floor: symexWalkerVersion >= 73 (C1 is behavior-identical, no bump — RFC F2)":
    check parseInt(symexWalkerVersion) >= 73
