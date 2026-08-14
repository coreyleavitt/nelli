## RFC-parser-normalization (#146), Cluster N, slice N0 — complete the
## `nnkFuncDef` widening (#147).
##
## `799b0bc` (walker v70) widened 19 sites so `func` is accepted everywhere
## `proc` is, but a grep-based site audit (RFC round 1/2) found THREE live
## unwidened sites in `dsl_parser.nim`, all Invariant-3-class policy gates
## that had been missed because the census only looked for bare `nnkProcDef`
## node-kind comparisons, not the second bare-kind class (`nsk*` SYMBOL-kind
## gates):
##
##   1. `borrowInfoFor` (:855) — `impl.kind != nnkProcDef` in front of the
##      already-widened `hasBorrowPragma`. A `func` borrow operator
##      classified `isBorrow: false` and fell to the ORDINARY infix path.
##   2. C3 proc-as-value (:1048 AND :1050) — the gate that actually excludes
##      a `func`-valued capture is `symKind(n) == nskProc` at :1048 (`func`
##      symbols are the DISTINCT `nskFunc` kind); `impl.kind == nnkProcDef`
##      at :1050 is unreachable for `func` until :1048 widens first.
##   3. G8 string-op disambiguation (:2083) — `calleeSym.getImpl.kind ==
##      nnkProcDef` is a POSITIVE-match gate (not an exclusion), so a user
##      `func` with a string-typed first param fell THROUGH to the
##      unregistered-stdlib-string-op degrade instead of falling through to
##      the user-proc call path.
##
## Full-repo bare-kind audit (grep, not list — the house rule this slice
## institutionalizes), run PRE-fix on 799b0bc-era HEAD:
##
##   node-kind gates — bare `nnkProcDef` comparisons/membership NOT already
##   paired with `nnkFuncDef` (`grep -rn "nnkProcDef" src/nelli/`, filtered
##   to lines that do NOT also mention `nnkFuncDef`):
##     - src/nelli/smt/dsl_parser.nim:855   (borrowInfoFor — fixed here)
##     - src/nelli/smt/dsl_parser.nim:1050  (C3 impl.kind — fixed here)
##     - src/nelli/smt/dsl_parser.nim:2083  (G8 getImpl.kind — fixed here)
##     - src/nelli/mutation.nim:123         (`{nnkLambda, nnkProcDef,
##       nnkDo}` — documented §Non-goals exclusion: a `func` there is
##       rejected LOUDLY by `expectKind`, not silently; a different
##       subsystem with its own vocabulary, out of this RFC's scope)
##   (src/nelli/coverage.nim:292 already reads `{nnkProcDef, nnkFuncDef,
##   nnkLambda}` — not a bare/unwidened site; also a documented §Non-goals
##   exclusion since it belongs to a different subsystem.)
##
##   symbol-kind gates — `nskProc`/`nskFunc` (`grep -rn "nskProc\|nskFunc"
## src/nelli/`):
##     - src/nelli/smt/dsl_parser.nim:1048  (C3 symKind(n) — fixed here;
##       the only site in the repo census, per the RFC)
##
## Post-fix residue (expected, unchanged by this slice): `coverage.nim:292`
## and `mutation.nim:123` only — both documented §Non-goals exclusions.
## Everything else under `src/nelli/` is either already-widened (the 19
## `799b0bc` sites) or fixed by this slice.
##
## Test framing per the RFC's round-2 correction (two different framings for
## three sites, NOT "RED test each"):
##   - Cycle 1 (C3) and Cycle 2 (G8): RED-first. Pre-fix, both degrade to a
##     WRONG classified verdict; the committed test asserts the CORRECT
##     post-fix verdict, and the pre-fix observed behavior is recorded in
##     each cycle's comment below (observed by running this file against
##     unpatched HEAD before the three-site widen was applied).
##   - Cycle 3 (borrowInfoFor): a CHARACTERIZATION PIN, not a promised RED.
##     Ground truth (RFC §Ground truth 1, round-2 severity correction): the
##     fallthrough is verdict/witness-INERT at HEAD — the ordinary
##     arithmetic/comparison infix arms eject both operands unconditionally
##     regardless of the borrow gate, computing the identical base result;
##     the only delta from the missed widen is the skipped `reboxDistinct`,
##     whose minted distinct const is never constrained and never read. So
##     this test pins `proc`-vs-`func` borrow TWIN EQUALITY (verdict AND
##     witness, one arithmetic-borrow pair and one comparison-borrow pair)
##     and is expected GREEN both BEFORE and AFTER the one-line :855 widen —
##     it would only go RED if a rebox-sensitive divergence existed after
##     all, which it does not (confirmed: green pre-fix, still green
##     post-fix, run both backends).
##
## `symexWalkerVersion` bumps 70 -> 71 in lockstep (Cluster N0 is `Ver: SW`
## — this slice changes VERDICTS for previously-degraded `func` programs:
## the C3 and G8 fixes turn a classified `sxUnknown` into a real verdict).
## The canonical `tsymex_phase15_CR2_cachekey.nim` `==` pin is updated in
## this same slice (see that file). This file additionally carries a `>=`
## floor pin (house convention for incidental, non-canonical pins).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/[dsl, runtime]

# ============================================================================
# Cycle 1 — C3 proc-as-value: a `func`-valued capture.
# ============================================================================
#
# Mirrors tests/tsymex_phase15_C3_proc_as_value.nim's SUT 1 exactly, with
# `func` in place of `proc` for BOTH the captured routine and the direct-call
# reference twin, so the two spellings prove the SAME verdict/witness the
# way the original C3 test proves `proc`-vs-value-vs-direct transparency.
#
# PRE-FIX OBSERVED (traced per RFC §Ground truth, confirmed by running this
# test against unpatched HEAD before the :1048/:1050 widen): `symKind(n) ==
# nskProc` at :1048 excludes the `func` symbol (`func` is `nskFunc`, not
# `nskProc`), so the capture falls to bare `mkVar` instead of
# `parseProcAsValue`. At walk time `g(n)` looks up an unbound env entry ->
# `KeyError` -> the outermost classified catch-all (:1022-1032 era mechanism)
# -> `sxUnknown` carrying `weInternalWalkerFault`. `sutFuncDirectCall` (which
# never goes through the value-capture arm) is unaffected and proves `sxSat`
# pre-fix already — only the VALUE-capture spelling was broken.
func doubleFunc(x: int): int = x * 2

proc sutFuncAsValue(n: int) =
  let g = doubleFunc
  if g(n) == 10:
    symexTarget("func-as-value")

proc sutFuncDirectCall(n: int) =
  if doubleFunc(n) == 10:
    symexTarget("func-direct")

suite "symex N0 cycle 1 — C3 widened for func-valued capture":
  test "N0-C3: a func-valued capture produces the SAME witness as calling the func directly":
    let viaValue  = symexFind(sutFuncAsValue, tLabel("func-as-value"))
    let viaDirect = symexFind(sutFuncDirectCall, tLabel("func-direct"))
    check viaValue.status == sxSat     ## pre-fix: sxUnknown (weInternalWalkerFault)
    check viaDirect.status == sxSat
    check viaValue.witness[0] == 5     ## n : n*2 == 10 => n == 5
    check viaDirect.witness[0] == 5
    check viaValue.status == viaDirect.status
    check viaValue.witness[0] == viaDirect.witness[0]

# ============================================================================
# Cycle 2 — G8 string-op disambiguation: a `func` with a string first param.
# ============================================================================
#
# `hasEvenNonEmptyLen`'s name resolves via `getStdlibModelFor` to
# `smkUnregistered` (it is not a recognized string-op model name), so the
# G8 guard's positive-match `calleeSym.getImpl.kind == nnkProcDef` decides
# whether the call falls through to the user-proc inlining path.
#
# PRE-FIX OBSERVED (traced; confirmed by running this test against unpatched
# HEAD before the :2083 widen): `hasEvenNonEmptyLen`'s `getImpl.kind` is
# `nnkFuncDef`, not `nnkProcDef`, so the `discard ## user proc — fall
# through` branch is NOT taken; the call instead falls into the generic
# string-receiver path and registers a classified `seUnsupportedStringOp`
# error (a FALSE degrade — `hasEvenNonEmptyLen` is an ordinary user routine,
# not an unsupported stdlib string op), producing `sxUnknown`.
func hasEvenNonEmptyLen(s: string): bool = s.len > 0 and (s.len mod 2) == 0

proc sutFuncStringParam(s: string) =
  if hasEvenNonEmptyLen(s):
    symexTarget("func-string-param")

suite "symex N0 cycle 2 — G8 widened for a func with a string first param":
  test "N0-G8: a user func taking a string first param resolves to a real verdict, not seUnsupportedStringOp":
    let r = symexFind(sutFuncStringParam, tLabel("func-string-param"))
    check r.status == sxSat            ## pre-fix: sxUnknown (seUnsupportedStringOp)
    check r.witness[0].len > 0
    check r.witness[0].len mod 2 == 0

# ============================================================================
# Cycle 3 — borrowInfoFor: proc-vs-func borrow TWIN EQUALITY (characterization
# pin, not a promised RED — see the file header).
# ============================================================================
#
# Two structurally-identical distinct float64 types, one borrowing its
# operators via `proc`, the other via `func`; one arithmetic-borrow SUT pair
# (`+`, re-boxes the distinct result) and one comparison-borrow SUT pair
# (`<`, returns raw bool) per type. Twin equality of verdict AND witness
# between the `proc` and `func` spelling is the acceptance criterion.
type MetersProc = distinct float64
proc `+`(a, b: MetersProc): MetersProc {.borrow.}
proc `<`(a, b: MetersProc): bool {.borrow.}

type MetersFunc = distinct float64
func `+`(a, b: MetersFunc): MetersFunc {.borrow.}
func `<`(a, b: MetersFunc): bool {.borrow.}

proc sutBorrowAddProc(m1, m2: MetersProc) =
  if m1 + m2 > MetersProc(10.0):
    symexTarget("borrow_add_proc")

proc sutBorrowAddFunc(m1, m2: MetersFunc) =
  if m1 + m2 > MetersFunc(10.0):
    symexTarget("borrow_add_func")

proc sutBorrowLtProc(m1, m2: MetersProc) =
  if m1 < m2:
    symexTarget("borrow_lt_proc")

proc sutBorrowLtFunc(m1, m2: MetersFunc) =
  if m1 < m2:
    symexTarget("borrow_lt_func")

suite "symex N0 cycle 3 — borrowInfoFor proc-vs-func twin equality (characterization pin)":
  test "N0-borrow pin: arithmetic borrow (+) — proc and func spellings agree on verdict AND witness":
    ## NOT a promised RED (see file header): expected GREEN both before and
    ## after the :855 widen, since the ordinary infix fallthrough already
    ## ejects both operands to base float and computes the same sum — the
    ## missed widen only skips re-boxing the (unread, unconstrained) result
    ## as a distinct const.
    let rProc = symexFind(sutBorrowAddProc, tLabel("borrow_add_proc"))
    let rFunc = symexFind(sutBorrowAddFunc, tLabel("borrow_add_func"))
    check rProc.status == sxSat
    check rFunc.status == sxSat
    check rProc.status == rFunc.status
    check float64(rProc.witness[0]) + float64(rProc.witness[1]) > 10.0
    check float64(rFunc.witness[0]) + float64(rFunc.witness[1]) > 10.0

  test "N0-borrow pin: comparison borrow (<) — proc and func spellings agree on verdict AND witness":
    let rProc = symexFind(sutBorrowLtProc, tLabel("borrow_lt_proc"))
    let rFunc = symexFind(sutBorrowLtFunc, tLabel("borrow_lt_func"))
    check rProc.status == sxSat
    check rFunc.status == sxSat
    check rProc.status == rFunc.status
    check float64(rProc.witness[0]) < float64(rProc.witness[1])
    check float64(rFunc.witness[0]) < float64(rFunc.witness[1])

# ============================================================================
# Version-pin discipline
# ============================================================================
suite "symex N0 — walker version floor":
  test "walker version floor: symexWalkerVersion >= 71 (N0 completes the func widening, Ver: SW)":
    check parseInt(symexWalkerVersion) >= 71
