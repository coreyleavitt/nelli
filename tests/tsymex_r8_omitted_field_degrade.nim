## RFC-chapulin-hardening R8 (deferred LOW finding, telemetry hygiene). P2a's
## value-object constructor (`nnkObjConstr` in expression position,
## `dsl_parser.nim` ~2280-2294) handles an OMITTED field by asking
## `zeroValueForType` for the field's sound Nim zero-init value. For a SCALAR
## field (int/bool/float/string) that succeeds and the constructed object is
## REALLY zero-initialised (see `tsymex_p2a_objconstr_expr.nim` P2a-5/6).
##
## For a NON-SCALAR field (a nested `seq`/`tuple`/`table`/`set`/variant —
## anything `zeroValueForType`'s `else: nil` catch-all declines), there is no
## clean zero encoding, so the omission is genuinely unmodeled. Before this
## fix, the `else` branch registered the correct classified
## `feUnsupportedExprKind` parse-error AND emitted the `mkUnsupported`
## SND-1-taint preamble stmt (both sound), but ALSO pushed a bare
## `mkIntLit(0)` into the tuple-literal `elems` as the field's placeholder
## value — a value whose IR *kind* does not match the field's declared
## (non-scalar) `IRType`. That mistyped element then flows into
## `mkTupleLit`/its lowering and throws a native `ValueError` at WALK time.
## Because `runSymexImpl`'s outer `try/except` is a single boundary around
## the whole walk, that runtime exception preempts the already-registered
## `feUnsupportedExprKind` classification entirely: the walk's own
## `prog.parseErrors` are never drained into the result (see
## `runtime.nim`'s `elif w.sawUnknown or capForcedUnknown ...` branch -- since
## RFC-0005 S9 the reach-joined verdict block -- which
## is only reached if the walk completes WITHOUT raising) and the generic
## `CatchableError` catch-all (`runtime.nim` ~7727) reclassifies the whole
## run as `weInternalWalkerFault` instead — a real engine-bug signal for
## what is actually a known, already-classified unmodeled construct.
##
## The verdict was ALWAYS `sxUnknown` either way (Invariant 3 — SND-1's
## `mkUnsupported` taint and/or the `weInternalWalkerFault` catch-all both
## force `sxUnknown`), so this is telemetry-only: no false `sxSat`/`sxUnsat`
## is possible before or after the fix. What changes is WHICH error `kind`
## is reported: after the fix, construction never emits a mistyped element,
## so the walk completes cleanly and the pre-registered
## `feUnsupportedExprKind` classification (not `weInternalWalkerFault`)
## reaches `SymexResult.errors`.
##
## RFC-0005 S8aj (walker 177): `zeroValueForType` now has the zero for an
## array, object, seq and variant (`mkZeroValue`, lowered by
## `defaultZero`), so an omitted `seq` field is no longer unmodeled: it is
## Nim's own zero, the empty seq. `Bag(tag: x).xs.len == 0` is TRUE in
## compiled Nim, so the target is a real `sxSat` (x == 5) with no decline,
## and its twin `xs.len != 0` is `sxUnsat`. The "guessed zero" R8-1 warned
## against is a zero Nim does not give; this one it does. Both R8 pins
## keep their invariants: never a false verdict (the SAT witness is
## checked, the twin refuted) and never `weInternalWalkerFault`.
import std/unittest
import nelli/symex
import nelli/smt/canonicalize
import std/strutils

type
  Bag = object
    tag: int
    xs: seq[int]      ## non-scalar field: zeroValueForType(itSeq) has no
                       ## clean zero encoding (declines via its `else: nil`).

# `xs` is OMITTED entirely (not merely an unsupported expression) — this is
# the CONSTRUCTION-TIME omitted-non-scalar-field path, distinct from
# `tsymex_p2a_objconstr_expr.nim`'s P2a-10 (a PRESENT but unsupported
# scalar-typed field, which already went through the CR-2a catch-all
# untouched by this fix).
#
# The guard condition READS `b.xs.len`: symbolic lowering of `and` builds
# BOTH operands into the branch's Z3 constraint eagerly (it is not a
# runtime short-circuit), so the mistyped placeholder field is exercised on
# every path through this SUT, not just a path that happens to touch it.
# Before the fix, `lowerTupleLit` stores whatever `lower()` naturally
# produces for the placeholder IRExpr at that field position with NO
# per-field kind check (only `itInt`/`itBool` fields get a proto at all —
# see `runtime.nim`'s `lowerTupleLit`), so a mistyped `mkIntLit(0)` silently
# becomes an `svInt` sitting where an `svSeq` belongs; reading `.len` off it
# then hits `iekSeqLen`'s `else: raise newException(ValueError, "iekSeqLen
# on non-container kind=...")` — a native `ValueError` the outer
# `CatchableError` catch-all reclassifies as `weInternalWalkerFault`.
proc sutBagOmittedSeqField(x: int) =
  let b = Bag(tag: x)
  if b.tag == 5 and b.xs.len == 0:
    symexTarget("bag_omitted_seq_hit")

proc sutBagOmittedSeqFieldDead(x: int) =
  let b = Bag(tag: x)
  if b.tag == 5 and b.xs.len != 0:
    symexTarget("bag_omitted_seq_dead")

suite "symex RFC-chapulin-hardening R8 — omitted non-scalar field construction-time degrade":

  test "R8-1: omitted seq field is Nim's empty seq -> a real sxSat, its twin sxUnsat (never a false verdict -- Invariant 3)":
    let r = symexFind(sutBagOmittedSeqField, tLabel("bag_omitted_seq_hit"))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(sutBagOmittedSeqFieldDead, tLabel("bag_omitted_seq_dead"))
    check d.status == sxUnsat

  test "R8-2: no decline and never weInternalWalkerFault":
    let r = symexFind(sutBagOmittedSeqField, tLabel("bag_omitted_seq_hit"))
    var sawDecline = false
    var sawFault = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawDecline = true
      if e.kind == weInternalWalkerFault:
        sawFault = true
    check not sawDecline
    check not sawFault

  test "symexWalkerVersion >= 177 (RFC-0005 S8aj: the omitted field's zero)":
    check parseInt(symexWalkerVersion) >= 177
