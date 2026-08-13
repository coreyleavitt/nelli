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
## `runtime.nim`'s `elif w.sawUnknown or capForcedUnknown ...` branch, which
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
import std/unittest
import nelli/symex

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

suite "symex RFC-chapulin-hardening R8 — omitted non-scalar field construction-time degrade":

  test "R8-1: omitted seq field -> sxUnknown (never a false sxSat/sxUnsat -- Invariant 3)":
    let r = symexFind(sutBagOmittedSeqField, tLabel("bag_omitted_seq_hit"))
    ## Load-bearing soundness assertion: this must NEVER become a false sxSat
    ## (a guessed zero for a non-scalar field would be exactly the
    ## false-verdict bug R8 must avoid introducing).
    check r.status != sxSat
    check r.status == sxUnknown

  test "R8-2: reported error kind is the clean feUnsupportedExprKind degrade, NOT weInternalWalkerFault":
    let r = symexFind(sutBagOmittedSeqField, tLabel("bag_omitted_seq_hit"))
    var sawClean = false
    var sawFault = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        sawClean = true
      if e.kind == weInternalWalkerFault:
        sawFault = true
    check sawClean
    check not sawFault
