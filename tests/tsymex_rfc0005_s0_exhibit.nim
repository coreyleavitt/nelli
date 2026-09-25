## RFC-0005 (soundness channels) slice S0 -- "exhibit the discarded
## capability": three GREEN characterization pins, run through the REAL
## public entry point (`symexFind`, `symex.nim` ~1220), that record what
## today's undifferentiated `sxUnknown` throws away. Nothing here is new
## engine capability -- these are pins on TODAY's behaviour, chosen so a
## later slice's flip is a one-line status-and-error-set diff against this
## file, not a fresh investigation.
##
## Each pin's doc comment states: what the engine reports today, WHY (the
## exact mechanism/funnel), and which RFC-0005 slice is expected to flip it
## and to what. `SymexResult.errors` is already public (`types.nim`), so
## each pin asserts the EXACT set of `sevError`-severity error KINDS the run
## drains -- the "over-taint-only" (or "clean witness + disjoint decline")
## claim is checked, not assumed.
##
## ----------------------------------------------------------------------------
## Pin 1 -- UNSAT exhibit (RFC-0005 S0, DoD item 1; expected to flip at S4)
## ----------------------------------------------------------------------------
## `s0DeadFreshSymbol` reads `p.s` -- a `string` FIELD through a heap-deref'd
## `ref` -- which `liftHeapValue`'s unsupported-pointee-kind `else` arm
## (`runtime_heap.nim` ~294-300) does not yet model (Cluster R1 covers only
## PRIMITIVE pointees; a `string`/composite pointee lands here). That site
## calls `allocDegrade(heUnresolvedRef, ...)` (the funnel at `runtime.nim`
## ~1295) and substitutes a FRESH, UNCONSTRAINED placeholder `svString` for
## `p.s` (`allocateSym(pointeeTy, "__liftHeapValueUnsupported", freshLiftPc)`
## -- no value constraint beyond the byte-faithful ADR-0006 char-range domain
## every `itString` allocation carries, which is a WELL-FORMEDNESS
## constraint, not a value pin: see `allocateSym`'s `of itString:` arm,
## `runtime.nim` ~2458). This is precisely RFC-0005 §2.2's `DegradeClass`
## `dcFreshSymbol`: the modelled program can read ANY string there, a
## superset of whatever the real field holds -- over-approximation only.
##
## The target's reachability has NOTHING to do with that degraded value:
## `n == 5 and n == 6` is a contradiction over a CLEAN, fully-modelled `int`
## parameter untouched by the heap read. No value of the fresh placeholder,
## nor of `p` itself, can make it true -- the target is genuinely unreachable
## in the real program, for a reason wholly independent of the
## over-approximation. Today the engine cannot tell "over-approximation
## only" from "under-approximation somewhere" -- ANY degrade sets
## `w.sawUnknown`, and `runSymexImpl`'s verdict block (`runtime.nim`
## ~13576-13595) reports `sxUnsat` only when `sawUnknown` never fired at
## all -- so this run is forced to `sxUnknown` despite proving the target
## unreachable. Under RFC-0005's §2.3 verdict rule (`scIncomplete notin
## runTaint` -> `sxUnsat`), this is a sound `sxUnsat`: `dcFreshSymbol`'s
## `runTaint` is `{scSpurious}` only (§2.2's `runTaint` table), so
## `scIncomplete` is never in it.
##
## **Routes through the `allocDegrade` funnel** (`runtime.nim` ~1295) --
## RFC-0005 slice S4 classifies that funnel (`heUnresolvedRef` -> `dcFreshSymbol`)
## and this pin is the one chosen to flip there: `sxUnknown` -> `sxUnsat`.
##
## Verified by reasoning AND by the observed error-kind set (below): the
## ONLY `sevError` kind ever drained on this run is `heUnresolvedRef`. No
## under-approximating kind fires -- no `beBudgetExhausted` (no loop/call/
## frontier budget is anywhere near this SUT), no heap-depth halt (a single
## one-level deref, nowhere near `maxHeapDepth`), no k-unroll (no loop at
## all).

import std/[unittest, sequtils, strutils]
import nelli/smt/canonicalize
import nelli/symex

type
  S0DeadNode = ref object
    s: string

proc s0DeadFreshSymbol(p: S0DeadNode, n: int) =
  if p != nil:
    discard p.s
  if n == 5 and n == 6:
    symexTarget("s0_dead_fresh_symbol")

# =============================================================================
# Pin 2 -- cap-veto companion (RFC-0005 S0, DoD item 2; expected to flip at S9)
# =============================================================================
## `cast[int32](x)` used as an OPERAND of `+` is an expression-position
## construct `parseExpr` (`dsl_parser.nim`) has no arm for outside the R11
## pointer-materialisation guard (which matches only `cast[ptr T]`/`addr`,
## and only at let-rhs classification). Hitting `parseExpr`'s final
## catch-all records `feUnsupportedExprKind` (`sevError`) in
## `prog.parseErrors` -- a Class-A, site-anchored decline (RFC-0005 §2.5
## item 1) -- at PARSE time, unconditionally: matches the EXACT precedent
## at `tests/tsymex_CR2a_expr_catchall.nim`'s `sutCastSubExpr` (confirmed:
## the SAME construct routed through a SEPARATE callee proc instead hits an
## unrelated `lowerConvIntWidth` walker assertion on the callee's own
## return-type widening -- a different, unclassified crash this pin does
## NOT want to exhibit -- so the construct stays inline in the caller).
##
## The `cast` sits inside `if deadGuard and not deadGuard:` in
## `s0CapVetoCompanion` -- a tautological contradiction over a symbolic
## `bool` param, true for NO value of `deadGuard` in any real run. It is
## nonetheless PARSED (`dsl_parser.nim`'s ordinary recursive AST walk runs
## before any symbolic walk and has no notion of walk-time feasibility), so
## `feUnsupportedExprKind` lands in `prog.parseErrors` regardless of
## whether the branch is ever, or could ever be, walked to a witness.
##
## `x == 42` is a CLEAN witness -- reachable, untainted, on a path that
## never touches `s0DeadCastHelper` at all. Today's engine cannot express
## "a decline exists in the program but was never on any path that
## mattered": `capForcedUnknown` (`runtime.nim` ~13492-13510) is a BLANKET
## switch that forces `sxUnknown` whenever ANY `sevError` exists ANYWHERE in
## `prog.parseErrors`, unconditionally, before the winner scan even runs
## (`runtime.nim` ~13536: `if w.found.len > 0 and not capForcedUnknown and
## not closureForcedUnknown`) -- so the clean witness is discarded and the
## verdict is `sxUnknown`, exactly the shape `capForcedUnknown`'s own doc
## comment describes ("a cap discovered on a NON-walked path ... guarded
## behind an unreachable branch").
##
## RFC-0005 slice S9 deletes this blanket veto (replacing it with the
## `DeclineScope`-based reach-taint of §2.5, landed inert at S8); this pin
## is the one chosen to flip there: `sxUnknown` -> `sxSat`.
##
## The ONLY `sevError` kind this run ever drains is `feUnsupportedExprKind`.

proc s0CapVetoCompanion(x: int, deadGuard: bool) =
  if deadGuard and not deadGuard:
    let y = cast[int32](x) + 1
    discard y
  if x == 42:
    symexTarget("s0_cap_veto_companion")

# =============================================================================
# Pin 3 -- closure-veto companion (RFC-0005 S0, DoD item 2; flips at S9)
# =============================================================================
## Same shape as pin 2, for `closureForcedUnknown` (`runtime.nim`
## ~13519-13523) rather than `capForcedUnknown`. `xs.filter(...)` over a
## `seq[int]` PARAMETER -- a symbolic-length seq -- takes `lowerHofCall`'s
## AXIOM path (`runtime.nim` ~12503-12523): there is no Z3 `seqFilter` HOF
## (a quantified filter predicate over a symbolic-length seq is a hang
## risk), so it records `ceUnsupportedHof` (`sevError`) into
## `currentClosureCallErrors` and returns a fresh placeholder seq -- the
## EXACT precedent at `tests/tsymex_r6_n27_hof_placeholder.nim`'s
## `sutFilterBackedSymbolic`. Per RFC-0005 §2.5's round-2 correction, this
## site writes ONLY `currentClosureCallErrors` + a ptr-cast `sawUnknown` --
## it does NOT set `loweringDidDegrade`, so `drainPendingLowerEffects` never
## taints the calling PATH at all. The error is accumulated into the RUN's
## `closureErrs` at drain time regardless of which path produced it (same
## blanket shape as `prog.parseErrors`).
##
## The `.filter` call sits behind `if x == 7:`, a branch disjoint from the
## `x == 42` clean witness -- the winning path never touches the closure
## call. `closureForcedUnknown` (`runtime.nim` ~13519-13523) is nonetheless
## a BLANKET switch exactly like `capForcedUnknown`: it fires on ANY
## `sevError` in the run-wide `closureErrs`, regardless of path, so the
## clean `x == 42` witness is discarded and the verdict is `sxUnknown`
## today.
##
## RFC-0005 slice S9 deletes this blanket veto too (gated on S7 routing
## every value-substituting closure/HOF decline through `w.degrade` + path
## taint, per §2.5's round-2 correction); this pin is the one chosen to
## flip there: `sxUnknown` -> `sxSat`.
##
## The ONLY `sevError` kind this run ever drains is `ceUnsupportedHof`.

proc s0ClosureVetoCompanion(xs: seq[int], x: int) =
  if x == 7:
    let kept = xs.filter(proc(v: int): bool = v > 0)
    discard kept
  if x == 42:
    symexTarget("s0_closure_veto_companion")

# =============================================================================
# Oracles -- the same computation executed for real in Nim (house rule)
# =============================================================================

suite "RFC-0005 S0 -- oracles":

  test "oracle: n == 5 and n == 6 is a genuine contradiction":
    for n in [0, 5, 6, 42, -1]:
      check not (n == 5 and n == 6)

  test "oracle: deadGuard and not deadGuard is a genuine contradiction":
    for g in [true, false]:
      check not (g and not g)

  test "oracle: x == 7 and x == 42 are genuinely disjoint":
    check not (7 == 42)

suite "RFC-0005 S0 pin 1 -- over-taint-only UNSAT exhibit (flips sxUnsat at S4)":

  test "today: sxUnknown, never sxSat/sxUnsat":
    let r = symexFind(s0DeadFreshSymbol, tLabel("s0_dead_fresh_symbol"))
    for e in r.errors: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat

  test "today: the drained sevError kind set is EXACTLY {heUnresolvedRef} -- over-taint-only, asserted not assumed":
    let r = symexFind(s0DeadFreshSymbol, tLabel("s0_dead_fresh_symbol"))
    var sevErrorKinds: seq[SymexErrorKind]
    for e in r.errors:
      if e.severity == sevError:
        sevErrorKinds.add e.kind
    check sevErrorKinds == @[heUnresolvedRef]
    # No under-approximating kind anywhere -- the run-wide taint is
    # over-only, which is exactly what licenses the S4 flip to sxUnsat.
    for e in r.errors:
      check e.kind != beBudgetExhausted
      check e.kind != weInternalWalkerFault

suite "RFC-0005 S0 pin 2 -- cap-veto companion (flips sxSat at S9)":

  test "today: a clean-path witness is discarded by the blanket cap veto -- sxUnknown, never sxSat":
    let r = symexFind(s0CapVetoCompanion, tLabel("s0_cap_veto_companion"))
    for e in r.errors: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)
    check r.status == sxUnknown
    check r.status != sxSat

  test "today: the drained sevError kind set is EXACTLY {feUnsupportedExprKind}, from a branch disjoint from the witness":
    let r = symexFind(s0CapVetoCompanion, tLabel("s0_cap_veto_companion"))
    var sevErrorKinds: seq[SymexErrorKind]
    for e in r.errors:
      if e.severity == sevError:
        sevErrorKinds.add e.kind
    # A kind SET (RFC-0005 S1b): the Class-A `isUnsupported` node now carries
    # its parse-time kind and the walker records it again where a path
    # reaches the decline, so `feUnsupportedExprKind` is drained twice (the
    # parse-time entry + the walk-site entry). The set is unchanged.
    check deduplicate(sevErrorKinds) == @[feUnsupportedExprKind]

suite "RFC-0005 S0 pin 3 -- closure-veto companion (flips sxSat at S9)":

  test "today: a clean-path witness is discarded by the blanket closure veto -- sxUnknown, never sxSat":
    let r = symexFind(s0ClosureVetoCompanion, tLabel("s0_closure_veto_companion"))
    for e in r.errors: checkpoint($e.kind & " sev=" & $e.severity & ": " & e.msg)
    check r.status == sxUnknown
    check r.status != sxSat

  test "today: the drained sevError kind set is EXACTLY {ceUnsupportedHof}, from a branch disjoint from the witness":
    let r = symexFind(s0ClosureVetoCompanion, tLabel("s0_closure_veto_companion"))
    var sevErrorKinds: seq[SymexErrorKind]
    for e in r.errors:
      if e.severity == sevError:
        sevErrorKinds.add e.kind
    check sevErrorKinds == @[ceUnsupportedHof]

suite "RFC-0005 S0 -- walker version pin":

  test "walker version floor >= 140 (S0 adds no walker-semantics change -- characterization only)":
    check parseInt(symexWalkerVersion) >= 140
