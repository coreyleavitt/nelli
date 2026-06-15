## Phase 15 — Cluster G, cycle G3: type-substitution path through `classifyType`
## + `auto`-return safety.
##
## LOCKED DECISION (see RFC-phase15-reconciliation.md §F Cluster G): generic
## procs symex via PARSE-TIME monomorphization (`gatherTypeSubst` →
## `monomorphize` → `parseCalleeImpl`). G3 is an AUDIT + guards cycle: it
## confirms that a substitution-DERIVED concrete type node (the node
## `monomorphize` produces when binding `T` to a concrete type from the typed
## call site) resolves to the correct `IRType` through `classifyType`, across
## the type families substitution may produce — with the float family the
## centerpiece (G3 depends on Cluster F's float bridge).
##
## Three audit targets:
##   1. `id[T](x: T): T = x` at `T = float64` — param + return classify as
##      itFloat64; the walker symex's the float-specialized body and reaches a
##      target with a float witness (sxSat, NOT an sxUnknown fallback). This is
##      the Cluster-F-bridge-through-generics centerpiece.
##   2. `foo[T](x: sink T): T = x` at `T = int` — the `sink` ownership wrapper
##      is stripped (Z3c/G3) so the param classifies as itInt; must NOT fail on
##      an unhandled sink node.
##
## (A string-instantiated identity at `T = string` is deferred: the
## type-SUBSTITUTION path classifies `string` correctly, but full string
## proc-RETURN value extraction is a separate, pre-existing unwired path — not a
## generic concern — so it is out of G3 scope. The float centerpiece proves the
## return-value bridge through generics; sink proves the wrapper strip.)
import std/unittest
import proptest/symex

# --- 1. float64 instantiation (Cluster F bridge through generics) -----------
proc idF[T](x: T): T = x

proc useFloat(x: float64) =
  # `idF(x)` instantiates at T = float64; the returned float must flow into a
  # float comparison and be reachable (sxSat) — proving the substitution-derived
  # float64 node classified as itFloat64 at BOTH the param and the return.
  let r = idF(x)
  if r > 1.5:
    symexTarget("float_reached")

# --- 2. sink T through generics (Z3c sink strip) ----------------------------
proc idSink[T](x: sink T): T = x

proc useSink(x: int) =
  let r = idSink(x)
  if r == 42:
    symexTarget("sink_reached")

suite "symex Phase 15 G3 — generic type-substitution through classifyType":
  test "identity proc instantiated at float64 classifies correctly":
    let r = symexFind(useFloat, tLabel("float_reached"))
    check r.status == sxSat

  test "sink T param through generics classifies as itInt (Z3c sink strip)":
    let r = symexFind(useSink, tLabel("sink_reached"))
    check r.status == sxSat
