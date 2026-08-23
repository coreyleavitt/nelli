## Round-6 lows slice (fix round 8) -- five Low-severity review findings in
## the collector/recognizer family of `src/nelli/smt/dsl_parser.nim` (plus
## one `src/nelli/smt/runtime.nim` companion). See each section below for
## the specific finding it pins.
##
## N11 (Low): cross-proc collector CYCLE GUARDS
## (`collectStringBackedByteSeqParamsImpl`/`collectIntOffsetParamsImpl`'s
## `visiting` parameter) were keyed by BARE PROC NAME even though the
## collectors themselves were already migrated to true symbol identity
## (`seq[NimNode]` + `containsSym`/`sameSym`) in R4 -- two overloaded procs
## sharing a printed name collided on one shared guard entry, so recursing
## into the FIRST overload silently blocked the trace from EVER recursing
## into the second, unrelated overload later in the same body
## (degrade-only: a missed closed-form promotion / representation-mismatch
## decline, never a wrong verdict -- the un-promoted argument falls back to
## the pre-existing sound k-unroll path). Fixed by keying `visiting` on the
## proc's own `nnkSym` node instead of its printed name.
##
## N17 (Low): `collectIntOffsetLiteralLocals` lacked the one-level
## call-boundary trace its param sibling `collectIntOffsetParamsImpl`
## already had -- a literal-seeded LOCAL (`var pos = 2`) passed as an
## argument to a callee whose own formal is offset-traced was never
## promoted, so it stayed BV-allocated and failed the callee's inlined
## `iekStrSubstr`/`iekStrInOptionRegion` CR-17 Int-sortedness check.
##
## N25 (Low): `scanShapeReceiverMutated`'s mutation veto matched a var-mode
## call argument (and the direct bracket-assign/`.add`/`.del`/`.insert`
## forms) by bare `strVal` instead of true symbol identity -- a
## nested-scope shadow local sharing the real formal's printed name could
## wrongly veto that formal's string-backed classification
## (false-positive-only, per the file header's own framing: an
## over-cautious decline costs a missed optimization, never a wrong
## verdict).
##
## N23 (Low, hardening, exercised naturally by N11/N17 above -- no
## dedicated section): `collectIntOffsetParamsImpl`'s own `walkCalls`
## resolved callees via raw `getImpl` + an inline `symKind in {nskProc,
## nskFunc}` gate, the exact pre-N2 pattern the permanent N2 audit bans.
## Routed through the shared audited `resolveRoutineImpl` core instead --
## every N11/N17 test below that exercises a one-level call trace exercises
## this fix too (both traces resolve their callee through it).
##
## N3 (Low, defensive hardening, NO REPRO -- no dedicated section):
## `retBindEq` (`runtime.nim`) gained a `reconcileInt` bridge at its own
## top, mirroring `lowerArith`/`lowerCmp`'s established idiom, and its bare
## kind-mismatch `doAssert` was converted to a classified
## `raise newException(ValueError, ...)` decline consistent with its
## neighboring arms. Proven UNREACHABLE in valid Nim today: the scan-offset
## counter feeding a bare-scalar call return is always int-typed,
## `collectIntOffsetParams`/`collectIntOffsetLiteralLocals` only ever trace
## a bare `nnkSym` (never introducing a representation mismatch on their
## own), and `iekConvIntWidth` is strictly widening (never narrows into a
## mismatched kind) -- added purely for symmetry and future-proofing, no
## repro constructed by design. Every proof above already round-trips
## through `retBindEq`'s reconciled path without incident, which is the
## most this finding can honestly be pinned by.
##
## VERDICT-AFFECTING (N11/N17/N25's classification fixes can flip a missed
## `sxUnknown` degrade to a genuine closed-form proof): `symexWalkerVersion`
## bumps 105->106.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

# =============================================================================
# N11 -- cross-proc collector cycle guard: overload-name collision.
# `sutN11OverloadCollision` has NO scan loop of its own -- both `a` and `b`
# rely entirely on the one-level call trace (`collectStringBackedByteSeqParamsImpl`'s
# `walkCalls`) promoting them via each overload's OWN qualifying loop.
# Pre-fix, tracing INTO the first overload marks the bare name "helperN11"
# visited, so the trace into the SECOND, textually-later, entirely
# different overload is skipped outright.
# =============================================================================

proc helperN11(data: seq[byte]): int =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  return i

proc helperN11(data: seq[byte], flag: bool): int =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  return i

proc sutN11OverloadCollision(a: seq[byte], b: seq[byte]) =
  let ia = helperN11(a)
  let ib = helperN11(b, true)
  ## `ib == 7` needs the SECOND overload's own scan to reach depth 7 -- past
  ## the default `maxLoopUnwind = 5` k-unroll budget the un-promoted
  ## (array-modeled) fallback is bounded by, but trivial for the genuine
  ## unbounded Sequence-theory closed form the promotion unlocks.
  if ia == 1 and ib == 7:
    symexTarget("n11_overload_deep")

suite "symex round-6 N11 -- cross-proc collector cycle guard, overload collision":

  test "N11-1: BOTH overloaded callees' offset traces compose -> sxSat (pre-fix RED: 2nd overload's cycle-guard entry collided with the 1st by bare name, its call trace never ran)":
    let r = symexFind(sutN11OverloadCollision, tLabel("n11_overload_deep"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

# =============================================================================
# N17 -- `collectIntOffsetLiteralLocals` one-level call trace. `pos` is a
# literal-seeded LOCAL of the CALLER (`sutN17LiteralSeededCallBoundary`),
# not itself an accumulating-scan/pair-loop counter in the caller's own
# body (the caller has no while loop of its own at all) -- only the
# CALLEE's (`readCStringN17`) own body has the recognized B4 shape whose
# counter traces back to `readCStringN17`'s OWN formal `offset`. Without
# the call-boundary trace, `pos` stays BV-allocated in the caller's env and
# the callee's inlined closed form's CR-17 Int-sortedness check declines.
# =============================================================================

proc readCStringN17(data: seq[byte], offset: int): (string, int) =
  var s = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (s, i + 1)
    s.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

proc sutN17LiteralSeededCallBoundary(data: seq[byte]) =
  var pos = 2   ## literal-seeded -- NOT a formal, NOT this proc's own loop
                ## counter (this proc has no loop of its own at all).
  let (s, _) = readCStringN17(data, pos)
  if s == "AB":
    symexTarget("n17_literal_call_boundary")

suite "symex round-6 N17 -- literal-seeded local, one-level call trace":

  test "N17-1: a literal-seeded local threaded through a call boundary to the callee's offset-consuming formal -> sxSat (pre-fix RED: CR-17 Int-sortedness decline, sxUnknown)":
    let r = symexFind(sutN17LiteralSeededCallBoundary, tLabel("n17_literal_call_boundary"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat
    check r.witness[0][2] == byte('A')
    check r.witness[0][3] == byte('B')
    check r.witness[0][4] == 0'u8

# =============================================================================
# N25 -- `scanShapeReceiverMutated`'s mutation veto, shadow-collision
# false positive. Construction mirrors `tsymex_r6_n28_shadow_collision.nim`'s
# own proven-safe shape (target-before-block, shadow copied from a SECOND
# param) to sidestep the SAME unrelated pre-existing walker gap that file's
# header documents (reasoning about code positioned textually AFTER a
# `block:` containing a recognized accumulating-scan is independently
# unreliable, regardless of any name collision) -- the real formal's own
# observable sits BEFORE the shadow-collision block; classification is a
# static, whole-proc pre-pass, so the collector still sees the block's
# mutation regardless of where the observable sits.
# =============================================================================

proc growByteSeqN25(s: var seq[byte]) =
  s.add 0'u8

proc sutN25ShadowVetoFalsePositive(data: seq[byte], src: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  ## `i == 10` needs depth past the default `maxLoopUnwind = 5` -- reachable
  ## only via the genuine closed form, i.e. only once `data` is correctly
  ## classified string-backed.
  if i == 10:
    symexTarget("n25_shadow_veto_false_positive")
  block:
    var data = src            ## SHADOW -- same printed name, DIFFERENT
                               ## binding from the real formal `data` above.
    growByteSeqN25(data)       ## mutates the SHADOW only.

suite "symex round-6 N25 -- mutation-veto shadow-collision false positive":

  test "N25-1: the real (never-mutated) formal is not wrongly vetoed by a same-named shadow's mutation -> sxSat (pre-fix RED: bare strVal match wrongly vetoed string-backing, sxUnknown)":
    let r = symexFind(sutN25ShadowVetoFalsePositive, tLabel("n25_shadow_veto_false_positive"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxSat

# =============================================================================
# N25 regression companion -- a GENUINE (non-shadowed) var-mode mutation of
# the real formal must stay vetoed exactly as before this fix (same
# shape as `tsymex_r6_r4_collector_scoping.nim`'s own W2a pin -- included
# here too since this slice changes `scanShapeReceiverMutated`'s own
# parameter type, `string` -> `NimNode`, and deserves its own direct
# regression check in the file that made that change).
# =============================================================================

proc sutN25GenuineMutationStillVetoed(data: var seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  growByteSeqN25(data)
  if i == 2:
    symexTarget("n25_genuine_veto_regression")

suite "symex round-6 N25 -- regression: genuine (non-shadowed) mutation still vetoed":

  test "N25-2: a genuinely var-aliased mutation of the real formal still excludes it from string-backing, unchanged by this fix":
    let r = symexFind(sutN25GenuineMutationStillVetoed, tLabel("n25_genuine_veto_regression"))
    check r.status == sxUnknown
    var sawWidthDecline = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault and "unsupported width" in e.msg:
        sawWidthDecline = true
    check sawWidthDecline

# =============================================================================
# Version pin
# =============================================================================

suite "symex round-6 lows -- walker version pin":

  test "walker version floor >= 106 (N11/N17/N25 collector/veto symbol-identity fixes, verdict-affecting; N23/N3 hardening)":
    check parseInt(symexWalkerVersion) >= 106
