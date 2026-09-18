## Issue #163 wiring audit, wave 2 — the last four gaps.
##
## Four independent findings, one suite each. Method note (inherited from
## #162/#163 wave 1): every symbolic expectation is paired with the same
## computation run for real in this file wherever the shape allows it — a
## taint/soundness bug is exactly the shape where a test can encode the
## engine's own wrong model and pass, and running Nim removes the model
## from the loop.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# W6 — a range-typed (non-enum) variant discriminator with an `else:` arm.
# =============================================================================
## Both discriminator-domain builders (the BV path and the isOptimised
## promoted-Int path) fan an `else:` arm's coverage out over `ty.vDiscTags`,
## which is populated ONLY from an enum impl (`dsl_typebridge.nim`). A
## non-enum (range-alias) discriminator leaves it empty, so the else-arm
## domain silently narrowed to just the explicit `of N:` literals and every
## else-arm value was falsely unreachable.

type
  W6Tag = range[0..10]
  W6Obj = object
    case kind: W6Tag
    of 1: a: int
    of 2: b: int
    else: e: int

proc gatedElseArm(v: W6Obj) =
  if v.kind == 5:
    if v.e == 42:
      symexTarget("else-hit")

proc gatedOfArm(v: W6Obj) =
  ## Non-regression companion: the fix must not cost the explicit arms
  ## their own reachability.
  if v.kind == 1:
    if v.a == 7:
      symexTarget("of-hit")

const Exact = SymexSettings(integerSemantics: isExact)

suite "#163 W6 -- range-alias variant discriminator with an else arm":

  test "oracle -- kind=5 is not an explicit `of` literal, so it really lands in the else arm":
    let v = W6Obj(kind: 5, e: 42)
    check v.kind == 5
    check v.e == 42

  test "isExact (the BV discriminator-domain builder) finds the else-arm target":
    let r = symexFind(gatedElseArm, tLabel("else-hit"), Exact)
    check r.status == sxSat

  test "isOptimised (the promoted-Int discriminator-domain builder) finds it too":
    let r = symexFind(gatedElseArm, tLabel("else-hit"))
    check r.status == sxSat

  test "non-regression -- an explicit `of` arm is still reachable in both modes":
    check symexFind(gatedOfArm, tLabel("of-hit"), Exact).status == sxSat
    check symexFind(gatedOfArm, tLabel("of-hit")).status == sxSat

# =============================================================================
# W8 — a traced int-offset allocation position drops a declared range.
# =============================================================================
## `allocateSym`'s top-level-param `isIntOffset` promotion re-asserts a
## declared `range[lo..hi]` when it promotes to `svInt`. Its two allocation-
## side siblings -- the bare (non-tuple) scan-offset return and the traced
## tuple position -- do not: both allocate `svInt` directly and ignore
## `ty.hasRange`/`ft.hasRange` sitting on the very type they were handed.
##
## Trigger: `calleeIntOffsetReturnPositions` (dsl_parser.nim) recognizes a
## scan loop's `return <expr>` PURELY by AST SHAPE (the loop counter, or a
## trivial `+/- literal` on it) -- it never inspects the proc's declared
## return type. Declaring that return type as `range[lo..hi]` still gets
## recognized, and the recognizer's positions flow straight into
## `allocateSym` via `stmt.retTy`/`freshRetSym`, so a scan proc can genuinely
## return a range-typed offset and hit either dropped-range arm.

type
  W8ScanError = object of CatchableError

proc findColonRanged(s: string, offset: int): range[0..1000] =
  ## Bare (non-tuple) scan-offset return, declared as a range. The loop
  ## counter `i` stays plain `int` -- only the RETURN TYPE is a range, which
  ## the shape-only recognizer does not care about.
  ##
  ## Shape note, and it is load-bearing: this is the **Q1/B0 skip-while**
  ## idiom (`while i < s.len and s[i] != lit: inc i`), NOT B3's
  ## early-return-on-match (`while i < s.len: (if s[i] == lit: return i);
  ## inc i`). Both reach the bare int-offset arm, but `tsymex_r6_b3_scanpair`
  ## is one of the six suites the Linux/podman sweep skips by name for
  ## non-termination, while `tsymex_r6_b0_scanlift_bound` passes there
  ## (rc=0 in the recorded baseline). Writing this in B3's shape made the
  ## whole file hang at the 600s bound and read as a new engine defect; it
  ## is the documented platform split, not a new one. Keep it in the B0
  ## shape so this suite stays runnable on Linux.
  var i = offset
  while i < s.len and s[i] != ':':
    inc i
  return i

proc scanAccRanged(s: string, offset: int): (string, range[0..1000]) =
  ## Traced TUPLE position, declared as a range: the accumulating (B4) scan
  ## shape, second field range-typed. B4 is `tsymex_r6_b4_readcstring`'s
  ## family, which passes on Linux (rc=0 in the recorded baseline), so this
  ## one keeps its early-return form.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(W8ScanError, "unterminated")

proc callerBare(s: string) =
  let p = findColonRanged(s, 0)
  if p > 1000:
    symexTarget("impossible_bare")

proc callerTuple(s: string) =
  let (_, p2) = scanAccRanged(s, 0)
  if p2 > 1000:
    symexTarget("impossible_tuple")

suite "#163 W8 -- traced int-offset positions still carry a declared range":

  test "oracle -- Nim itself enforces the declared range at the bare scan's own return":
    check findColonRanged("ab:cd", 0) == 2
    let tooFar = repeat('x', 1500) & ":"
    expect RangeDefect:
      discard findColonRanged(tooFar, 0)

  test "oracle -- and at the tuple-position scan's own return":
    let (acc, off) = scanAccRanged("ab:cd", 0)
    check acc == "ab"
    check off == 3
    let tooFar = repeat('x', 1500) & ":"
    expect RangeDefect:
      discard scanAccRanged(tooFar, 0)

  test "bare scan-offset return: the declared range constrains the path (was falsely satisfiable)":
    let r = symexFind(callerBare, tLabel("impossible_bare"))
    check r.status == sxUnsat

  test "traced tuple position: the declared range constrains the path too":
    let r = symexFind(callerTuple, tLabel("impossible_tuple"))
    check r.status == sxUnsat
