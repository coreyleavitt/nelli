## Round-6 A0 — fold `low(T)`/`high(T)` int magics at parse time.
##
## Discovered en route to v69 (RFC "Discovered en route (v69 round)"): a
## `low(int32)`/`high(int32)` magic call inside a symex target produced a
## walker fault — `dsl_parser.nim`'s `nnkCall` arm has no interception for
## these `.magic`-pragma system procs, so `earlyClosureCallDetect` /
## `ensureProcRegistered` probed `getImpl` on a body-less intrinsic and
## faulted, even though the equivalent LITERAL spelling (`rLimb >
## -2147483648`) proved clean. A0 folds a concrete int-family `low(T)`/
## `high(T)` call to its literal value at parse time (const-fold-adjacent to
## the existing `nskConst` fold, `tsymex_r5_const_fold.nim`), reusing every
## downstream literal-width-inference path unchanged. A non-int-family
## argument (type or value) declines cleanly instead of falling through to
## the fault.
import std/[unittest, strutils, macros]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/dsl_parser   ## siteMsg unit test — Layer 1 isolation (ADR-0002)

proc rLimbAboveLowInt32(rLimb: int32) =
  ## The exact v69 fault spelling. Almost every int32 (all but the single
  ## value `low(int32)` itself) satisfies `rLimb > low(int32)`, so this is
  ## satisfiable with a real witness — the fold must let the walker resolve
  ## a real verdict here rather than fault.
  if rLimb > low(int32):
    symexTarget("rLimb_above_low")

proc rLimbBelowLowInt32(rLimb: int32) =
  ## UNSAT companion: no int32 is strictly LESS than `low(int32)` — proves
  ## the fold is SOUND (the exact literal value, not just a non-crashing
  ## placeholder), not merely that it stopped faulting.
  if rLimb < low(int32):
    symexTarget("rLimb_below_low")

proc rLimbAboveHighInt32(rLimb: int32) =
  ## `high(T)` sibling: no int32 is strictly GREATER than `high(int32)` —
  ## the sibling magic folds correctly too, not just `low`.
  if rLimb > high(int32):
    symexTarget("rLimb_above_high")

proc lowOnBoolStaysDeclined(flag: bool) =
  ## Out-of-scope type: `bool` is not in `intTyNames`. Must NOT be folded —
  ## must decline cleanly to a classified `sxUnknown`, never crash/fault.
  if flag == low(bool):
    symexTarget("low_bool_reached")

suite "symex round-6 A0 — low/high int magics fold at parse time":

  test "`rLimb > low(int32)` proves reachable with a witness (sxSat)":
    let r = symexFind(rLimbAboveLowInt32, tLabel("rLimb_above_low"))
    check r.status == sxSat

  test "`rLimb < low(int32)` is unreachable (sxUnsat) — the fold is sound":
    let r = symexFind(rLimbBelowLowInt32, tLabel("rLimb_below_low"))
    check r.status == sxUnsat

  test "`rLimb > high(int32)` is unreachable (sxUnsat) — the `high` sibling":
    let r = symexFind(rLimbAboveHighInt32, tLabel("rLimb_above_high"))
    check r.status == sxUnsat

  test "`low(bool)` (non-int-family) stays a classified decline, not a crash":
    let r = symexFind(lowOnBoolStaysDeclined, tLabel("low_bool_reached"))
    check r.status == sxUnknown
    var hasClassified = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError:
        hasClassified = true
    check hasClassified

# ---- siteMsg unit test (ADR-0002 Layer 1 isolation, mirrors
# tsymex_phase1_dsl.nim's `macro ... string` wrapper idiom: capture a raw
# `untyped` AST fixture at the call site, invoke the parser-layer proc at
# macro time, hand the result back as a runtime string literal) ------------

macro siteMsgOf(code: untyped): string =
  newLit(siteMsg(code, "A0 unit test note"))

suite "symex round-6 A0 — siteMsg helper":

  test "opens with <file>:<line>:<col>: and carries the note + n.repr":
    let msg = siteMsgOf(a0UnitTestMarkerVar + 1)
    # "<file>:<line>:<col>: " — locate the ".nim:" boundary (the filename
    # itself may embed a colon, e.g. a Windows drive letter, so this walks
    # forward from the LAST plausible split rather than assuming a fixed
    # split count) and confirm two digit runs each followed by ':', the
    # second followed by ": ".
    let nimIdx = msg.find(".nim:")
    check nimIdx > 0
    let afterFile = msg[(nimIdx + 5) .. ^1]
    let c1 = afterFile.find(':')
    check c1 > 0
    check allCharsInSet(afterFile[0 ..< c1], Digits)
    let afterLine = afterFile[(c1 + 1) .. ^1]
    let c2 = afterLine.find(':')
    check c2 > 0
    check allCharsInSet(afterLine[0 ..< c2], Digits)
    check afterLine[c2 + 1] == ' '
    check "A0 unit test note" in msg
    check "a0UnitTestMarkerVar" in msg   ## the `n.repr` shape

suite "symex round-6 A0 — walker version pin":

  test "walker version floor >= 74 (low/high int-magic parse-time fold)":
    check parseInt(symexWalkerVersion) >= 74
