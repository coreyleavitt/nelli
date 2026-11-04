## RFC-0005 batch 9 -- a call declines before Nim's call depth limit ends the
## process.
##
## A build with stack traces quits at `nimCallDepthLimit` nested frames (2000 by
## default), and `walk` recurses natively once per inlined call, 9 frames a
## level. S8ca's check measures the stack, and on a Windows solve's 16 MB fiber
## the frame limit came first: `tsymex_rfc0005_s8ca_stack`'s deep budget ended the
## binary with rc=1. Nothing in the walk could report it.
##
## This file's `.nim.cfg` lowers the limit to 800, so the frames run out long
## before any stack does and the same pin holds on every platform.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/runtime
import nelli/smt/nativestack

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc framesNamed(errs: seq[SymexErrorInfo]): bool =
  for e in errs:
    if e.kind == beBudgetExhaustedUnmodelled and
       "call depth limit" in e.msg and "nimCallDepthLimit" in e.msg:
      return true

proc forever(n: uint): uint =
  ## As `tsymex_rfc0005_s8ca_stack`'s: only the call, on a new argument. Never
  ## run natively.
  result = forever(n + 1)

proc foreverSut(n: uint) =
  if forever(n) > 1_000_000'u:
    symexTarget("cd_forever_never")

proc helper(x: int): int = x + 1

proc shallow(x: int) =
  if helper(x) == 8:
    symexTarget("cd_shallow")

const deep = SymexSettings(budget: ResourceBudget(maxCallDepth: 100_000,
                                                  maxRecursionDepth: 100_000))

suite "batch 9: Nim's call depth limit":

  test "the limit this build has is read":
    check nimFramesLeft() > 0
    check nimFramesLeft() <= 800

  test "a depth budget past the limit declines in-band, named":
    let r = symexFind(foreverSut, tLabel("cd_forever_never"), deep)
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check framesNamed(r.errors)
    # The machine's limit, not the program's: not cached.
    check rdNativeStack in r.soundness.runDependence

  test "a call the limit leaves room for is inlined and decides":
    let r = symexFind(shallow, tLabel("cd_shallow"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check rdNativeStack notin r.soundness.runDependence
