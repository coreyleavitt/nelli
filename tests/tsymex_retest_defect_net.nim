## Round-3 crash-doctrine decision (Corey, 2026-08-06) — the Defect net.
## §0 says "never a native crash"; CR-1c deliberately excluded `Defect`s so
## the ~63 internal doAsserts crashed loudly. With 0.1.0 shipped and
## chapulin consuming, the decision: ONE `except Defect` arm on the
## outermost `runSymex` try, classified `weInternalWalkerFault` (the same
## walker-bug-backlog telemetry contract as the CatchableError net — never
## conflated with construct gaps). Consumers get a classified sxUnknown
## instead of a dead process; nelli CI tracks the kind's occurrence.
##
## Synthetic injection, mirroring `tsymex_phase16_CR1c_internal_fault.nim`:
## the companion `.nim.cfg` sets `-d:symexTestInjectWalkerFault`, under
## which the walker raises an `AssertionDefect` — the exact type a real
## doAssert produces — when dispatch reaches the sentinel
## `symexTarget("__inject_walker_defect__")`. On Windows this also
## exercises the v64 fiber trampoline ferrying a Defect across the fiber
## switch with its dynamic type intact.
import std/unittest
import std/strutils
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

proc defectInjector() =
  symexTarget("__inject_walker_defect__")

suite "symex round-3 — Defect net at the runSymex boundary":

  test "an in-walk AssertionDefect degrades to classified sxUnknown (was: process crash)":
    let r = symexFind(defectInjector, tLabel("__inject_walker_defect__"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    check r.errors.len > 0
    var sawFault = false
    for e in r.errors:
      if e.kind == weInternalWalkerFault and "AssertionDefect" in e.msg:
        sawFault = true
    check sawFault

suite "symex round-3 — walker version pin":

  test "walker version floor >= 64 (Defect net landed with the round-3 batch)":
    check parseInt(symexWalkerVersion) >= 64
