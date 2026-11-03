## RFC-0005 (soundness channels) slice S8as -- S8an's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8as_remainder_b`, `tsymex_rfc0005_s8as_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 80 s).

import std/[unittest, strutils, math]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

template notUnsat(fn: typed, lbl: string, kind: SymexErrorKind) =
  ## No longer a false `sxUnsat`: the walk models the write as a fresh value
  ## (`kind` recorded), so the target is a candidate. Replay decides it: the
  ## solver's witness need not be one that reaches it for real.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check r.errors.hasKind(kind)
    check not r.errors.hasKind(weInternalWalkerFault)

template clean(fn: typed, lbl: string, want: SymexStatusKind) =
  ## The verdict, with nothing recorded at all.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0

# ---- (2) an opaque call writes a module-level variable ----------------------
#
# WRONG VERDICT before S8as: an inert opaque call (statement position, value
# arguments) was a no-op for the walk, on the argument that the walker did
# not model globals; S8an made it model them. `gOp` kept the value written
# before the call: `og` was a false `sxUnsat` with `errors` empty. Probed:
# `sutOpaqueGlobal(5)` reaches `og`.

var gOp: int

proc opSet(a: int) {.symexOpaque.} =
  gOp = a

proc opSetDeep(a: int) {.symexOpaque.} =
  opSet(a + 1)

proc sutOpaqueGlobal(v: int) =
  gOp = 0
  opSet(v)
  if gOp == 5: symexTarget("og")

proc sutOpaqueGlobalDeep(v: int) =
  gOp = 0
  opSetDeep(v)            # writes `gOp` through the routine it calls
  if gOp == 5: symexTarget("ogd")

proc opNoWrite(a: int) {.symexOpaque.} =
  discard a

proc sutOpaqueNoWrite(v: int) =
  gOp = 0
  opNoWrite(v)            # its summary is empty: `gOp` keeps 0
  if gOp == 0 and v == 1: symexTarget("onw")
  if gOp != 0: symexTarget("onw_dead")

proc sutNestedOpaque(v: int) =
  # WRONG VERDICT before S8as, the capture twin: `c` kept 0.
  var c = 0
  proc setc(a: int) {.symexOpaque.} =
    c = a
  setc(v)
  if c == 5: symexTarget("no")

# ---- (3) a module-level variable read before any write ----------------------

var gInit = 7
let gLet = 9
let gLetComputed = gInit * 2

proc sutGlobalEntry(x: int) =
  if gInit == 7 and x == 1: symexTarget("ge")
  let a = gInit
  if a != gInit: symexTarget("ge_dead")

proc sutLetLiteral(x: int) =
  if gLet == 9 and x == 1: symexTarget("ll")
  if gLet != 9: symexTarget("ll_dead")

proc sutLetComputed(x: int) =
  if gLetComputed == 14 and x == 1: symexTarget("lc")

proc readG(): int = gInit

proc sutCalleeEntry(x: int) =
  # A callee reads the entry value, the caller then writes: the callee's
  # second read sees the write.
  discard readG()
  gInit = 3
  if readG() == 3 and x == 2: symexTarget("ce")
  if readG() != 3: symexTarget("ce_dead")

proc sutClosureGlobal(v: int) =
  # A closure body reads the global the caller wrote (it declined).
  gOp = 0
  let f = proc (): int = gOp
  gOp = v                 # after the closure was built
  if f() == 3: symexTarget("cg")
  if f() != v: symexTarget("cg_dead")

suite "RFC-0005 S8as: walker version":
  test "symexWalkerVersion is at least 192":
    check parseInt(symexWalkerVersion) >= 192

suite "RFC-0005 S8as (2): an opaque call's writes":
  test "an opaque routine's write to a global reaches the caller":
    notUnsat(sutOpaqueGlobal, "og", feGlobalHavoc)
  test "through a routine it calls":
    notUnsat(sutOpaqueGlobalDeep, "ogd", feGlobalHavoc)
  test "a routine that writes nothing leaves the global as it was, clean":
    clean(sutOpaqueNoWrite, "onw", sxSat)
    clean(sutOpaqueNoWrite, "onw_dead", sxUnsat)
  test "a nested opaque routine's write to its capture reaches it":
    notUnsat(sutNestedOpaque, "no", feGlobalHavoc)

suite "RFC-0005 S8as (3): a global's entry value":
  test "a var global read before any write holds its entry value":
    verdict(sutGlobalEntry, "ge", sxSat)
    verdict(sutGlobalEntry, "ge_dead", sxUnsat)
  test "a let global initialised by a literal reads the literal, clean":
    clean(sutLetLiteral, "ll", sxSat)
    clean(sutLetLiteral, "ll_dead", sxUnsat)
  test "a let global with a computed initialiser holds a fresh value":
    verdict(sutLetComputed, "lc", sxSat)
  test "a callee reads the entry value and then the caller's write":
    verdict(sutCalleeEntry, "ce", sxSat)
    verdict(sutCalleeEntry, "ce_dead", sxUnsat)
  test "a closure body reads the global as the caller holds it":
    verdict(sutClosureGlobal, "cg", sxSat)
    verdict(sutClosureGlobal, "cg_dead", sxUnsat)
