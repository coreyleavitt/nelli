## RFC-0016 W3-z R5b. What `diagnostics` can carry of a raise's soundness.
##
## A path carries `Path.undefined` only through a degrade token whose kind is
## `dcFreshSymbol` (a `{.noinit.}` read, a havoc'd global, an opaque call): the
## path is `scSpurious`, so a raise on it is a CANDIDATE (`admitSolvedHit`),
## never a clean finding. Only a clean finding rides `diagnostics`; a
## candidate is a winner only by a replay confirming it (`settleCandidate`),
## and then it is the verdict, with its own `witnessUndefined`. So a
## diagnostic is never past undefined behaviour, and carries `witnessUnsafe`
## only for a crash raise.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/[types, soundness]

type Node = ref object
  v: int

proc cleanThenRaise(x, m: int) =
  doAssert m != 5
  if x == 7: symexTarget("hit")

proc undefThenRaise(x, m: int) =
  ## The raise at `doAssert` is past an uninitialised read.
  var u {.noinit.}: int
  let y = u + 0
  doAssert m != 5
  if x == 7: symexTarget("hit")

proc crashThenLabel(p: Node, m: int) =
  if m == 5: discard p.v
  if m == 3: symexTarget("hit")

suite "W3-z R5b: the soundness a diagnostic carries":
  test "a non-winning clean raise is host-runnable":
    let r = symexFind(cleanThenRaise, tLabel("hit"))
    check r.status == sxSat
    check r.diagnostics.len == 1
    check r.diagnostics[0].witnessUndefined == {}
    check not r.diagnostics[0].witnessUnsafe
    check hostRunnable(allRaiseFindings(r)[0])

  test "a non-winning crash raise is not host-runnable":
    let r = symexFind(crashThenLabel, tLabel("hit"))
    checkpoint $r.status & " " & $r.diagnostics.len
    check r.status == sxSat
    check r.diagnostics.len == 1
    check r.diagnostics[0].witnessUnsafe
    check r.diagnostics[0].witnessUndefined == {}
    check not hostRunnable(allRaiseFindings(r)[0])

  test "a raise past an undefined read is a candidate, not a diagnostic":
    let r = symexFind(undefThenRaise, tLabel("hit"))
    checkpoint $r.status & " " & $r.diagnostics.len
    for d in r.diagnostics:
      check d.witnessUndefined == {}
    check r.diagnostics.len == 0
