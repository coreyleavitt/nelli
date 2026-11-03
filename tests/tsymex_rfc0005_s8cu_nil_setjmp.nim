## RFC-0005 S8cu -- a nil dereference in a `--exceptions:setjmp` build (`.nim.cfg`).
##
## Only here does `std/segfaults` make it a catchable `NilAccessDefect` (and run a
## `finally`). The walker does not read whether the program imports it, so a
## dereference under a `try` declines; one under no `try` is still the crash.
## This file imports `std/segfaults`, so the native rows catch it. Each runs in a
## child process (`native:<form>`), which prints `RAN` and the labels it reached.
##
## The cpp backend cannot build `--exceptions:setjmp`, so the `.nim.cfg` applies
## it to c only. On cpp (`--exceptions:cpp`) `std/segfaults` leaves the defect
## unhandled natively, and the suite pins the crash finding there instead.
import std/[unittest, os, osproc, strutils, sets, segfaults]
import nelli
import nelli/symex
import ./s8cu_helpers

type R = ref object
  a: int

proc param(r: R; v: int) =
  try:
    let x = r.a
    if x == 5 and v == 1: symexTarget("ok")
  except NilAccessDefect:
    symexTarget("hit")

proc readIt(r: R): int = r.a
proc inCallee(r: R; v: int) =
  try:
    let x = readIt(r)
    if x == 5 and v == 1: symexTarget("ok")
  finally:
    symexTarget("hit")

proc unguarded(r: R; v: int) =
  let x = r.a
  if x == 5 and v == 1: symexTarget("hit")

if paramCount() >= 1 and paramStr(1).startsWith("native:"):
  symexCaptureBegin()
  case paramStr(1)
  of "native:param": param(nil, 1)
  else: discard
  let hits = symexCaptureEnd()
  echo "RAN ", (if "hit" in hits: "hit" else: "-")
  quit 0

suite "S8cu: a nil dereference with --exceptions:setjmp":

  when compileOption("exceptions", "setjmp"):
   test "with std/segfaults the handler runs natively, so the walk declines":
    let (output, rc) = execCmdEx(quoteShell(getAppFilename()) & " native:param")
    checkpoint "rc=" & $rc & " " & output
    check rc == 0
    check "RAN hit" in output
    declines(param, heNilDerefMayBeCaught)

   test "a `finally` in the caller guards a callee's dereference too":
    # The label in the `finally` is reached on a non-nil input (sxSat); the nil
    # dereference itself is what declines.
    let r = symexFind(inCallee, tNilAccess())
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(heNilDerefMayBeCaught)

  else:
   test "cpp exceptions: std/segfaults does not catch it, so it is the crash":
    let (output, rc) = execCmdEx(quoteShell(getAppFilename()) & " native:param")
    checkpoint "rc=" & $rc & " " & output
    check rc != 0
    check "RAN" notin output
    let r = symexFind(param, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxRaised
    check r.raisedTypeId == "NilAccessDefect"

  test "under no `try` it is the crash finding":
    let r = symexFind(unguarded, tNilAccess())
    checkpoint show(r.errors)
    check r.status == sxRaised
    check r.raisedTypeId == "NilAccessDefect"
