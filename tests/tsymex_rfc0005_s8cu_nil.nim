## RFC-0005 S8cu -- a nil dereference is a crash no `except` and no `finally` sees.
##
## Natively (Nim 2.2.10) it is a SIGSEGV: by default, with `--panics:on`, under
## `-d:danger`, with clang and on cpp, under `except NilAccessDefect`, `except
## Defect`, a bare `except` and a `finally`. `std/segfaults` makes it catchable
## only with `--exceptions:setjmp`; there a dereference under a `try` declines
## (`heNilDerefMayBeCaught`). The walker routed it as an ordinary raise: a label
## in the handler was a false sxSat and `tNilAccess` a false sxUnsat.
##
## A crash cannot run in this process, so each native row runs this binary again
## with `native:<form>`; it prints `RAN` only if it returns.
import std/[unittest, os, osproc, strutils, sets]
import nelli
import nelli/symex
import ./s8cu_helpers

const declKey = cellKey(faGeneric, "s8cu_nil")

type R = ref object
  a: int

var gR: R

proc direct(v: int) =
  var r: R = nil
  try:
    if v == 4:
      let x = r.a
      if x == 12345: symexTarget("never")
    symexTarget("after")
  except NilAccessDefect:
    symexTarget("hit")

proc param(r: R; v: int) =
  try:
    let x = r.a
    if x == 5 and v == 1: symexTarget("ok")
  except NilAccessDefect:
    symexTarget("hit")

proc paramDefect(r: R; v: int) =
  try:
    let x = r.a
    if x == 5 and v == 1: symexTarget("ok")
  except Defect:
    symexTarget("hit")

proc paramBare(r: R; v: int) =
  try:
    let x = r.a
    if x == 5 and v == 1: symexTarget("ok")
  except:
    symexTarget("hit")

proc paramFinally(r: R; v: int) =
  try:
    let x = r.a
    if x == 5 and v == 1: symexTarget("ok")
  finally:
    symexTarget("hit")

proc captured(v: int) =
  var r: R = nil
  let f = proc (): int = r.a
  try:
    if v == 4:
      let x = f()
      if x == 12345: symexTarget("never")
  except NilAccessDefect:
    symexTarget("hit")

proc global(v: int) =
  try:
    if v == 4:
      let x = gR.a
      if x == 12345: symexTarget("never")
  except NilAccessDefect:
    symexTarget("hit")

proc derefLit(v: int) =
  var p: ref int = nil
  try:
    if v == 4:
      let x = p[]
      if x == 12345: symexTarget("never")
  except NilAccessDefect:
    symexTarget("hit")

proc readIt(r: R): int = r.a
proc inCallee(r: R; v: int) =
  try:
    let x = readIt(r)
    if x == 5 and v == 1: symexTarget("ok")
  except NilAccessDefect:
    symexTarget("hit")

if paramCount() >= 1 and paramStr(1).startsWith("native:"):
  symexCaptureBegin()
  case paramStr(1)
  of "native:direct": direct(4)
  of "native:param": param(nil, 1)
  of "native:paramDefect": paramDefect(nil, 1)
  of "native:paramBare": paramBare(nil, 1)
  of "native:paramFinally": paramFinally(nil, 1)
  of "native:captured": captured(4)
  of "native:global": global(4)
  of "native:derefLit": derefLit(4)
  of "native:inCallee": inCallee(nil, 1)
  else: discard
  echo "RAN ", symexCaptureEnd().len
  quit 0

proc crashes(form: string): bool =
  ## The form ran natively in a child process and ended before returning.
  let (output, rc) = execCmdEx(quoteShell(getAppFilename()) & " native:" & form)
  checkpoint form & ": rc=" & $rc & " " & output.splitLines()[0]
  rc != 0 and "RAN" notin output

template crashFinding(fn: untyped) =
  ## The label behind the handler: the walk finds the crash, not the label.
  let r = symexFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxRaised
  check r.raisedTypeId == "NilAccessDefect"
  let n = symexFind(fn, tNilAccess())
  check n.status == sxRaised

suite "S8cu: a nil dereference crashes":

  test "a nil literal, then a field read under `except NilAccessDefect`":
    check crashes("direct")
    crashFinding(direct)

  test "a parameter, under each handler that would match":
    check crashes("param")
    crashFinding(param)
    check crashes("paramDefect")
    crashFinding(paramDefect)
    check crashes("paramBare")
    crashFinding(paramBare)

  test "a `finally` does not run on the nil input":
    check crashes("paramFinally")
    let n = symexFind(paramFinally, tNilAccess())
    check n.status == sxRaised
    # Reached on a non-nil input, natively as well.
    check native(paramFinally(R(a: 1), 1)) == "hit"
    decides(paramFinally, sxSat)

  test "captured by a closure":
    check crashes("captured")
    crashFinding(captured)

  test "`r[]` of a nil literal":
    check crashes("derefLit")
    crashFinding(derefLit)

  test "in a callee, with the handler in the caller":
    check crashes("inCallee")
    crashFinding(inCallee)

  test "a global ref declines (not modelled)":
    check crashes("global")
    pinDecline(global, declKey, feGlobalReadUnmodelled)
