## RFC-0005 batch 6 -- a statement whose receiver is a module-level
## variable the walk has not yet written.
##
## S8as models a global read before any write as its ENTRY value
## (`entryValueOf`, `feGlobalHavoc`), through `lower`'s `iekVar` arm. The
## statement arms that name their receiver directly -- `xs[i] = v`
## (`isIndexAssign`), `xs.pop()` (`isSeqPop`) and the discriminator
## reassignments `o.kind = k` (`isVariantReassign`,
## `isVariantReassignSymbolic`) -- read it straight from `Env` instead. A
## global not yet in `Env` raised `KeyError` there: the index assignment
## dropped the path (a reachable target was a false `sxUnsat`, with no
## decline) and the pop reported a walker fault. The reassignment arms
## skipped the statement, so its `FieldDefect` was never forked (a false
## `sxUnsat`, no error). Every arm now reads an unbound receiver as `lower`
## reads the name (`recvValue`).
##
## Every expectation below is Nim's (the "nim" tests run each SUT
## natively).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template candidate(fn: typed, lbl: string) =
  ## The target is reachable: never `sxUnsat`. A hit needs an entry value
  ## of the global, which the replay does not set, so the path carries
  ## `feGlobalHavoc`.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check r.errors.hasKind(feGlobalHavoc)
    check not r.errors.hasKind(weInternalWalkerFault)

template declinesGlobal(fn: typed, lbl: string) =
  ## The global's type has no entry-value model (`programGlobal` holds
  ## none for a case object): the walk declines, never `sxUnsat`.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feGlobalReadUnmodelled)
    check not r.errors.hasKind(weInternalWalkerFault)

template dead(fn: typed, lbl: string) =
  ## Unreachable for every entry value.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnsat
    check not r.errors.hasKind(weInternalWalkerFault)

var gS: seq[int]

proc sutIndexAssign(k: int) =
  if gS.len < 2: return
  gS[1] = k
  if gS[1] == 3: symexTarget("gia")
  if gS[1] != k: symexTarget("gia_dead")

proc sutIndexAssignOob(k: int) =
  try:
    gS[k] = 1
  except IndexDefect:
    if k >= 0: symexTarget("gia_oob")

proc sutPop(k: int) =
  if gS.len < 1: return
  let x = gS.pop()
  if x == k: symexTarget("gpop")

proc sutPopEmpty(k: int) =
  try:
    discard gS.pop()
  except IndexDefect:
    symexTarget("gpop_empty")

type
  GK = enum gkA, gkB
  GV = object
    case kind: GK
    of gkA: a: int
    of gkB: b: int

var gV: GV

proc sutReassign(k: int) =
  try:
    gV.kind = gkB
  except FieldDefect:
    symexTarget("grs_raise")
  if k == 1: symexTarget("grs_after")

proc sutReassignSym(k: int) =
  let t = if k == 0: gkA else: gkB
  try:
    gV.kind = t
  except FieldDefect:
    symexTarget("grss_raise")

suite "batch 6: a statement on an unbound global receiver":
  test "nim":
    symexCaptureBegin()
    gS = @[5, 6]
    sutIndexAssign(3)
    gS = @[]
    sutIndexAssignOob(0)
    gS = @[7]
    sutPop(7)
    gS = @[]
    sutPopEmpty(0)
    {.cast(uncheckedAssign).}:
      gV = GV(kind: gkA)
    sutReassign(1)
    {.cast(uncheckedAssign).}:
      gV = GV(kind: gkA)
    sutReassignSym(1)
    let h = symexCaptureEnd()
    checkpoint $h
    for l in ["gia", "gia_oob", "gpop", "gpop_empty", "grs_raise",
              "grs_after", "grss_raise"]:
      checkpoint l
      check l in h
    check "gia_dead" notin h

  test "an index assignment (was a false sxUnsat)":
    candidate(sutIndexAssign, "gia")
    dead(sutIndexAssign, "gia_dead")
  test "an index assignment's IndexDefect":
    candidate(sutIndexAssignOob, "gia_oob")
  test "a pop (was a false sxUnsat)":
    candidate(sutPop, "gpop")
  test "an empty pop's IndexDefect":
    candidate(sutPopEmpty, "gpop_empty")
  test "a discriminator reassignment's FieldDefect (was a false sxUnsat)":
    # A case-object global is not modelled (`feGlobalReadUnmodelled`); the
    # arm skipped the statement, so the raise was `sxUnsat` with no error
    # and the label after it a clean `sxSat` over a write it never made.
    declinesGlobal(sutReassign, "grs_raise")
    declinesGlobal(sutReassign, "grs_after")
  test "a symbolic discriminator reassignment's FieldDefect":
    declinesGlobal(sutReassignSym, "grss_raise")

