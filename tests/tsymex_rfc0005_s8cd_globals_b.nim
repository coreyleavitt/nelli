## RFC-0005 S8cd -- globals: a pointer of unknown origin over a global's
## entry cell (item 2), case-object globals (item 3), and a receiver read
## as a receiver (item 5).
##
## Every expectation is Nim's: the "nim" tests run the SUT natively with the
## global set up as the walker's candidate needs it, and the walker's verdict
## must not contradict the labels that run reached.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8cd_globals`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 68 s).

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
  ## Reachable for some entry value: never `sxUnsat`, never a fault. The hit
  ## needs an entry value the replay does not set, so `feGlobalHavoc`.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown, sxRaised}
    check r.errors.hasKind(feGlobalHavoc)
    check not r.errors.hasKind(weInternalWalkerFault)

template dead(fn: typed, lbl: string) =
  ## Unreachable for every entry value.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnsat

template exact(fn: typed, lbl: string) =
  ## Reached with nothing unwritten observed.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feGlobalHavoc)

template confirmed(fn: typed, lbl: string) =
  ## Reached and replayed to the target: the entry value the replay runs on
  ## is one the hit can use.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feReplayRefuted)

# --- item 3: case-object globals ---------------------------------------------

type
  GK = enum gkA, gkB
  GV = object
    case kind: GK
    of gkA: a: int
    of gkB: b: string
  GW = object
    tag: int
    case kind: GK
    of gkA: x: int
    of gkB: ys: seq[int]
  GM = object
    case p: bool
    of true: pa: int
    of false: pb: int
    case q: GK
    of gkA: qa: int
    of gkB: qb: int

var gV: GV
var gW: GW
var gMV: GM
var gVArr: array[2, GV]

proc readDisc(k: int) =
  if gV.kind == gkA and k == 1: symexTarget("v_disc_a")
  if gV.kind == gkB and k == 1: symexTarget("v_disc_b")
  if gV.kind == gkA and gV.kind == gkB: symexTarget("v_disc_dead")

proc readArm(k: int) =
  try:
    if gV.a == k: symexTarget("v_arm")
  except FieldDefect:
    symexTarget("v_arm_raise")

proc readWrongArmAfterWrite(k: int) =
  gV = GV(kind: gkA, a: k)
  if gV.a == 2: symexTarget("v_write")
  if gV.kind == gkB: symexTarget("v_write_dead")
  try:
    if gV.b == "x": symexTarget("v_wrong_dead")
  except FieldDefect:
    symexTarget("v_wrong_raise")

proc reassign(k: int) =
  try:
    gV.kind = gkB
  except FieldDefect:
    symexTarget("v_re_raise")
  if k == 1: symexTarget("v_re_after")

proc reassignSym(k: int) =
  let t = if k == 0: gkA else: gkB
  try:
    gV.kind = t
    if k == 2: symexTarget("v_res_after")
  except FieldDefect:
    symexTarget("v_res_raise")

proc caseDispatch(k: int) =
  case gV.kind
  of gkA:
    if gV.a == k: symexTarget("v_case_a")
  of gkB:
    if gV.b == "x": symexTarget("v_case_b")

proc plainAndArm() =
  if gW.tag == 2 and gW.kind == gkB and gW.ys.len == 1: symexTarget("w_all")

proc multiAxis(k: int) =
  if gMV.p and gMV.q == gkB and k == 1: symexTarget("m_axes")
  if gMV.p and not gMV.p: symexTarget("m_dead")

proc multiArmRaise() =
  try:
    if gMV.pb == 1: symexTarget("m_arm")
  except FieldDefect:
    symexTarget("m_raise")

proc arrElem(k: int) =
  if gVArr[1].kind == gkA and k == 2: symexTarget("v_elem")
  if gVArr[1].kind == gkA and gVArr[1].kind == gkB: symexTarget("v_elem_dead")

type GR = object
  case kind: GK
  of gkA: r: ref int
  of gkB: n: int

var gR: GR

proc refArmReassign(k: int) =
  # A case object reaching a heap cell has no entry-value model.
  try:
    gR.kind = gkB
    if k == 1: symexTarget("gr_after")
  except FieldDefect:
    symexTarget("gr_raise")

proc armAlias(p: ptr int) =
  # A pointer may address the arm field of a global only read.
  if p == nil or gV.kind != gkA: return
  let a = gV.a
  p[] = 7
  if gV.a != a: symexTarget("v_ptr")

proc viaUnknownCall(f: proc(); k: int) =
  # A call the walk cannot resolve may write the global.
  let a = gV.kind
  f()
  if gV.kind != a and k == 1: symexTarget("v_havoc")

proc opaqueWrite() {.noinline.} =
  {.cast(noSideEffect).}:
    gV = GV(kind: gkB, b: "w")

proc viaOpaque(k: int) =
  let a = gV.kind
  opaqueWrite()
  if gV.kind != a and k == 1: symexTarget("v_opaque")

suite "S8cd item 3: case-object globals":

  test "nim: an alias of an arm field, a write by a later call":
    symexCaptureBegin()
    gV = GV(kind: gkA, a: 0); armAlias(addr gV.a)
    gV = GV(kind: gkA, a: 0)
    viaUnknownCall(proc() = gV = GV(kind: gkB, b: "w"), 1)
    gV = GV(kind: gkA, a: 0); viaOpaque(1)
    check symexCaptureEnd() == toHashSet(["v_ptr", "v_havoc", "v_opaque"])

  test "a global's arm field is a pointer's target, a later call may write it":
    candidate(armAlias, "v_ptr")
    let r = symexFind(viaUnknownCall, tLabel("v_havoc"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    let r2 = symexFind(viaOpaque, tLabel("v_opaque"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status != sxUnsat


  test "nim: with the global set up, each label is reached":
    symexCaptureBegin()
    gV = GV(kind: gkB, b: "x")
    readDisc(1); readArm(0); reassign(1); caseDispatch(0)
    reassignSym(1)
    gV = GV(kind: gkA, a: 0)
    readDisc(1); readArm(0); readWrongArmAfterWrite(2); reassign(1)
    caseDispatch(0)
    gV = GV(kind: gkA, a: 0); reassignSym(1)
    gV = GV(kind: gkA, a: 0); reassignSym(0)
    gV = GV(kind: gkA, a: 0); caseDispatch(0)
    gW = GW(tag: 2, kind: gkB, ys: @[1]); plainAndArm()
    gMV = GM(p: true, q: gkB); multiAxis(1); multiArmRaise()
    gVArr[1] = GV(kind: gkA, a: 0); arrElem(2)
    let hit = symexCaptureEnd()
    for lbl in ["v_disc_a", "v_disc_b", "v_arm", "v_arm_raise", "v_write",
                "v_wrong_raise", "v_re_raise", "v_re_after", "v_case_a",
                "v_case_b", "v_res_raise", "w_all", "m_axes", "m_raise",
                "v_elem"]:
      checkpoint lbl
      check lbl in hit
    for lbl in ["v_disc_dead", "v_write_dead", "v_wrong_dead", "m_dead",
                "v_elem_dead"]:
      checkpoint lbl
      check lbl notin hit

  test "the discriminator's entry value: each tag a candidate":
    # `gV` holds `gkA` on replay, so the first hit replays to its target.
    confirmed(readDisc, "v_disc_a")
    candidate(readDisc, "v_disc_b")
    dead(readDisc, "v_disc_dead")

  test "an arm field read forks FieldDefect over the entry tag":
    candidate(readArm, "v_arm")
    candidate(readArm, "v_arm_raise")

  test "a written global is exact, its wrong arm raises":
    exact(readWrongArmAfterWrite, "v_write")
    dead(readWrongArmAfterWrite, "v_write_dead")
    dead(readWrongArmAfterWrite, "v_wrong_dead")
    exact(readWrongArmAfterWrite, "v_wrong_raise")

  test "a discriminator reassignment forks FieldDefect over the entry tag":
    candidate(reassign, "v_re_raise")
    candidate(reassign, "v_re_after")
    candidate(reassignSym, "v_res_raise")

  test "case dispatch, plain field and seq arm field":
    candidate(caseDispatch, "v_case_a")
    candidate(caseDispatch, "v_case_b")
    candidate(plainAndArm, "w_all")

  test "a multi-axis case object":
    candidate(multiAxis, "m_axes")
    dead(multiAxis, "m_dead")
    candidate(multiArmRaise, "m_raise")

  test "a case object reaching a heap cell declines, never sxUnsat":
    template declines(lbl: string) =
      let r = symexFind(refArmReassign, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check not r.errors.hasKind(weInternalWalkerFault)
    block: declines("gr_after")
    block: declines("gr_raise")

  test "a case object held in an array global":
    candidate(arrElem, "v_elem")
    dead(arrElem, "v_elem_dead")
