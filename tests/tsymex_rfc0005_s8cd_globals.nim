## RFC-0005 S8cd -- globals: a pointer of unknown origin over a global's
## entry cell (item 2), case-object globals (item 3), and a receiver read
## as a receiver (item 5).
##
## Every expectation is Nim's: the "nim" tests run the SUT natively with the
## global set up as the walker's candidate needs it, and the walker's verdict
## must not contradict the labels that run reached.
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

# --- item 2: a ptr of unknown origin over a global's entry cell -------------

var gJ: int
var gK: tuple[a, b: int]
var gL: array[2, int]
var gM: seq[int]
var gN: seq[int]

proc aliasScalar(p: ptr int) =
  # The SOUNDNESS bug: `gJ` is only read, so it was no target of `p`.
  if p == nil: return
  let a = gJ
  p[] = 7
  if gJ != a: symexTarget("p_scalar")

proc aliasTuple(p: ptr int) =
  if p == nil: return
  let a = gK.a
  p[] = 7
  if gK.a != a: symexTarget("p_tuple")

proc aliasArray(p: ptr int) =
  if p == nil: return
  let a = gL[1]
  p[] = 7
  if gL[1] != a: symexTarget("p_array")

proc aliasSeqElem(p: ptr int) =
  if p == nil: return
  if gM.len == 0: return
  let a = gM[0]
  p[] = 7
  if gM[0] != a: symexTarget("p_seq")

proc aliasTwo(p, q: ptr int) =
  if p == nil or q == nil: return
  p[] = 7
  let g = gJ
  q[] = 8
  if gJ != g: symexTarget("p_two")

proc aliasMustHold(p: ptr int) =
  # `p` is not `gJ`'s, then the store leaves `gJ`: a mere read stays exact.
  if p == nil: return
  let a = gJ
  gJ = a
  p[] = 7
  if gJ != a and gJ != 7: symexTarget("p_dead")

proc noStore(p: ptr int) =
  if p == nil: return
  let a = gJ
  if gJ != a: symexTarget("p_nostore_dead")

proc entryAfterElemWrite(p: ptr int; k: int) =
  # The base declined: `ptrTargets` read the seq's entry cell from
  # `globalEntryVals` only, and an S8as global's entry value was absent.
  gN[0] = k
  if p != nil and p[] == 3: symexTarget("p_ini")

proc popMayDangle(p: ptr int) =
  # A resize may move the buffer: still declines, on this path.
  discard gN.pop()
  if p != nil and p[] == 3: symexTarget("p_dangle")

suite "S8cd item 2: a ptr of unknown origin over a global's entry cell":

  test "nim: every alias is reachable":
    symexCaptureBegin()
    gJ = 0; aliasScalar(addr gJ)
    gK.a = 0; aliasTuple(addr gK.a)
    gL[1] = 0; aliasArray(addr gL[1])
    gM = @[0]; aliasSeqElem(addr gM[0])
    gJ = 0; aliasTwo(addr gJ, addr gJ)
    var z = 3
    gN = @[1]; entryAfterElemWrite(addr z, 1)
    check symexCaptureEnd() ==
      toHashSet(["p_scalar", "p_tuple", "p_array", "p_seq", "p_two", "p_ini"])

  test "a global only read is a target: never sxUnsat":
    candidate(aliasScalar, "p_scalar")
    candidate(aliasTuple, "p_tuple")
    candidate(aliasArray, "p_array")
    candidate(aliasSeqElem, "p_seq")
    candidate(aliasTwo, "p_two")

  test "no store, or a bound global neither value holds: stays dead":
    dead(noStore, "p_nostore_dead")
    dead(aliasMustHold, "p_dead")

  test "the entry cell after a same-length write is a valid target":
    let r = symexFind(entryAfterElemWrite, tLabel("p_ini"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown, sxRaised}
    check not r.errors.hasKind(feUnsupportedOp)

  test "a pop still declines: the pointer may dangle":
    let r = symexFind(popMayDangle, tLabel("p_dangle"))
    checkpoint $r.status & " " & show(r.errors)
    check r.errors.hasKind(feUnsupportedOp)
    check "may dangle" in show(r.errors) or "dangling" in show(r.errors)

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

# --- item 5: a receiver read as a receiver -----------------------------------

type
  One = enum oA, oB, oC
  GOne = object
    # One branch holds every tag: no reassignment can leave it.
    n: int
    case kind: One
    of oA, oB, oC: v: int

var gOne: GOne
var gS: seq[int]
var gA: array[3, int]

proc oneBranch(k: int) =
  gOne.kind = oB
  if k == 1: symexTarget("r_one")

proc oneBranchSym(k: int) =
  gOne.kind = if k == 0: oA else: oC
  if k == 1: symexTarget("r_ones")

proc oneThenDisc(k: int) =
  gOne.kind = oB
  if gOne.kind == oB and k == 1: symexTarget("r_one_disc")
  if gOne.kind != oB: symexTarget("r_one_dead")

proc oneThenPlain(k: int) =
  gOne.kind = oB
  if gOne.n == k: symexTarget("r_one_plain")

proc popReadsLen(k: int) =
  discard gS.pop()
  if k == 1: symexTarget("r_pop")

proc idxWrite(k: int) =
  if gS.len < 2: return
  gS[1] = k
  if gS[1] == 3: symexTarget("r_idx")

proc arrWrite(k: int) =
  gA[1] = k
  if gA[1] == 3: symexTarget("r_arr")

proc arrUntouched(k: int) =
  gA[1] = k
  if gA[0] == 3: symexTarget("r_arr_other")

suite "S8cd item 5: a receiver is not observed whole":

  test "nim":
    symexCaptureBegin()
    oneBranch(1); oneBranchSym(1)
    gOne = GOne(n: 1, kind: oA); oneThenDisc(1)
    gOne = GOne(n: 1, kind: oA); oneThenPlain(1)
    gS = @[1, 2]; popReadsLen(1)
    gS = @[1, 2]; idxWrite(3)
    arrWrite(3)
    gA[0] = 3; arrUntouched(1)
    check symexCaptureEnd() == toHashSet(["r_one", "r_ones", "r_one_disc",
      "r_one_plain", "r_pop", "r_idx", "r_arr", "r_arr_other"])

  test "a reassignment no tag can fail reads no discriminator":
    exact(oneBranch, "r_one")
    exact(oneBranchSym, "r_ones")
    exact(oneThenDisc, "r_one_disc")
    dead(oneThenDisc, "r_one_dead")

  test "an untouched part is observed only when it is read":
    candidate(oneThenPlain, "r_one_plain")
    exact(arrWrite, "r_arr")
    candidate(arrUntouched, "r_arr_other")

  test "seq length and the popped element are read, once each":
    candidate(idxWrite, "r_idx")
    let r = symexFind(popReadsLen, tLabel("r_pop"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown, sxRaised}
    check r.errors.hasKind(feGlobalHavoc)

suite "S8cd":
  test "walker floor":
    check parseInt(symexWalkerVersion) >= 249
