## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 6 of 8 of this suite, with
## `tsymex_rfc0005_s8ar_remainder`, `tsymex_rfc0005_s8ar_remainder_b`,
## `tsymex_rfc0005_s8ar_remainder_c`, `tsymex_rfc0005_s8ar_remainder_d`,
## `tsymex_rfc0005_s8ar_remainder_g`, `tsymex_rfc0005_s8ar_remainder_h`,
## `tsymex_rfc0005_s8ar_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 120 s).
import std/[unittest, strutils, sequtils, tables, sets]
import nelli
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

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

type
  TabHolder = ref object
    ti: Table[int, int]
    ts: Table[string, string]
    tf: Table[string, float]
    tb: Table[bool, int8]
  BadTab = ref object
    tq: Table[string, seq[int]]
    n: int
  OddHolder = ref object
    hs: HashSet[string]
    bad: Table[string, (int, int)]   ## RFC-0005 S8at: was `seq[int]`, now backed
    n: int

proc tOdd(p: OddHolder) =
  if p != nil and p.n == 9: symexTarget("t_odd")

suite "S8ar (7): a container a ref pointee holds no longer demotes the parameter":
  test "a HashSet[string] and an unbacked Table field beside an int field":
    let r = symexFind(tOdd, tLabel("t_odd"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedWitnessType)
    if r.status == sxSat: check reproduces(tOdd(r.witness[0]), "t_odd")

type
  WKind = enum wkA, wkB
  WVar = ref object
    case kind: WKind
    of wkA: xs: seq[int]
    of wkB: hs: HashSet[int8]
  WHolder = ref object
    tp: (seq[int], int)
    a2: array[2, seq[int]]
    tt: Table[int, int]
    hs: HashSet[int8]
  ByValVar = object
    case kind: WKind
    of wkA: a: int
    of wkB: b: bool
  DSeq = distinct seq[int]
  DeclHolder = ref object
    bv: ByValVar
    n: int
  DeclHolder2 = ref object
    ds: DSeq
    n: int

proc wfTree(p: WHolder) =
  if p == nil: return
  if p.tp[0].len < 0 or p.tp[0].len > 1024: symexTarget("wf_tp_dead")
  if p.a2[1].len < 0: symexTarget("wf_a2_dead")
  if p.tt.len == 0 and 3 in p.tt: symexTarget("wf_tt_dead")
  if p.hs.len > 256: symexTarget("wf_hs_dead")
  if p.tp[0].len == 2 and p.a2[1].len == 1 and 3 in p.tt and p.hs.len == 256:
    symexTarget("wf_tree")

proc wfArm(p: WVar) =
  if p == nil: return
  if p.kind == wkA and p.xs.len < 0: symexTarget("wf_arm_dead")
  if p.kind == wkB and p.hs.len > 256: symexTarget("wf_arm_set_dead")
  if p.kind == wkA and p.xs.len == 3: symexTarget("wf_arm")

proc wfWritten(p: WHolder, v: int) =
  if p == nil: return
  p.tp = (@[v], 1)
  if p.tp[0].len != 1: symexTarget("wf_written_dead")

suite "S8ar (10): every read of a cell asserts its well-formedness":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "tree parts: a nested seq, an array of seqs, a cell-keyed Table, a HashSet":
    discard run(wfTree, "wf_tp_dead", sxUnsat)
    discard run(wfTree, "wf_a2_dead", sxUnsat)
    discard run(wfTree, "wf_tt_dead", sxUnsat)
    discard run(wfTree, "wf_hs_dead", sxUnsat)
    let r = run(wfTree, "wf_tree", sxSat)
    if r.status == sxSat: check reproduces(wfTree(r.witness[0]), "wf_tree")

  test "a ref variant's arm cells":
    discard run(wfArm, "wf_arm_dead", sxUnsat)
    discard run(wfArm, "wf_arm_set_dead", sxUnsat)
    let r = run(wfArm, "wf_arm", sxSat)
    if r.status == sxSat: check reproduces(wfArm(r.witness[0]), "wf_arm")

  test "a written cell is the value the program built":
    discard run(wfWritten, "wf_written_dead", sxUnsat)
