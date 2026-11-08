## RFC-0016 K2-0 -- the probe batch, part 2: the hang probes W-22 (`parseBool`
## on a length-4 string) and CRH-08 (`cmpIgnoreStyle`), and INT-22, PND-13 and
## HRV-06, which need a child process or share these fixtures. Each walks in a CHILD of this binary (the
## test re-executes itself with `K20_CHILD=<name>`), so a hang is observed, not
## suffered: the parent gives the child `childBudgetSecs`, then kills it.
##
## A child writes a marker file just before it calls `symexFind`, so a child
## that is still running after the budget is hung inside the walk and not still
## starting. A control child (`small`) takes the same route and must finish,
## which shows the budget is long enough for an ordinary walk.
##
## These pin the CURRENT behaviour of a known defect: when a hang is fixed the
## test fails, and the row (W-22, CRH-08) is then re-pinned with `pinExact` or
## `pinDecline`.
import std/[streams, unittest, os, osproc, strutils, times, sets, macros, tables]
import nelli
import nelli/symex
import ./s8cu_helpers

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("k20h_pins_" & $getCurrentProcessId()))

const childBudgetSecs = 25.0

proc parseBoolLen4(s: string) =
  if s.len == 4:
    try:
      if parseBool(s): symexTarget("hit")
    except ValueError: discard

proc cmpStyle(a: string) =
  if cmpIgnoreStyle(a, "abc") == 0: symexTarget("hit")

proc small(k: int) =
  if k * 3 == 21: symexTarget("hit")

proc quitAfter(k: int) =
  if k == 5:
    symexTarget("hit")
    quit(0)

macro chainAdd(n: static int): untyped =
  result = newStmtList()
  for i in 0 ..< n:
    result.add parseStmt("x = x + " & $(i + 1))
proc bigTerm(k: int) =
  var x = k
  chainAdd(1500)
  let a = [1, 2, 3, 4]
  if a[x and 3] == 3: symexTarget("hit")
proc bigEq(k: int) =
  var x = k
  chainAdd(1500)
  if x == 1125751: symexTarget("hit")
proc smallIdx(k: int) =
  var x = k
  chainAdd(40)
  let a = [1, 2, 3, 4]
  if a[x and 3] == 3: symexTarget("hit")

type VK = enum va, vb, vc, vd, ve
type DI = distinct int
type V6 = object
  case k: VK
  of va: t: Table[string, int]
  of vb: s: HashSet[int]
  of vc: a: array[3, int]
  of vd: d: DI
  of ve: q: (int, string)
proc omitTable(k: int) =
  let v = V6(k: va)
  if v.k == va and k == 3: symexTarget("hit")
proc omitSet(k: int) =
  let v = V6(k: vb)
  if v.k == vb and k == 3: symexTarget("hit")
proc omitArr(k: int) =
  let v = V6(k: vc)
  if v.k == vc and v.a[1] == 0 and k == 3: symexTarget("hit")
proc omitDistinct(k: int) =
  let v = V6(k: vd)
  if v.k == vd and int(v.d) == 0 and k == 3: symexTarget("hit")
proc omitTuple(k: int) =
  let v = V6(k: ve)
  if v.k == ve and v.q[0] == 0 and k == 3: symexTarget("hit")

proc childMain(name: string) =
  let mark = getEnv("K20_MARK")
  writeFile(mark, "entered")
  var st = ""
  case name
  of "parseBool": st = $symexFind(parseBoolLen4, tLabel("hit"), pinSettingsConst).status
  of "cmpIgnoreStyle": st = $symexFind(cmpStyle, tLabel("hit"), pinSettingsConst).status
  of "bigTerm":
    let r = symexFind(bigTerm, tLabel("hit"), pinSettingsConst)
    st = $r.status & " " & show(r.errors)
  of "bigEq":
    let r = symexFind(bigEq, tLabel("hit"), pinSettingsConst)
    st = $r.status & " " & show(r.errors)
  of "smallIdx":
    let r = symexFind(smallIdx, tLabel("hit"), pinSettingsConst)
    st = $r.status & " " & show(r.errors)
  of "quit":
    let r = symexFind(quitAfter, tLabel("hit"), pinSettingsConst)
    echo "VERDICT ", r.status, " ", show(r.errors)
    echo "ASSERTING"
    discard assertCoveredBy(quitAfter, tLabel("hit"))
    echo "SURVIVED"
  of "small": st = $symexFind(small, tLabel("hit"), pinSettingsConst).status
  else: quit(2)
  echo "VERDICT ", st

type ChildRun = object
  entered, hung: bool
  rc: int
  output: string
  secs: float

proc runChild(name: string): ChildRun =
  let mark = getTempDir() / ("k20_mark_" & name & "_" & $getCurrentProcessId())
  removeFile(mark)
  putEnv("K20_CHILD", name)
  putEnv("K20_MARK", mark)
  let t0 = epochTime()
  let p = startProcess(getAppFilename(), options = {poStdErrToStdOut})
  delEnv("K20_CHILD")
  while p.running and epochTime() - t0 < childBudgetSecs: sleep(25)
  result.hung = p.running
  if result.hung: p.kill()
  else:
    result.rc = p.peekExitCode()
    result.output = p.outputStream.readAll()
  result.secs = epochTime() - t0
  result.entered = fileExists(mark)
  p.close()
  removeFile(mark)

if getEnv("K20_CHILD").len > 0:
  childMain(getEnv("K20_CHILD"))
else:
  suite "RFC-0016 K2-0: hangs":
    test "the SUTs run natively (the walk is what hangs)":
      for s in ["true", "TRUE", "t_rue", "nope", "abcd"]:
        let r = nativeRun(parseBoolLen4(s))
        check r.raised.len == 0
      check "hit" in nativeRun(parseBoolLen4("true")).hits
      check "hit" in nativeRun(cmpStyle("A_b_C")).hits
      check "hit" notin nativeRun(cmpStyle("abd")).hits

    test "control: an ordinary walk finishes inside the budget":
      let c = runChild("small")
      checkpoint c.output
      check not c.hung
      check c.rc == 0
      check "VERDICT sxSat" in c.output

    test "W-22: parseBool on a length-4 string hangs the walk":
      let c = runChild("parseBool")
      checkpoint "hung=" & $c.hung & " secs=" & $c.secs & " out=" & c.output
      check c.entered
      check c.hung
      skipCell(cellKey(axStdlibBody, "strutils.parseBool/len4"),
               "K2-0 W-22: symexFind hangs (no budget bites; killed at " &
               $int(childBudgetSecs) & " s); a known defect pinned as the observed outcome")

    test "CRH-08: cmpIgnoreStyle hangs the walk":
      let c = runChild("cmpIgnoreStyle")
      checkpoint "hung=" & $c.hung & " secs=" & $c.secs & " out=" & c.output
      check c.entered
      check c.hung
      skipCell(cellKey(axStdlibBody, "strutils.cmpIgnoreStyle"),
               "K2-0 CRH-08: symexFind hangs (killed at " & $int(childBudgetSecs) &
               " s); a known defect pinned as the observed outcome")

    test "INT-22: a clean faithful winner whose witness ends the process ends assertCoveredBy's host":
      # The verdict is a clean sxSat (nothing replays a faithful winner), and
      # `assertCoveredBy` then splats the witness into the host, where
      # `quit(0)` after the target ends the process: "SURVIVED" never prints.
      # KNOWN DEFECT (INT-22, unchanged from 0.8.0). The native run of this SUT
      # ends its process too, so it is only ever run in the child.
      let c = runChild("quit")
      checkpoint "hung=" & $c.hung & " rc=" & $c.rc & " out=" & c.output
      check not c.hung
      check "VERDICT sxSat []" in c.output
      check "ASSERTING" in c.output
      check "SURVIVED" notin c.output
      skipCell(cellKey(axConstruct, "quit/afterTarget/assertCoveredBy"),
               "K2-0 INT-22 reproduces: clean sxSat, then assertCoveredBy's splat of the witness ends the host process (rc 0, no line after the call)")

    test "PND-13: a 1500-statement chain does not reach Z3's depth, it is slow in the walk":
      # The compile-time parser stops a SUT of 3000 such statements (the VM
      # iteration cap, in parseDeferList), well below any Z3 recursion limit.
      # At 1500 the walk has not finished inside the budget though 40 finish
      # in about a second: a cost curve (superlinear in statements), not a
      # Z3 stack. The timing is not pinned, only that the walk was entered.
      let small = runChild("smallIdx")
      check not small.hung
      check "VERDICT sxSat" in small.output
      let big = runChild("bigEq")
      checkpoint "hung=" & $big.hung & " secs=" & $big.secs & " out=" & big.output
      check big.entered
      skipCell(cellKey(axBuild, "z3/recursionDepth"),
               "K2-0 PND-13: no SUT reaches Z3's own recursion depth: parser stops at ~3000 straight-line statements; 1500 additions then an equality exceed 25 s (cost, not depth); 40 finish in 1 s")

    test "HRV-06: an omitted variant field with no zero value declines; the rest agree":
      pinDecline(omitTable, cellKey(axTypeClass, "variant/omittedField/Table"), feUnsupportedOpHavoc)
      pinDecline(omitSet, cellKey(axTypeClass, "variant/omittedField/HashSet"), feUnsupportedOpHavoc)
      discard pinExact(omitArr, cellKey(axTypeClass, "variant/omittedField/array"), domain = sampled([0, 3]))
      discard pinExact(omitDistinct, cellKey(axTypeClass, "variant/omittedField/distinct"), domain = sampled([0, 3]))
      discard pinExact(omitTuple, cellKey(axTypeClass, "variant/omittedField/tuple"), domain = sampled([0, 3]))
