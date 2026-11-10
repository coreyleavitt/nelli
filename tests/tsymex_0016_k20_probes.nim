## RFC-0016 K2-0 -- the probe batch, part 1 (the fast probes; the hangs and the
## child-process probes are `tsymex_0016_k20_probes_child`). One smallest SUT per
## claim, run through `symexFind` and natively with K9a's verbs. A probe that
## reproduces a defect pins the CURRENT behaviour: the test passes while the
## defect stands and fails the day it is fixed, which is the cue to re-pin the
## row with `pinExact` or `pinDecline`. Rows: SND-13, CRH-06, CRH-09, INT-11,
## INT-12, INT-15, W-19b, W-19c, W-24.
import std/[unittest, os, strutils, sets, tables, macros, sequtils]
when defined(posix):
  import std/posix
import nelli
import nelli/symex
import ./s8cu_helpers
import ./s8cu_fix_k20_nopop

if getEnv("NELLI_PIN_DIR").len == 0:
  putEnv("NELLI_PIN_DIR", getTempDir() / ("k20_pins_" & $getCurrentProcessId()))

proc faulted(r: SymexResult; needle: string): bool =
  ## The walker's verdict is `sxUnknown` and an internal walker fault naming
  ## `needle` was recorded: a crash-class stop, not a named decline.
  if r.status != sxUnknown: return false
  for e in r.errors:
    if e.kind == weInternalWalkerFault and needle in e.msg: return true

# --- CRH-06: zeroMem / copyMem on `addr x` ------------------------------------

proc zm(k: int) =
  var x = k
  zeroMem(addr x, sizeof(x))
  if x == 0: symexTarget("hit")
proc cm(k: int) =
  var x = k
  var y = 0
  copyMem(addr y, addr x, sizeof(int))
  if y == k: symexTarget("hit")

# --- INT-11 / W-19b: the cycle collector and a dynamic-subtype hook -----------

var gA5: int
type
  HT = object
    v: int
  TCell = ref object
    h: HT
    next: TCell
proc `=trace`(a: var HT; env: pointer) = gA5 = gA5 + 1
proc cycle(k: int) =
  var c = TCell(h: HT(v: k))
  c.next = c
proc trace1(k: int) =
  let a = gA5
  cycle(k)
  GC_fullCollect()
  if gA5 != a: symexTarget("hit")

var gD: int
type
  BObj = object of RootObj
  SObj = object of BObj
    v: int
proc `=destroy`(x: SObj) = gD += 1
proc dynSut(v: int) =
  gD = 0
  block:
    var r: ref BObj = (ref SObj)(v: v)
    r = nil
  GC_fullCollect()
  if gD > 0: symexTarget("hit")

# --- W-19b: threads, signals, an opaque proc with a `var T` parameter ----------

var gT: int
var thr: Thread[int]
proc thrBody(v: int) {.thread.} = gT = v
proc thrSut(v: int) =
  gT = 0
  createThread(thr, thrBody, 7)
  joinThread(thr)
  if gT == 7: symexTarget("hit")

when defined(posix):
  var gS: int
  proc sigH(sig: cint) {.noconv.} = gS = 9
  proc sigSut(v: int) =
    gS = 0
    signal(SIGUSR1, sigH)
    discard kill(getpid(), SIGUSR1)
    if gS == 9: symexTarget("hit")

proc cmemset(p: var int; c: cint; n: csize_t): pointer
  {.importc: "memset", header: "<string.h>", discardable.}
proc opqZero(v: int) =
  var x = v
  cmemset(x, 0, 8)
  if x == 0: symexTarget("hit")
proc opqNonzero(v: int) =
  var x = v
  cmemset(x, 0, 8)
  if x != 0: symexTarget("hit")

# --- SND-13: a push AND its pop both built by macros ---------------------------

type K = enum kA, kB
type P = object
  case k: K
  of kA: x: int
  of kB: y: int
macro pushOffS(): untyped = parseStmt("{.push " & "fieldChecks: off.}")
macro popS(): untyped = parseStmt("{.pop.}")
pushOffS()
proc macPair(v: int) =
  var q = P(k: kA, x: v)
  q.y = v
  symexTarget("hit")
popS()

# --- W-19c: S1b block/break binding, S7 expression-position drains -------------

proc s1b(k: int) =
  block a:
    block b:
      if k > 3: break a
      if k > 1: break b
      symexTarget("one")
    symexTarget("two")
  symexTarget("three")
proc s1bTwo(k: int) =
  block a:
    block b:
      if k > 3: break a
      if k > 1: break b
      discard
    symexTarget("hit")
proc s1bb(k: int) =
  var r = 0
  block a:
    for i in 0 .. 2:
      block a2:
        if i == k: break a
        if k > 5: break a2
      r += 1
  if r == 2: symexTarget("hit")
proc inExpr(k: int) =
  if k > 1000 or k < -1000: return
  let y = (if k > 0:
      var t = k
      t += 1
      t
    else:
      var u = 0
      u - k)
  let z = (case k
    of 1:
      var t = 5
      t
    else: 7)
  if y == 6 and z == 7: symexTarget("hit")
proc inExprTry(k: int) =
  var g = 0
  proc bump(): int =
    g += 1
    g
  var y = 0
  try:
    if k > 0: raise newException(ValueError, "x")
    y = bump()
  except ValueError: y = -1
  if y == -1 and g == 0: symexTarget("hit")
proc drainOrder(k: int) =
  var g = 0
  proc f(a, b: int): int = a * 10 + b
  let y = f((g += 1; g), g)
  if y == 11 and k == 3: symexTarget("hit")

# --- CRH-09 -------------------------------------------------------------------

proc helper(x: int): int = x
proc cast32(x: int) =
  if cast[int32](helper(x)) + 1 == 5: symexTarget("hit")
proc notInt(k: int) =
  if (not k) + 1 == 5: symexTarget("hit")
proc ptrLt(k: int) =
  var a, b: int
  let p = addr a
  let q = addr b
  if p < q or q < p: symexTarget("hit")
proc inSet(c: char) =
  if c in {'0'..'9'}: symexTarget("hit")
proc inSetCall(c: char) =
  if {'0'..'9'}.contains(c): symexTarget("hit")
type Col = enum cR, cG, cB
proc arrEnum(k: int) =
  var a: array[Col, int]
  a[cG] = k
  if a[cG] == 5 and a[cR] == 0: symexTarget("hit")

proc chk(x: int): bool =
  var i = 0
  while i < 3:
    inc i
    if i == 1: continue
  x > i
proc n35a(x: int) =
  var i = x
  while chk(i) and i < 10:
    inc i
  symexTarget("hit")
proc n35b(x: int) =
  var i = x
  while i < 10 and chk(i):
    inc i
  if i >= 10: symexTarget("hit")

proc filterSut(s: seq[int]) =
  let r = s.filterIt(it > 0)
  if r.len > 0: symexTarget("hit")

proc small(k: int) =
  if k * 3 == 21: symexTarget("hit")

proc res(fn: auto; tgt = tLabel("hit")): auto = symexFind(fn, tgt, pinSettingsConst)

suite "RFC-0016 K2-0: crashes and faults (CRH-06, INT-11, W-19b)":
  test "CRH-06: zeroMem and copyMem on addr x are a walker fault":
    check "hit" in nativeRun(zm(5)).hits
    check "hit" in nativeRun(cm(5)).hits
    let a = symexFind(zm, tLabel("hit"), pinSettingsConst)
    let b = symexFind(cm, tLabel("hit"), pinSettingsConst)
    checkpoint show(a.errors) & show(b.errors)
    check a.faulted("ptrPointeeTy")
    check b.faulted("ptrPointeeTy")
    skipCell(cellKey(axMagic, "zeroMem/copyMem(addr x)"),
             "K2-0 CRH-06 reproduces: weInternalWalkerFault (FieldDefect, ptrPointeeTy of an itUninterp), sxUnknown; a fault, not a named decline")

  test "INT-11: the =trace hook only the cycle collector runs declines":
    check "hit" in nativeRun(trace1(3)).hits
    let r = symexFind(trace1, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check not r.faulted("coerceIntLit")
    pinDecline(trace1, cellKey(axConstruct, "hook/=trace/cycleCollector"), feUnsupportedExprKind)

  test "W-19b: a dynamic-subtype =destroy hook is the same fault as INT-11":
    check "hit" in nativeRun(dynSut(1)).hits
    let r = symexFind(dynSut, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    check not r.faulted("coerceIntLit")
    pinDecline(dynSut, cellKey(axConstruct, "hook/=destroy/dynamicSubtype"), feUnsupportedExprKind)

  test "W-19b: createThread declines by name at the call, never a verdict":
    check "hit" in nativeRun(thrSut(1)).hits
    let r = symexFind(thrSut, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    # RFC-0016 K4c made `typedthreads.createThread` decline at the CALL by its
    # `never` row (`callDeclines`), before the stdlib body (pthread or Win32)
    # is registered. The probe's invariant is unchanged (no verdict, no
    # fault); its old expectation of the K2-0 `ptrPointeeTy` fault is stale.
    check r.status == sxUnknown
    check not r.trusted
    check r.errors.named(feUnsupportedOp)
    check not r.errors.named(weInternalWalkerFault)
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and "routine `createThread` is not modelled" in e.msg:
        named = true
    check named
    skipCell(cellKey(axConstruct, "threads/createThread"),
             "K2-0 W-19b, re-pinned by K4c: feUnsupportedOp (the call declines by its never row), sxUnknown")

  when defined(posix):
    test "W-19b: a signal handler writing a global declines (not a fault)":
      check "hit" in nativeRun(sigSut(1)).hits
      pinDecline(sigSut, cellKey(axConstruct, "signals/handler"), feOpaqueCallUnmodelled)

  test "W-19b: an opaque proc with a var T parameter havocs it (no stale environment)":
    check "hit" in nativeRun(opqZero(3)).hits
    check "hit" notin nativeRun(opqNonzero(3)).hits
    # The walker must not claim the stale value (x == v, nonzero) as a trusted
    # hit of opqNonzero, nor refute opqZero.
    let nz = symexFind(opqNonzero, tLabel("hit"), pinSettingsConst)
    checkpoint $nz.status & show(nz.errors)
    check not (nz.status == sxSat and nz.errors.len == 0)
    check nz.errors.named(feGlobalHavoc)
    let z = symexFind(opqZero, tLabel("hit"), pinSettingsConst)
    checkpoint $z.status & show(z.errors)
    check z.status != sxUnsat

suite "RFC-0016 K2-0: soundness (SND-13)":
  test "a macro-built push whose pop is macro-built too is a false sxRaised":
    # Natively the fieldChecks are off, so the discriminant write is silent.
    check native(macPair(4)) == "hit"
    let r = symexFind(macPair, tLabel("hit"), pinSettingsConst)
    checkpoint $r.status & " " & r.raisedTypeId & " " & show(r.errors)
    # KNOWN DEFECT (SND-13): neither the push nor the pop is in the source the
    # scan reads, so the routine is read as checked and the walker reports the
    # FieldDefect natively absent. When fixed this becomes pinDecline(feCheckOption).
    check r.status == sxRaised
    check r.raisedTypeId == "FieldDefect"
    var msg = ""
    try:
      discard pinExact(macPair, cellKey(axPragma, "push/macroBuiltPair"))
    except PinFailure as e: msg = e.msg
    check "sxRaised" in msg
    skipCell(cellKey(axPragma, "push/macroBuiltPair"),
             "K2-0 SND-13 reproduces: false sxRaised (FieldDefect) where native reaches the label with fieldChecks off")

  test "a push that is never popped declines (the scan reads it to the end)":
    check native(npField(4)) == "hit"
    pinDecline(npField, cellKey(axPragma, "push/neverPopped"), feCheckOption)

suite "RFC-0016 K2-0: closure probes (W-19c)":
  test "S1b: nested block/break binding agrees with native":
    for k in [0, 1, 2, 3, 4, 9]:
      checkpoint "k=" & $k
      check ("two" in nativeRun(s1b(k)).hits) == (k <= 3)
    discard pinExact(s1bTwo, cellKey(axConstruct, "block/break/nested"),
                     domain = sampled([0, 1, 2, 3, 4, 9]))
    discard pinExact(s1bb, cellKey(axConstruct, "block/break/forLoopLabel"),
                     domain = sampled([0, 1, 2, 3, 9]))

  test "S7: expression-position statement lists and drains agree with native":
    discard pinExact(inExpr, cellKey(axConstruct, "stmtListExpr/ifCase"),
                     domain = sampled([-5, 0, 1, 5, 7]))
    discard pinExact(inExprTry, cellKey(axConstruct, "drain/tryNestedProc"),
                     domain = sampled([-1, 0, 1, 5]))
    discard pinExact(drainOrder, cellKey(axConstruct, "drain/argOrder"),
                     domain = sampled([0, 3, 5]))

suite "RFC-0016 K2-0: CRH-09 items":
  test "W-24: filterIt is a named decline, not a walker fault":
    check "hit" in nativeRun(filterSut(@[1])).hits
    pinDecline(filterSut, cellKey(axStdlibBody, "sequtils.filterIt"), feUnsupportedExprKind,
               excluding = {weInternalWalkerFault})

  test "HRV-45: cast[int32] over a helper's result is a named decline":
    pinDecline(cast32, cellKey(axTypeOp, "cast/int32"), feUnsupportedExprKind)

  test "W-25: bitwise not on an int agrees with native":
    discard pinExact(notInt, cellKey(axTypeOp, "not/int"),
                     domain = sampled([-5, 0, 4, high(int)]))

  test "W-28: < on ptr is a named decline, not a cmpBV fault":
    pinDecline(ptrLt, cellKey(axDefinedness, "order/pointer"), feUnsupportedOp,
               needle = "bLt")

  test "HRV-47 / HRV-49: char-set contains and array[Enum, T] agree with native":
    discard pinExact(inSet, cellKey(axTypeOp, "set/char/in"),
                     domain = sampled(['0', '5', 'a']))
    discard pinExact(inSetCall, cellKey(axTypeOp, "set/char/contains"),
                     domain = sampled(['0', '5', 'a']))
    discard pinExact(arrEnum, cellKey(axTypeClass, "array/enumIndex"),
                     domain = sampled([0, 5, 6]))

  test "HRV-43 (N35): a guard-shaped callee in a while guard no longer crashes":
    check "hit" in nativeRun(n35a(3)).hits
    for fn in [0, 1]:
      let r = if fn == 0: symexFind(n35a, tLabel("hit"), pinSettingsConst)
              else: symexFind(n35b, tLabel("hit"), pinSettingsConst)
      checkpoint $r.status & show(r.errors)
      check r.status in {sxSat, sxUnknown}
      check not r.errors.named(weInternalWalkerFault)
      check r.errors.named(beBudgetExhausted)

  test "HRV-51: thirty sequential symexFind calls in one binary do not run out of Z3 memory":
    for i in 1 .. 30:
      let r = symexFind(small, tLabel("hit"), pinSettingsConst)
      checkpoint "call " & $i & ": " & $r.status & show(r.errors)
      check r.status == sxSat
      check r.errors.len == 0

  test "HRV-46: the PCRE interpreter crashes natively on a long subject":
    # Not a walker verdict: the native engine dies, with no cell to decline it.
    # 100000 bytes crash here (Linux PCRE); 10000 do not, so the 8000-byte
    # figure of the row is a Windows PCRE 8.45 / stack figure.
    let src = "import std/re, strutils\nlet s = repeat(\"ab\", 50000)\n" &
              "echo match(s, re\"(a|b)*c\")\n"
    pinCrash(cellKey(axBuild, "pcre/interpreter/longSubject"), src, [], ceSegv)

suite "RFC-0016 K2-0: probes this build cannot run":
  test "INT-12: setjmp exceptions on Windows (no Windows host)":
    when defined(windows):
      skip()
    else:
      skipCell(cellKey(axBuild, "exceptions/setjmp/windows"),
               "K2-0 INT-12: the crash is Windows-only (the 16 MB fiber under setjmp); " &
               "tsymex_rfc0005_s8cu_nil_setjmp runs the Linux c arm green and carries the Windows pin")
  test "INT-15: setControlCHook is not in hostRuntimeHook (Windows re-exec only)":
    skipCell(cellKey(axBuild, "replay/hostHook/setControlCHook"),
             "K2-0 INT-15: a fork replay (Linux, macOS) copies the hook, so there is no divergence to probe; " &
             "the re-exec replay is Windows-only. Static finding: hostRuntimeHook (replayproc.nim) checks six hooks, not setControlCHook")
  test "W-19b: Windows re-exec unseen macro hooks (no Windows host)":
    skipCell(cellKey(axBuild, "replay/hostHook/macroHooks"),
             "K2-0 W-19b: Windows re-exec replay only; no Windows host")
