## RFC-0005 S8cu. What the suites share: the native check and the decline check.
import std/[sets, strutils, os, osproc, json, locks, times, macros, algorithm,
            options, streams]
import nelli/symex
import nelli/smt/admission
export admission

proc show*(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if taintsRun(e): parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc named*(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k and taintsRun(e): return true

template native*(call: untyped): string =
  ## "hit" if the call reached the label, the Defect's name if it raised, else
  ## "ran". On this build, so a wrong expectation fails with the verdict.
  block:
    var res = ""
    symexCaptureBegin()
    try:
      call
    except Defect as e:
      res = $e.name
    let hits = symexCaptureEnd()
    if res.len == 0: res = if "hit" in hits: "hit" else: "ran"
    res

template declines*(fn: untyped; kind: SymexErrorKind) =
  let r = symexFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxUnknown
  check r.errors.named(kind)

template decides*(fn: untyped; want: SymexStatusKind) =
  let r = symexFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == want

# ---------------------------------------------------------------------------
# RFC-0016 K9a. The native-pin verbs and the pin record they write.
#
# Three verbs (`pinExact`, `pinDecline`, `pinCrash`) and `skipCell`. Each
# writes one JSON line to this run's record file under `$NELLI_PIN_DIR`
# (default `tests/.pins/`); `pinRecords` reads a directory back. A pin that
# fails raises `PinFailure` and writes nothing, so a record is evidence.
# Built on the public API only: nothing in `symex.nim` is exported for it.
# ---------------------------------------------------------------------------

type
  PinFailure* = object of CatchableError
    ## A pin's claim did not hold. A unittest test fails on it uncaught; a test
    ## that expects a failure catches it with `expect PinFailure`.

  PinVerdict* = enum
    pvExact      ## the walker's definite verdict was reproduced natively
    pvDeclined   ## the walker declined, with the named kind
    pvRaised     ## a definite raise verdict reproduced natively
    pvCrashed    ## a probe crashed natively; evidences declined/never only
    pvSkipped    ## `skipCell`: not run on this build, and why

  CrashExpect* = enum
    ceDivTrap    ## SIGFPE on POSIX, 0xC0000094 on Windows
    ceSegv       ## SIGSEGV on POSIX, 0xC0000005 on Windows
    ceDefect     ## a Nim Defect or panic: exit 1 with an unhandled-exception report
    ceAbnormal   ## any non-zero exit

  Domain*[T] = object
    values*: seq[T]
    exhaustive*: bool   ## true when `values` is every input of interest

  NativeRun* = object
    ## What running the SUT natively did: the markers it reached and the
    ## exception type name it raised ("" if it returned).
    hits*: HashSet[string]
    raised*: string

  PinRecord* = object
    runId*, testFile*, entry*: string
    cell*: CellKey
    target*, domain*: string
    exhaustive*: bool
    verdict*: PinVerdict
    walker*: string        ## the walker's status ("" for crash and skip)
    declineKind*: string   ## the SymexErrorKind a decline named ("" otherwise)
    native*: string        ## what the native run showed
    build*: string         ## `buildSegment()` at write time
    flags*: seq[string]    ## pinCrash: the exact flags the probe was built with
    why*: string           ## skipCell: the reason

func exhaustive*[T](v: openArray[T]): Domain[T] =
  Domain[T](values: @v, exhaustive: true)

func sampled*[T](v: openArray[T]): Domain[T] =
  Domain[T](values: @v, exhaustive: false)

const boundaryInts* = sampled([low(int), low(int) + 1, -1, 0, 1, 7,
                               high(int) - 1, high(int)])

func describe*[T](d: Domain[T]): string =
  var vs: seq[string]
  for i, v in d.values:
    if i == 12: vs.add "..."; break
    vs.add $v
  (if d.exhaustive: "exhaustive" else: "sampled") & "[" & $d.values.len & "]{" &
    vs.join(",") & "}"

proc mkPinSettings(): SymexSettings =
  ## Resource limits only (RFC-0016 §10): the step-counted rlimit budgets stay
  ## at their defaults and the wall-clock `queryTimeoutMs` is off, so a loaded
  ## machine cannot turn an exact pin into a decline.
  result = defaultSymexSettings()
  result.budget.queryTimeoutMs = 0

const pinSettingsConst* = mkPinSettings()
  ## The settings every pin runs under (`symexFind` takes `static` settings).

const mmName = (
  when defined(gcArc): "arc" elif defined(gcOrc): "orc"
  elif defined(gcAtomicArc): "atomicArc" elif defined(gcRefc): "refc"
  elif defined(gcMarkAndSweep): "markAndSweep" elif defined(gcBoehm): "boehm"
  elif defined(gcGo): "go" else: "none")

proc buildSegment*(): string =
  ## The build this run is: rendered from `defined()` and `compileOption` arms
  ## in this one proc. W1-c1a replaces the body with the `BuildProfile` const.
  var parts: seq[string]
  parts.add "backend=" & (when defined(cpp): "cpp" else: "c")
  parts.add "os=" & hostOS
  parts.add "cpu=" & hostCPU
  parts.add "cc=" & (when defined(vcc): "vcc" elif defined(clang): "clang"
                     elif defined(gcc): "gcc" else: "other")
  parts.add "mm=" & mmName
  parts.add "exceptions=" & (
    when compileOption("exceptions", "setjmp"): "setjmp"
    elif compileOption("exceptions", "quirky"): "quirky"
    elif compileOption("exceptions", "goto"): "goto"
    else: "cpp")
  parts.add "panics=" & (when defined(nimPanics): "on" else: "off")
  parts.add "overflowChecks=" & (when compileOption("overflowChecks"): "on" else: "off")
  parts.add "rangeChecks=" & (when compileOption("rangeChecks"): "on" else: "off")
  parts.add "boundChecks=" & (when compileOption("boundChecks"): "on" else: "off")
  parts.add "fwrapv=" & (when defined(nelliFwrapv): "on" else: "off")
  parts.add "opt=" & (when defined(danger): "danger" elif defined(release): "release"
                      else: "debug")
  parts.add "threads=" & (when compileOption("threads"): "on" else: "off")
  parts.add "z3=" & z3FullVersion()
  parts.join(";")

# --- the record file -------------------------------------------------------

var
  pinLock: Lock
  pinFile {.guard: pinLock.}: string
  pinRunId {.guard: pinLock.}: string
initLock(pinLock)

proc pinDir*(): string =
  getEnv("NELLI_PIN_DIR", "tests" / ".pins")

func toJson(r: PinRecord): JsonNode =
  %*{"runId": r.runId, "testFile": r.testFile, "entry": r.entry,
     "cell": render(r.cell), "target": r.target, "domain": r.domain,
     "exhaustive": r.exhaustive, "verdict": $r.verdict, "walker": r.walker,
     "declineKind": r.declineKind, "native": r.native, "build": r.build,
     "flags": r.flags, "why": r.why}

proc fromJson(n: JsonNode): PinRecord =
  result.runId = n["runId"].getStr
  result.testFile = n["testFile"].getStr
  result.entry = n["entry"].getStr
  let c = parseCellKey(n["cell"].getStr)
  doAssert c.isSome, "pin record has an unparsable cell: " & n["cell"].getStr
  result.cell = c.get
  result.target = n["target"].getStr
  result.domain = n["domain"].getStr
  result.exhaustive = n["exhaustive"].getBool
  result.verdict = parseEnum[PinVerdict](n["verdict"].getStr)
  result.walker = n["walker"].getStr
  result.declineKind = n["declineKind"].getStr
  result.native = n["native"].getStr
  result.build = n["build"].getStr
  for f in n["flags"]: result.flags.add f.getStr
  result.why = n["why"].getStr

proc writePinRecord*(r: PinRecord): string {.discardable.} =
  ## Appends `r` to this run's file (one file per run id, so two runs never
  ## clobber). Under a lock, so it is correct from any thread. Returns the path.
  var rec = r
  rec.build = buildSegment()
  {.cast(gcsafe).}:
    withLock pinLock:
      if pinFile.len == 0:
        let dir = pinDir()
        createDir(dir)
        let base = splitFile(getAppFilename()).name
        pinRunId = base & "-" & $getCurrentProcessId() & "-" &
                   $(getTime().toUnix * 1_000_000_000 + getTime().nanosecond)
        pinFile = dir / (pinRunId & ".jsonl")
      rec.runId = pinRunId
      let f = open(pinFile, fmAppend)
      try: f.writeLine($toJson(rec))
      finally: f.close()
      result = pinFile

iterator pinRecords*(dir: string): PinRecord =
  ## Every record under `dir`, file by file in name order, line by line.
  var files: seq[string]
  if dirExists(dir):
    for k, p in walkDir(dir):
      if k == pcFile and p.endsWith(".jsonl"): files.add p
  files.sort()
  for p in files:
    for line in lines(p):
      if line.len > 0: yield fromJson(parseJson(line))

# --- native evaluation -----------------------------------------------------

template nativeRun*(call: untyped): NativeRun =
  ## Runs `call` on this build with marker capture; records what it reached and
  ## the type name of an exception it raised.
  block:
    var nr: NativeRun
    symexCaptureBegin()
    try:
      call
    except Defect as e:
      nr.raised = $e.name
    except CatchableError as e:
      nr.raised = $e.name
    nr.hits = symexCaptureEnd()
    nr

func nameMatches(raised, typeId: string): bool =
  raised.len > 0 and (typeId.len == 0 or typeId == raised or
                      typeId.endsWith("." & raised) or typeId.endsWith(raised))

proc hitsTarget*(nr: NativeRun; t: SymexTarget): bool =
  case t.kind
  of stkLabel: t.label in nr.hits
  of stkRaisedExn: nameMatches(nr.raised, t.typeFilter)
  of stkAssertionViolation: nr.raised == "AssertionDefect"
  of stkIndexError: nr.raised == "IndexDefect"
  of stkFieldDefect: nr.raised == "FieldDefect"
  of stkNilAccess: nr.raised == "NilAccessDefect"

func describeNative(nr: NativeRun): string =
  var h: seq[string]
  for x in nr.hits: h.add x
  h.sort()
  "hits=[" & h.join(",") & "] raised=" & (if nr.raised.len == 0: "-" else: nr.raised)

proc kindsOf(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if taintsRun(e): parts.add $e.kind
  parts.join(",")

proc pinFail(msg: string) {.noreturn.} =
  raise newException(PinFailure, msg)

# --- pinExact --------------------------------------------------------------

proc pinJudge*[T, D](res: SymexResult[T]; key: CellKey; tgt: SymexTarget;
                     dom: Domain[D]; file: string;
                     runW: proc (w: T): NativeRun;
                     runD: proc (vals: seq[D];
                                 hit: proc (n: NativeRun): bool): string
                    ): SymexResult[T] =
  ## The differential judgement `pinExact` expands to.
  let cell = render(key)
  let isHit = proc (n: NativeRun): bool = hitsTarget(n, tgt)
  var rec = PinRecord(testFile: file, entry: "symexFind", cell: key,
                      target: describeTarget(tgt), domain: describe(dom),
                      exhaustive: dom.exhaustive, walker: $res.status)
  case res.status
  of sxSat:
    if not res.trusted:
      pinFail("pinExact " & cell & ": sxSat is not trusted; errors: " &
              kindsOf(res.errors))
    if res.soundness.witnessUnsafe:
      pinFail("pinExact " & cell & ": the witness ends or hangs the process " &
              "that runs it; it cannot be reproduced in-process")
    let nr = runW(res.witness)
    if not isHit(nr):
      pinFail("pinExact " & cell & ": walker says sxSat for " & rec.target &
              " but the witness does not hit natively: " & describeNative(nr))
    rec.verdict = pvExact
    rec.native = "witness hit: " & describeNative(nr)
  of sxRaised:
    if not res.trusted:
      pinFail("pinExact " & cell & ": sxRaised is not trusted; errors: " &
              kindsOf(res.errors))
    let nr = runW(res.raisedWitness)
    if not nameMatches(nr.raised, res.raisedTypeId):
      pinFail("pinExact " & cell & ": walker says sxRaised(" & res.raisedTypeId &
              ") but the witness natively did: " & describeNative(nr))
    rec.verdict = pvRaised
    rec.native = "witness raised: " & describeNative(nr)
  of sxUnsat:
    if not res.trusted:
      pinFail("pinExact " & cell & ": sxUnsat is not trusted; errors: " &
              kindsOf(res.errors))
    if dom.values.len == 0:
      pinFail("pinExact " & cell & ": an empty domain refutes nothing")
    let hitAt = runD(dom.values, isHit)
    if hitAt.len > 0:
      pinFail("pinExact " & cell & ": walker says sxUnsat for " & rec.target &
              " but " & hitAt & " hits it natively")
    rec.verdict = pvExact
    rec.native = "no domain value hit (" & $dom.values.len & ")"
  of sxUnknown:
    pinFail("pinExact " & cell & ": sxUnknown; errors: " & kindsOf(res.errors))
  writePinRecord(rec)
  res

proc paramCount(fn: NimNode): int =
  let ty = fn.getTypeInst
  doAssert ty.kind in {nnkProcTy, nnkLambda} or ty.len > 0,
    "pinExact: cannot read the parameter list of " & fn.repr
  let fp = ty[0]
  for i in 1 ..< fp.len: result += fp[i].len - 2

macro pinExactImpl*(fn: typed; claim, key, target, domain, file: untyped): untyped =
  let n = paramCount(fn)
  let res = genSym(nskLet, "res")
  let tgt = genSym(nskLet, "tgt")
  let dom = genSym(nskLet, "dom")
  # runW: the SUT applied to a witness tuple.
  let w = genSym(nskParam, "w")
  let wcall = newCall(fn)
  for i in 0 ..< n: wcall.add nnkBracketExpr.newTree(w, newLit(i))
  # runD: the SUT applied to every combination of domain values over its
  # parameters, reporting the first input that hits.
  let hit = genSym(nskParam, "hit")
  let vals = genSym(nskParam, "vals")
  let found = genSym(nskVar, "found")
  var loopVars: seq[NimNode]
  for i in 0 ..< n: loopVars.add genSym(nskForVar, "v" & $i)
  let dcall = newCall(fn)
  for v in loopVars: dcall.add v
  var shown = newLit("input (")
  for i, v in loopVars:
    shown = infix(shown, "&", newCall(ident"$", v))
    if i < loopVars.high: shown = infix(shown, "&", newLit(","))
  shown = infix(shown, "&", newLit(")"))
  var loops = quote do:
    if `found`.len == 0 and `hit`(nativeRun(`dcall`)): `found` = `shown`
  for i in countdown(n - 1, 0):
    loops = nnkForStmt.newTree(loopVars[i], vals, newStmtList(loops))
  quote do:
    block:
      let `tgt` = `target`
      let `dom` = `domain`
      let `res` = `claim`
      pinJudge(`res`, `key`, `tgt`, `dom`, `file`,
        proc (`w`: typeof(`res`.witness)): NativeRun = nativeRun(`wcall`),
        proc (`vals`: seq[typeof(`dom`.values[0])];
              `hit`: proc (n: NativeRun): bool): string =
          var `found` = ""
          `loops`
          `found`)

template pinExact*(fn: untyped; key: CellKey;
                   target: untyped = tLabel("hit");
                   domain: untyped = boundaryInts): untyped =
  ## Differential exact pin; returns the `SymexResult`. `sxSat`: the witness
  ## hits natively. `sxUnsat`: no domain value hits (every combination across
  ## the parameters; each parameter takes the domain's element type).
  ## `sxUnknown` or untrusted: fails with `PinFailure`. A raise is a target:
  ## `target = tRaisedExn("ValueError")`.
  pinExactImpl(fn, symexFind(fn, target, pinSettingsConst), key, target, domain,
               instantiationInfo(-1).filename)

template pinExactOn*(fn: untyped; claim: untyped; key: CellKey;
                     target: untyped = tLabel("hit");
                     domain: untyped = boundaryInts): untyped =
  ## `pinExact`'s judgement over a verdict the caller supplies instead of the
  ## walker's: the way a test plants a wrong claim and sees the pin refuse it.
  pinExactImpl(fn, claim, key, target, domain, instantiationInfo(-1).filename)

# --- pinDecline ------------------------------------------------------------

proc pinDeclineJudge*[T](res: SymexResult[T]; key: CellKey; tgt: SymexTarget;
                         kind: SymexErrorKind; file: string) =
  let cell = render(key)
  if res.trusted:
    pinFail("pinDecline " & cell & ": the verdict " & $res.status &
            " is trusted; it should decline with " & $kind)
  if not res.errors.named(kind):
    pinFail("pinDecline " & cell & ": not trusted, but no " & $kind &
            " was recorded; errors: " & kindsOf(res.errors))
  writePinRecord(PinRecord(testFile: file, entry: "symexFind", cell: key,
    target: describeTarget(tgt), domain: "-", verdict: pvDeclined,
    walker: $res.status, declineKind: $kind,
    native: "not run: the cell declines"))

template pinDecline*(fn: untyped; key: CellKey; kind: SymexErrorKind;
                     target: untyped = tLabel("hit")) =
  ## The cell declines: the verdict is not trusted and `kind` was recorded.
  block:
    let pdRes = symexFind(fn, target, pinSettingsConst)
    pinDeclineJudge(pdRes, key, target, kind, instantiationInfo(-1).filename)

# --- pinCrash and skipCell -------------------------------------------------

proc crashClass(rc: int; output: string; expect: CrashExpect): bool =
  when defined(windows):
    let code = cast[uint32](int32(rc))
    case expect
    of ceDivTrap: code == 0xC0000094'u32
    of ceSegv: code == 0xC0000005'u32
    of ceDefect: rc != 0 and "Defect]" in output
    of ceAbnormal: rc != 0
  else:
    case expect
    of ceDivTrap: rc == 128 + 8      # SIGFPE
    of ceSegv: rc == 128 + 11        # SIGSEGV
    of ceDefect: rc != 0 and "Defect]" in output
    of ceAbnormal: rc != 0

proc appTestFile(): string = splitFile(getAppFilename()).name & ".nim"

var probeCounter {.threadvar.}: int

proc pinCrash*(key: CellKey; probe: string; flags: openArray[string];
               expect: CrashExpect) =
  ## Compiles `probe` in a child with the host's build-relevant defines plus
  ## `flags`, runs it, and asserts the exit class. `probe` is a path to a Nim
  ## file, or the source text itself when it contains a newline. A child that
  ## exits 0 fails. The record is `pvCrashed`: it bypasses every public entry
  ## point, so K1 may use it for a `declined` or `never` cell only.
  let nim = findExe("nim")
  if nim.len == 0: pinFail("pinCrash: nim is not on PATH")
  inc probeCounter
  let dir = getTempDir() / ("k9a_probe_" & $getCurrentProcessId() & "_" &
                            $probeCounter)
  createDir(dir)
  var src = probe
  if '\n' in probe:
    src = dir / "probe_src.nim"
    writeFile(src, probe)
  else:
    src = absolutePath(probe)
  let exe = dir / ("probe" & ExeExt)
  var args = @["--hints:off", "--warnings:off", "--threads:on",
               "--nimcache:" & (dir / "cache"), "--out:" & exe,
               "--panics:" & (when defined(nimPanics): "on" else: "off"),
               "--mm:" & mmName]
  when defined(nelliFwrapv): args.add "-d:nelliFwrapv"
  when defined(release): args.add "-d:release"
  when defined(danger): args.add "-d:danger"
  when defined(vcc): args.add "--cc:vcc"
  elif defined(windows): args.add "--cc:gcc"   # the toolchain ships Nim alone
  for f in flags: args.add f
  let backend = when defined(cpp): "cpp" else: "c"
  let (cout, crc) = execCmdEx(quoteShellCommand(@[nim, backend] & args & @[src]))
  if crc != 0: pinFail("pinCrash " & render(key) & ": probe build failed:\n" & cout)
  let p = startProcess(exe, options = {poStdErrToStdOut})
  let rc = p.waitForExit(20_000)
  let output = p.outputStream.readAll()
  let timedOut = p.running
  if timedOut: p.kill()
  p.close()
  removeDir(dir)
  if timedOut: pinFail("pinCrash " & render(key) & ": the probe did not finish")
  if rc == 0:
    pinFail("pinCrash " & render(key) & ": the probe exited 0; expected " &
            $expect & "\n" & output)
  if not crashClass(rc, output, expect):
    pinFail("pinCrash " & render(key) & ": exit " & $rc &
            " is not the expected " & $expect & "\n" & output)
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "pinCrash", cell: key, target: "-", domain: "-",
    verdict: pvCrashed, native: "rc=" & $rc & " expected=" & $expect,
    flags: @args & @[backend]))

proc skipCell*(key: CellKey; why: string) =
  ## Not run on this build, and why. K2a's census fails a bare `skip(`.
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "skipCell", cell: key, target: "-", domain: "-",
    verdict: pvSkipped, why: why))
