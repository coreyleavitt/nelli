## RFC-0005 S8cu. What the suites share: the native check and the decline check.
import std/compilesettings
import std/[sets, tables, strutils, os, osproc, json, locks, times, macros, algorithm,
            options, streams, tempfiles, typetraits, sequtils]
import nelli/symex
from nelli/engine/markers import symexAssumeGateOpen, symexAssumeGateClose
import nelli/db
import nelli/choice
import nelli/int128
import nelli/engine/types
import nelli/smt/admission
import nelli/smt/soundness
from nelli/smt/errorkind import UbKind
from nelli/smt/types import undefinedKinds, `$`
import nelli/smt/buildprofile
import ./probe_build
import ./k9d_regex
export admission, probe_build, k9d_regex

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

template nativeHits*(call: untyped): HashSet[string] =
  ## The labels `call` reaches on this build, under a capture frame. The one
  ## shared copy of what thirty-five suites each defined (RFC-0016 K9b).
  block:
    symexCaptureBegin()
    call
    symexCaptureEnd()

proc nativeHits*(fn: proc (k: int) {.nimcall.};
                 ks: openArray[int]): HashSet[string] =
  ## The labels `fn` reaches over every `k` in `ks`, on this build.
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

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
  PinVerdict* = enum
    pvExact      ## the walker's definite verdict was reproduced natively
    pvDeclined   ## the walker declined, with the named kind
    pvRaised     ## a definite raise verdict reproduced natively
    pvCrashed    ## a probe crashed natively; evidences declined/never only
    pvSkipped    ## `skipCell`: not run on this build, and why

  CrashExpect* = enum
    ceDivTrap    ## SIGFPE on POSIX; on Windows 0xC0000094/5 or Nim's SIGFPE report, exit 1
    ceSegv       ## SIGSEGV on POSIX; on Windows 0xC0000005, 0xC00000FD (stack overflow) or Nim's SIGSEGV report, exit 1
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
    rejected*: bool
      ## a false `symexAssume` ended the run: the input is outside the
      ## walker's domain, so the run hit and raised nothing

  PinRecord* = object
    runId*, testFile*, entry*: string
    cell*: CellKey
    target*, domain*: string
    exhaustive*: bool
    verdict*: PinVerdict
    walker*: string        ## the walker's status ("" for crash and skip)
    declineKind*: string   ## the SymexErrorKind a decline named ("" otherwise)
    native*: string        ## what the native run showed
    build*: string         ## `pinBuildSegment()` at write time
    row*: string           ## `rowOf`'s BuildRow at write time ("" when none)
    date*: string          ## UTC write time, `pinDateFmt` ("" in older records)
    cap*: string           ## pinCap: the CapKind member the run halted on
    flags*: seq[string]    ## pinCrash: the exact flags the probe was built with
    why*: string           ## skipCell: the reason

# ---- closed primitives for the generic domain code (K9d-7) ------------------
# An overloaded call in a generic routine (`add`, `len`, `items`, `contains`)
# is an open symbol: Nim looks it up again where the routine is instantiated,
# so a suite that declares its own `add(var seq[int], int)` or
# `len(seq[int16])` (RFC-0005 S8c does, on purpose) silently replaces the
# stdlib's inside the generated domain (S8c's int domains came out empty).
# The domain code calls these instead: each is the only routine of its name
# here (a closed symbol, bound where it is defined) and reaches the stdlib by
# a qualified name. `domPut` also avoids `system.add`, whose instance for
# `seq[seq[uint32]]` is shared with `seq[seq[cuint]]` (nim-z3 declares one)
# and then does not compile in C: a Nim defect, the two element types being
# one Nim type but two C types (reproducer in the K9d plan, K9d-7b).

proc domPut*[T](s: var seq[T]; v: sink T) {.inline.} =
  let n = system.len(s)
  system.setLen(s, n + 1)
  s[n] = v

proc domLen*[T](s: seq[T]): int {.inline.} = system.len(s)

proc domHas*[T](s: seq[T]; v: T): bool =
  ## membership; a float compares by its bits (NaN is a member of a domain
  ## that holds it, and -0.0 is not 0.0)
  for i in 0 ..< system.len(s):
    when T is SomeFloat:
      when sizeof(T) == 4:
        if cast[uint32](s[i]) == cast[uint32](v): return true
      else:
        if cast[uint64](s[i]) == cast[uint64](v): return true
    else:
      if s[i] == v: return true

func exhaustive*[T](v: openArray[T]): Domain[T] =
  Domain[T](values: @v, exhaustive: true)

func sampled*[T](v: openArray[T]): Domain[T] =
  Domain[T](values: @v, exhaustive: false)

const boundaryInts* = sampled([low(int), low(int) + 1, -1, 0, 1, 7,
                               high(int) - 1, high(int)])

proc heapIdOf*(p: pointer): int
  ## forward (K9d-10): a pool cell's number, -1 otherwise

proc heapTypeIn(t: NimNode; seen: var seq[string]): bool

proc heapFieldsIn(n: NimNode; seen: var seq[string]): bool =
  case n.kind
  of nnkIdentDefs:
    heapTypeIn(n[^2], seen)
  of nnkRecCase:
    var found = heapTypeIn(n[0][^2], seen)
    for i in 1 ..< n.len:
      if heapFieldsIn(n[i][^1], seen): found = true
    found
  else:
    var found = false
    for c in n:
      if heapFieldsIn(c, seen): found = true
    found

proc heapTypeIn(t: NimNode; seen: var seq[string]): bool =
  ## the type (as a typed node) holds a ref, a ptr or a pointer
  if t.kind == nnkEmpty: return false
  let k = t.repr
  if k in seen: return false
  seen.add k
  if t.kind == nnkSym and t.strVal == "pointer": return true
  let impl = t.getTypeImpl
  case impl.kind
  of nnkRefTy, nnkPtrTy: true
  of nnkSym: impl.strVal == "pointer"
  of nnkObjectTy:
    var found = heapFieldsIn(impl[2], seen)
    if impl[1].kind == nnkOfInherit and heapTypeIn(impl[1][0], seen):
      found = true
    found
  of nnkTupleTy, nnkTupleConstr:
    var found = false
    for c in impl:
      let ft = if c.kind == nnkIdentDefs: c[^2] else: c
      if heapTypeIn(ft, seen): found = true
    found
  of nnkBracketExpr:
    var found = false
    for i in 1 ..< impl.len:
      if impl[i].kind in {nnkSym, nnkBracketExpr} and heapTypeIn(impl[i], seen):
        found = true
    found
  else: false

macro holdsHeap*(T: typedesc): bool =
  ## the type holds a ref, a ptr or a pointer somewhere in its fields
  var seen: seq[string]
  newLit(heapTypeIn(T.getType[1], seen))

func showArg*[T](v: T): string =
  ## `$` of a generated input; a distinct type shows as its base type
  ## (a string shows quoted and escaped: a record is text, and a generated
  ## string holds NUL and bytes above 0x7F)
  when T is distinct: showArg(distinctBase(T)(v))
  elif T is string: escape(v)
  elif T is cstring: escape($v)
  elif T is seq or T is array:
    var parts: seq[string]
    for i in low(v) .. high(v): domPut(parts, showArg(v[i]))
    (when T is seq: "@" else: "") & "[" & parts.join(", ") & "]"
  elif T is Table:
    var parts: seq[string]
    for k, x in tables.pairs(v): domPut(parts, showArg(k) & ": " & showArg(x))
    "{" & parts.join(", ") & "}"
  elif T is HashSet:
    var parts: seq[string]
    for e in sets.items(v): domPut(parts, showArg(e))
    "{" & parts.join(", ") & "}"
  elif T is ref or T is ptr or T is pointer:
    # a pool cell by its number (K9d-10), a witness's own cell as "#w"; a
    # non-object pointee's value is shown, an object's is not (a cycle)
    if v == nil: "nil"
    else:
      var id = -1
      {.cast(noSideEffect).}:
        id = heapIdOf(cast[pointer](v))
      let tag = if id >= 0: "#" & $id else: "#w"
      when T is pointer: tag
      elif typeof(v[]) is object: tag
      else: tag & ":" & showArg(v[])
  elif (T is object or T is tuple) and holdsHeap(T):
    # `$` of an object reaches its ref fields, which have no `$`
    var parts: seq[string]
    for n, f in fieldPairs(v): domPut(parts, n & ": " & showArg(f))
    "(" & parts.join(", ") & ")"
  else: $v

func describe*[T](d: Domain[T]): string =
  var vs: seq[string]
  for i in 0 ..< domLen(d.values):
    if i == 12: domPut(vs, "..."); break
    domPut(vs, showArg(d.values[i]))
  (if d.exhaustive: "exhaustive" else: "sampled") & "[" & $domLen(d.values) & "]{" &
    vs.join(",") & "}"

proc mkPinSettings(): SymexSettings =
  ## Resource limits only (RFC-0016 §10): the step-counted rlimit budgets stay
  ## at their defaults and the wall-clock `queryTimeoutMs` is off, so a loaded
  ## machine cannot turn an exact pin into a decline. Off is not unbounded: a
  ## run's step-bounded solves still share the 600 s stall
  ## backstop deadline (`stallBackstopMs`, RFC-0016 INT-57), so a stalled
  ## query declines named and the walk ends.
  result = defaultSymexSettings()
  result.budget.queryTimeoutMs = 0

const pinSettingsConst* = mkPinSettings()
  ## The settings every pin runs under (`symexFind` takes `static` settings).

proc pinBuildSegment*(): string =
  ## The build this run is: `buildprofile.buildSegment` (the one renderer) of
  ## this build and the host this run linked (the Z3 version in it).
  buildprofile.buildSegment(buildprofile.buildSemantics,
                            buildprofile.readHost(z3FullVersion()))

proc pinBuildRow*(): string =
  ## The `BuildRow` this build is (RFC-0016 section 8.2: records carry
  ## `rowOf`'s row), "" when no row covers it. Unlike the segment this sees the
  ## C compiler family (`buildProvenance`), so it tells mingw from msvc. It is
  ## computed here and never keyed: `buildSegment` and the cache key are
  ## untouched.
  let r = buildprofile.rowOf(buildprofile.buildSemantics,
                             buildprofile.readHost(z3FullVersion()),
                             buildprofile.buildProvenance)
  if r.isSome: $r.get else: ""

# --- the record file -------------------------------------------------------

var
  pinLock: Lock
  pinFile {.guard: pinLock.}: string
  pinRunId {.guard: pinLock.}: string
initLock(pinLock)

proc pinDir*(): string =
  getEnv("NELLI_PIN_DIR", "tests" / ".pins")

const pinDateFmt* = "yyyy-MM-dd'T'HH:mm:ss'Z'"

proc pinNow*(): Time =
  ## The clock every pin date and freshness check reads. `$NELLI_PIN_NOW`
  ## (unix seconds) replaces the wall clock, so a test can fix "now".
  let o = getEnv("NELLI_PIN_NOW", "")
  if o.len > 0: fromUnix(parseBiggestInt(o)) else: getTime()

proc pinDate*(t: Time): string = t.utc.format(pinDateFmt)

func toJson(r: PinRecord): JsonNode =
  %*{"runId": r.runId, "testFile": r.testFile, "entry": r.entry,
     "cell": render(r.cell), "target": r.target, "domain": r.domain,
     "exhaustive": r.exhaustive, "verdict": $r.verdict, "walker": r.walker,
     "declineKind": r.declineKind, "native": r.native, "build": r.build,
     "row": r.row, "date": r.date, "cap": r.cap, "flags": r.flags, "why": r.why}

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
  result.row = n{"row"}.getStr       # absent in records written before K1a
  result.date = n{"date"}.getStr     # absent in records written before K1a-last
  result.cap = n{"cap"}.getStr
  for f in n["flags"]: result.flags.add f.getStr
  result.why = n["why"].getStr

proc writePinRecord*(r: PinRecord): string {.discardable.} =
  ## Appends `r` to this run's file (one file per run id, so two runs never
  ## clobber). Under a lock, so it is correct from any thread. Returns the path.
  var rec = r
  rec.build = pinBuildSegment()
  rec.row = pinBuildRow()
  rec.date = pinDate(pinNow())
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

proc appendPinRecordTo*(dir: string; r: PinRecord) =
  ## Appends an already-complete record (its run id, build and row kept) to
  ## `dir/<testFile stem>-reemitted.jsonl`. For a test that runs its probes
  ## against a private pin directory and ships the verdicts that evidence a
  ## cell to the leg's directory.
  createDir(dir)
  let f = open(dir / (splitFile(r.testFile).name & "-reemitted-" &
                      $getCurrentProcessId() & ".jsonl"), fmAppend)
  try: f.writeLine($toJson(r))
  finally: f.close()

proc recordFiles(dir: string): seq[string] =
  if dirExists(dir):
    for k, p in walkDir(dir):
      if k == pcFile and p.endsWith(".jsonl"): result.add p
  result.sort()

const exercisedKind* = "exercised"
  ## The `kind` field of RFC-0016 K8b's cells-exercised record, the second
  ## record kind of a run's file. A pin record has no `kind` field.

iterator pinRecords*(dir: string): PinRecord =
  ## Every pin record under `dir`, file by file in name order, line by line.
  ## A cells-exercised record (`exercisedRecords`) is skipped.
  for p in recordFiles(dir):
    for line in lines(p):
      if line.len > 0:
        let n = parseJson(line)
        if n{"kind"}.getStr != exercisedKind: yield fromJson(n)

# --- RFC-0016 K8b: the cells-exercised record --------------------------------
#
# One generated program under one variant, run through `symexFind` and the
# native differential: the family it belongs to, the family cells it
# exercises, and how the run ended (`exact`, `declined`, `disagree`). The
# pairwise figure (§8.2, §12 item 4) is computed from these; K1 reads them
# from the same record files as the pins (`tests/s0016_k8b_pairs.nim`).

type
  ExercisedRecord* = object
    runId*, testFile*, variant*, outcome*: string
    family*: Scope
    seed*, progId*: int
    cells*: seq[CellKey]
    build*, row*, date*: string

func toJson(r: ExercisedRecord): JsonNode =
  var cs = newJArray()
  for c in r.cells: cs.add %render(c)
  %*{"kind": exercisedKind, "runId": r.runId, "testFile": r.testFile,
     "family": scopePrefix[r.family], "seed": r.seed, "progId": r.progId,
     "variant": r.variant, "outcome": r.outcome, "cells": cs,
     "build": r.build, "row": r.row, "date": r.date}

proc exercisedFromJson*(n: JsonNode): ExercisedRecord =
  ## A malformed record (an unknown family or an unparsable cell) raises
  ## `ValueError` naming it: a typo fails instead of naming nothing.
  let fam = n["family"].getStr
  var found = false
  for sc in Scope:
    if scopePrefix[sc] == fam:
      result.family = sc
      found = true
  if not found:
    raise newException(ValueError, "exercised record: unknown family " & fam)
  for c in n["cells"]:
    let k = parseCellKey(c.getStr)
    if k.isNone:
      raise newException(ValueError,
        "exercised record: unparsable cell " & c.getStr)
    result.cells.add k.get
  result.runId = n["runId"].getStr
  result.testFile = n["testFile"].getStr
  result.seed = n["seed"].getInt
  result.progId = n["progId"].getInt
  result.variant = n["variant"].getStr
  result.outcome = n["outcome"].getStr
  result.build = n["build"].getStr
  result.row = n["row"].getStr
  result.date = n["date"].getStr

proc exercisedLine*(r: ExercisedRecord): string = $toJson(r)

proc writeExercisedTo*(dir: string; rs: seq[ExercisedRecord]) =
  ## Appends `rs` to `dir/<testFile stem>-exercised-<pid>.jsonl`, each stamped
  ## with this build's segment, row and date.
  if rs.len == 0: return
  createDir(dir)
  let f = open(dir / (splitFile(rs[0].testFile).name & "-exercised-" &
                      $getCurrentProcessId() & ".jsonl"), fmAppend)
  try:
    for r0 in rs:
      var r = r0
      r.build = pinBuildSegment()
      r.row = pinBuildRow()
      r.date = pinDate(pinNow())
      r.runId = splitFile(getAppFilename()).name & "-" & $getCurrentProcessId()
      f.writeLine(exercisedLine(r))
  finally: f.close()

iterator exercisedRecords*(dir: string): ExercisedRecord =
  ## Every cells-exercised record under `dir` (pin records are skipped).
  for p in recordFiles(dir):
    for line in lines(p):
      if line.len > 0:
        let n = parseJson(line)
        if n{"kind"}.getStr == exercisedKind: yield exercisedFromJson(n)

# --- native evaluation -----------------------------------------------------

proc restoreHeapDomain*()
  ## forward (K9d-10, with the ref domains): every ref/ptr pool cell back to
  ## its snapshot

template nativeRun*(call: untyped): NativeRun =
  ## Runs `call` on this build with marker capture; records what it reached and
  ## the type name of an exception it raised.
  block:
    var nr: NativeRun
    let gate = symexAssumeGateOpen()
    restoreHeapDomain()
    symexCaptureBegin()
    try:
      call
    except Defect as e:
      nr.raised = $e.name
    except CatchableError as e:
      nr.raised = $e.name
    nr.hits = symexCaptureEnd()
    restoreHeapDomain()
    nr.rejected = symexAssumeGateClose(gate)
    if nr.rejected:
      # outside the walker's domain: nothing the run reached counts
      nr.hits.clear()
      nr.raised = ""
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
  of stkUndefined: false   # a witness that reaches undefined behaviour is not run

func describeNative(nr: NativeRun): string =
  if nr.rejected: return "rejected by symexAssume (outside the assumed domain)"
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

# --- entry-point adapters --------------------------------------------------
#
# A pin goes through a public entry point (RFC-0016 section 10) chosen with
# `pinExact(..., via = ...)`. An adapter runs the entry point and returns a
# `Claimed`: the verdict as a `SymexResult` plus the entry's name. The name is
# written only here, beside the call it names, so a record's `entry` cannot
# say an entry point the verdict did not come through.

type
  Claimed*[T] = object
    res*: SymexResult[T]
    entry*: string

proc claimed*[T](res: SymexResult[T]; entry: string): Claimed[T] =
  Claimed[T](res: res, entry: entry)

proc statusResult[T](st: SymexStatusKind; w: T; s: Soundness): SymexResult[T] =
  case st
  of sxSat: SymexResult[T](status: sxSat, witness: w, soundness: s)
  of sxUnsat: SymexResult[T](status: sxUnsat, soundness: s)
  else: SymexResult[T](status: sxUnknown, soundness: s)

proc decodeWitness*[T: tuple](nodes: seq[ChoiceNode]): T =
  ## A witness's choice sequence as the parameter tuple: one integer or
  ## boolean node per field, in order.
  var i = 0
  for f in fields(result):
    if i >= nodes.len:
      raise newException(PinFailure, "pin: a witness of " & $nodes.len &
        " choices does not cover " & $T)
    let n = nodes[i]
    inc i
    when f is bool:
      if n.kind != ckBoolean:
        raise newException(PinFailure, "pin: choice " & $(i - 1) & " is not a bool")
      f = n.boolVal
    elif f is SomeInteger:
      if n.kind != ckInteger:
        raise newException(PinFailure, "pin: choice " & $(i - 1) & " is not an integer")
      f = typeof(f)(n.intVal.toInt64)
    else:
      {.error: "pin: finding witnesses decode integer and bool parameters only".}

proc fromFinding*[T](f: SymexFinding; entry: string): Claimed[T] =
  ## A `SymexFinding` (`symexFindAllWitnesses`, `symexForAll`,
  ## `assertCoveredBy`) as a typed verdict. The witness is decoded from its
  ## choices; a raise finding is not an exact claim here.
  let st = case f.status
    of sfSat: sxSat
    of sfUnsat: sxUnsat
    else: sxUnknown
  let w = if st == sxSat: decodeWitness[T](f.witnessChoices) else: default(T)
  Claimed[T](res: statusResult(st, w, f.soundness), entry: entry)

proc findingFor*(fs: openArray[SymexFinding]; t: SymexTarget): SymexFinding =
  for f in fs:
    if f.targetDesc == describeTarget(t): return f
  raise newException(PinFailure, "pin: no finding for " & describeTarget(t) &
    " among " & $fs.len)

proc fromVerdict*[T](v: Option[CachedVerdict]; entry: string): Claimed[T] =
  ## A `loadSymexVerdict` hit: its stored status and soundness, no witness.
  if v.isNone:
    raise newException(PinFailure, "pin: the cache holds no verdict")
  let st = if v.get.status == sfUnsat: sxUnsat else: sxUnknown
  Claimed[T](res: statusResult(st, default(T), v.get.soundness), entry: entry)

proc fromFlip*[T](r: ConcolicFlipResult; entry: string): Claimed[T] =
  ## A `concolicFlip` outcome. The result's own `soundness` is the claim's
  ## (RFC-0016 W3-z R4): the collect pass's declines and the undefined
  ## operations the flip reached are in it, so an `sxUnsat` over either is not
  ## trusted. A solved flip is a witness, a proven-infeasible one an `sxUnsat`,
  ## anything else (an optimistic relaxation included) is `sxUnknown`.
  let s = r.soundness
  case r.outcome
  of cfoSolvedExact:
    Claimed[T](res: statusResult(sxSat, decodeWitness[T](r.materialized), s),
               entry: entry)
  of cfoUnsat:
    Claimed[T](res: statusResult(sxUnsat, default(T), s), entry: entry)
  else:
    Claimed[T](res: statusResult(sxUnknown, default(T), s), entry: entry)

template witnessTypeOf*(fn: untyped): untyped =
  typeof(symexFind(fn, tLabel("hit"), pinSettingsConst).witness)

template viaFind*(fn, target: untyped): untyped =
  claimed(symexFind(fn, target, pinSettingsConst), "symexFind")

template viaFindAll*(fn, target: untyped): untyped =
  fromFinding[witnessTypeOf(fn)](
    findingFor(symexFindAllWitnesses(fn, inMemoryDatabase(), pinSettingsConst),
               target), "symexFindAllWitnesses")

template viaForAll*(fn, target, strategy: untyped): untyped =
  ## `strategy` yields `fn`'s parameter (a tuple for several).
  fromFinding[witnessTypeOf(fn)](
    findingFor(symexForAll(strategy, fn, inMemoryDatabase(),
                           pinSettingsConst).symexFindings, target),
    "symexForAll")

template viaCovered*(fn, target: untyped): untyped =
  block:
    var cov: SymexFinding
    try:
      cov = assertCoveredBy(fn, target, fn, pinSettingsConst)
    except SymexCoverageDefect as e:
      raise newException(PinFailure, "pin: assertCoveredBy refused its own " &
        "witness: " & e.msg)
    fromFinding[witnessTypeOf(fn)](cov, "assertCoveredBy")

template viaCache*(fn, target: untyped): untyped =
  ## A cold `symexFindAllWitnesses` fills the database; the claim is what
  ## `loadSymexVerdict` then serves (a non-SAT verdict).
  block:
    let cacheDb = inMemoryDatabase()
    discard symexFindAllWitnesses(fn, cacheDb, pinSettingsConst)
    fromVerdict[witnessTypeOf(fn)](
      loadSymexVerdict(cacheDb, fn, target, pinSettingsConst),
      "loadSymexVerdict")

template viaConcolic*(fn, target, trace, bindings, branch: untyped): untyped =
  ## Flip the recorded decision `branch` of `trace` and read the new draws.
  ## `target` is what the flipped run is native-checked against.
  fromFlip[witnessTypeOf(fn)](
    concolicFlip(fn, trace, bindings, branch, pinSettingsConst), "concolic")

macro viaClaim(via, fn, target: untyped): untyped =
  ## `via` is an adapter name, or a call of one with its extra arguments;
  ## `fn` and `target` are put in front of those.
  if via.kind in {nnkIdent, nnkSym}:
    result = newCall(via, fn, target)
  else:
    result = copyNimTree(via)
    result.insert(1, fn)
    result.insert(2, target)

# --- pinExact --------------------------------------------------------------

proc pinJudge*[T, D](res: SymexResult[T]; key: CellKey; tgt: SymexTarget;
                     dom: Domain[D]; file: string;
                     runW: proc (w: T): NativeRun;
                     runD: proc (vals: seq[D];
                                 hit: proc (n: NativeRun): bool): string;
                     entry = "symexFind";
                     undefined: set[UbKind] = {};
                     domDesc = ""): SymexResult[T] =
  ## The differential judgement `pinExact` expands to. `undefined` (RFC-0016
  ## INT-69): the undefined behaviours the program's modelled answer carries.
  ## A `sxSat` that is untrusted ONLY because its witness reads one of them
  ## (`witnessUndefined` non-empty, within `undefined`, and the soundness
  ## otherwise trusted) is the model's answer, as `pinUndefined` judges it;
  ## it is reproduced when its witness hits natively, and recorded as
  ## `pinUndefined` records (`pvDeclined` by the kind), with the native hit.
  ## `domDesc`, when given, is the record's domain text in place of
  ## `describe(dom)` (`pinFind`'s per-parameter domains are judged as a
  ## domain of combination indices).
  let cell = render(key)
  let isHit = proc (n: NativeRun): bool = hitsTarget(n, tgt)
  var rec = PinRecord(testFile: file, entry: entry, cell: key,
                      target: describeTarget(tgt),
                      domain: (if domDesc.len > 0: domDesc else: describe(dom)),
                      exhaustive: dom.exhaustive, walker: $res.status)
  case res.status
  of sxSat:
    let ub = res.soundness.undefinedKinds
    var defined = res.soundness
    defined.witnessUndefined = {}
    let asModelled = not res.trusted and undefined != {} and ub != {} and
                     ub <= undefined and trustedSat(defined)
    if not res.trusted and not asModelled:
      pinFail("pinExact " & cell & ": sxSat is not trusted; errors: " &
              kindsOf(res.errors) & (if ub != {}: "; undefined: " & $ub else: ""))
    if res.soundness.witnessUnsafe:
      pinFail("pinExact " & cell & ": the witness ends or hangs the process " &
              "that runs it; it cannot be reproduced in-process")
    let nr = runW(res.witness)
    if not isHit(nr):
      pinFail("pinExact " & cell & ": walker says sxSat for " & rec.target &
              " but the witness does not hit natively: " & describeNative(nr))
    if asModelled:
      for k in ub:
        rec.verdict = pvDeclined
        rec.declineKind = $k
        rec.native = "witness hit: " & describeNative(nr) &
          "; the verdict carries the undefined behaviour it models"
        writePinRecord(rec)
      return res
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
    if domLen(dom.values) == 0:
      pinFail("pinExact " & cell & ": an empty domain refutes nothing")
    let hitAt = runD(dom.values, isHit)
    if hitAt.len > 0:
      pinFail("pinExact " & cell & ": walker says sxUnsat for " & rec.target &
              " but " & hitAt & " hits it natively")
    rec.verdict = pvExact
    rec.native = "no domain value hit (" & $domLen(dom.values) & ")"
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

macro pinExactImpl*(fn: typed; claim, key, target, domain, file,
                    undefined: untyped): untyped =
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
    shown = infix(shown, "&", newCall(bindSym("showArg", brOpen), v))
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
      pinJudge(`res`.res, `key`, `tgt`, `dom`, `file`,
        proc (`w`: typeof(`res`.res.witness)): NativeRun = nativeRun(`wcall`),
        proc (`vals`: seq[typeof(`dom`.values[0])];
              `hit`: proc (n: NativeRun): bool): string =
          var `found` = ""
          `loops`
          `found`,
        `res`.entry, `undefined`)

template pinExact*(fn: untyped; key: CellKey;
                   target: untyped = tLabel("hit");
                   domain: untyped = boundaryInts;
                   via: untyped = viaFind): untyped =
  ## Differential exact pin; returns the `SymexResult`. `via` names the public
  ## entry point the verdict comes through (an adapter above, with its extra
  ## arguments, e.g. `via = viaForAll(integers(0, 10))`); the record's `entry`
  ## is that entry point. `sxSat`: the witness
  ## hits natively. `sxUnsat`: no domain value hits (every combination across
  ## the parameters; each parameter takes the domain's element type).
  ## `sxUnknown` or untrusted: fails with `PinFailure`. A raise is a target:
  ## `target = tRaisedExn("ValueError")`.
  pinExactImpl(fn, viaClaim(via, fn, target), key, target, domain,
               instantiationInfo(-1).filename, {})

template pinExactOn*(fn: untyped; claim: untyped; key: CellKey;
                     target: untyped = tLabel("hit");
                     domain: untyped = boundaryInts): untyped =
  ## `pinExact`'s judgement over a verdict the caller supplies instead of the
  ## walker's: the way a test plants a wrong claim and sees the pin refuse it.
  ## Its record's entry is "caller", not a public entry point: K1 refuses it.
  pinExactImpl(fn, claimed(claim, "caller"), key, target, domain,
               instantiationInfo(-1).filename, {})

# --- pinFind (K9d) ---------------------------------------------------------
#
# The generator for suites with no native idiom (W-54): `pinFind` is the
# suite's own `symexFind` call, same arguments, same result, judged natively
# by `pinJudge`. The `sxUnsat` domain is generated from each parameter's type.

const pinFindCap* = 65_536
  ## The most input combinations an `sxUnsat` pin runs natively; a larger
  ## product is run up to the cap and recorded as sampled.

macro declaredValues(T: typedesc): untyped =
  ## the enum's declared values as an array literal (a holey enum's holes are
  ## not in its type, so `low .. high` would invent invalid values)
  result = newNimNode(nnkBracket).add(T.getType[1].getTypeImpl[1..^1])

const fieldProductFull* = 4096
  ## A tuple or object whose field domains multiply to at most this many
  ## values is generated as the full product; a larger one as an all-pairs
  ## covering array (`pairwiseRows`).

proc productRows(sizes: seq[int]): seq[seq[int]] =
  ## every index combination, the last position varying fastest
  var row = newSeq[int](sizes.len)
  for s in sizes:
    if s == 0: return @[]
  while true:
    result.add row
    var i = sizes.len - 1
    while i >= 0:
      inc row[i]
      if row[i] < sizes[i]: break
      row[i] = 0
      dec i
    if i < 0: break

proc pairwiseRows*(sizes: seq[int]): seq[seq[int]] =
  ## A deterministic all-pairs covering array over fields with `sizes[i]`
  ## values each: for every two fields i < j and every value a of i and b of
  ## j, some row has a at i and b at j. Greedy: each row starts from the first
  ## uncovered pair and fills the other fields with the value covering the
  ## most uncovered pairs (ties to the lowest index).
  let k = sizes.len
  if k == 0: return @[newSeq[int](0)]
  for s in sizes:
    if s == 0: return @[]
  if k == 1:
    for v in 0 ..< sizes[0]: result.add @[v]
    return
  var unc = newSeq[seq[bool]](k * k)
  var left = 0
  for i in 0 ..< k:
    for j in i + 1 ..< k:
      unc[i * k + j] = newSeq[bool](sizes[i] * sizes[j])
      for x in 0 ..< unc[i * k + j].len: unc[i * k + j][x] = true
      left += unc[i * k + j].len
  while left > 0:
    var row = newSeq[int](k)
    for f in 0 ..< k: row[f] = -1
    block seed:
      for i in 0 ..< k:
        for j in i + 1 ..< k:
          for x in 0 ..< unc[i * k + j].len:
            if unc[i * k + j][x]:
              row[i] = x div sizes[j]
              row[j] = x mod sizes[j]
              break seed
    for f in 0 ..< k:
      if row[f] >= 0: continue
      var best = 0
      var bestGain = -1
      for v in 0 ..< sizes[f]:
        var gain = 0
        for g in 0 ..< k:
          if g == f or row[g] < 0: continue
          let ix = if g < f: unc[g * k + f][row[g] * sizes[f] + v]
                   else: unc[f * k + g][v * sizes[g] + row[g]]
          if ix: inc gain
        if gain > bestGain:
          bestGain = gain
          best = v
      row[f] = best
    for i in 0 ..< k:
      for j in i + 1 ..< k:
        let x = row[i] * sizes[j] + row[j]
        if unc[i * k + j][x]:
          unc[i * k + j][x] = false
          dec left
    result.add row

proc exceeds*(sizes: seq[int]; limit: int): bool =
  ## whether the product of `sizes` is above `limit` (without overflowing)
  var prod = 1
  for s in sizes:
    if s > 0:
      if prod > limit div s: return true
      prod *= s
  prod > limit

proc fieldRows*(sizes: seq[int]; limit = fieldProductFull):
    tuple[rows: seq[seq[int]], full: bool] =
  ## the index rows over fields of these domain sizes: the full product when it
  ## is at most `limit`, else the all-pairs covering array
  if exceeds(sizes, limit): (pairwiseRows(sizes), false)
  else: (productRows(sizes), true)

# --- the string domain (K9d-6) ---------------------------------------------
#
# `boundaryOf(string)` is a deterministic finite set, never the whole type:
# the fixed core (empty, every byte of a byte alphabet that holds the control,
# ASCII, high and UTF-8 lead/continuation bytes, all pairs over a smaller one,
# all triples over a smaller one, whole multi-byte sequences) plus what the
# SUT's own source says: its string and char literals, and each literal's
# neighbours (prefixes, suffixes, one byte appended, removed or changed, case
# variants), and strings at its integer literals' lengths +/- 1. A pinFind
# call harvests those literals at macro time and sets them as the hints for
# the domains it generates; no hints is the fixed core alone.

type
  StringHints* = object
    strs*: seq[string]   ## string and char literals of the SUT, in source order
    ints*: seq[int]      ## its small integer literals (length thresholds)
    nums*: seq[float64]  ## its float literals and integer literals, as floats
    pats*: seq[string]   ## its regex literals (`re"..."`, `rex"..."`), which
                         ## are patterns, not data (K9d-9, k9d_regex.nim)

const
  stringDomainCap* = 2048
    ## the most values `boundaryOf(string)` holds, whatever the hints
  stringCore* = 64
    ## a string field thinned to cross with other fields keeps this prefix of
    ## its domain: the empty string, the single bytes, then the literals
  strMaxLiterals = 32
  strNeighbourMaxLen = 64
  strBytes = ['\0', 'a', 'z', '0', '9', ' ', '-', '\x7F', '\x80', '\xFF',
              'A', 'Z', '_', '.', '/', '\n', '\xC3', '\xA9', '\xE2', '\x82',
              '\xAC', '\xF0', '\x9F', '\x98', '\xBF']
  strPairBytes = ['\0', 'a', '0', ' ', '-', '\x7F', '\x80', '\xFF', '\xC3',
                  '\xA9']
  strTripleBytes = ['\0', 'a', '0', '\x80', '\xFF']
  strAppendBytes = ['\0', 'a', '0', ' ', '\xFF']
  strUtf8 = ["\xC3\xA9", "\xE2\x82\xAC", "\xF0\x9F\x98\x80", "\xC0\x80",
             "\xE2\x82", "\xF0\x9F\x98", "\xED\xA0\x80", "\xF4\x90\x80\x80"]
  strFixedLens = [5, 8, 16, 33, 64, 100]

var stringHintsCur {.threadvar.}: StringHints

proc newHeapEpoch()
  ## forward (K9d-10): the ref pools are rebuilt over the new hints

proc setStringHints*(h: StringHints) =
  stringHintsCur = h
  newHeapEpoch()

proc clearStringHints*() =
  stringHintsCur = StringHints()

proc stringDomainValues*(h: StringHints): seq[string] =
  ## The string domain for these hints (see above), at most `stringDomainCap`
  ## values, in priority order, deterministic.
  var seen = initHashSet[string]()
  template put(s: string) =
    if result.len < stringDomainCap and not seen.containsOrIncl(s):
      result.add s
  var lits: seq[string]
  for s in h.strs:
    if lits.len < strMaxLiterals and s notin lits: lits.add s
  put ""
  for c in strBytes: put $c
  for l in lits:
    for i in 0 ..< min(l.len, strNeighbourMaxLen): put $l[i]
  for l in lits: put l
  # the regex part (K9d-9): members, boundaries, structural near-misses and
  # case variants first, the one-edit neighbours after the thresholds
  let rx = regexStages(h.pats)
  var rxLeft = regexDomainCap
  template putRx(v: string) =
    if rxLeft > 0 and result.len < stringDomainCap and not seen.containsOrIncl(v):
      result.add v
      dec rxLeft
  for st in 0 .. 3:
    for v in rx[st]: putRx v
  for u in strUtf8: put u
  var ks: seq[int]
  for k in h.ints:
    if k in 1 .. 256 and k notin ks and ks.len < 16: ks.add k
  for k in ks:
    for n in [k - 1, k, k + 1]: put 'a'.repeat(n)
  for n in strFixedLens: put 'a'.repeat(n)
  for v in rx[4]: putRx v
  let near = lits.filterIt(it.len in 1 .. strNeighbourMaxLen)
  for l in near:                       # prefixes, suffixes
    for i in 1 ..< l.len:
      put l[0 ..< i]
      put l[i .. ^1]
  for l in near:                       # one byte appended or prepended
    for b in strAppendBytes:
      put l & $b
      put $b & l
  for l in near:                       # one byte removed
    for i in 0 ..< l.len: put l[0 ..< i] & l[i + 1 .. ^1]
  for l in near:                       # one byte changed
    for i in 0 ..< l.len:
      for b in [char((ord(l[i]) + 1) and 255), char((ord(l[i]) + 255) and 255), 'a', '\0']:
        var m = l
        m[i] = b
        put m
  for l in near:                       # case, padding
    put l.toUpperAscii
    put l.toLowerAscii
    put " " & l
    put l & " "
  for a in strPairBytes:
    for b in strPairBytes: put $a & $b
  for a in strTripleBytes:
    for b in strTripleBytes:
      for c in strTripleBytes: put $a & $b & $c

var cstringArena {.threadvar.}: seq[string]
  ## the storage behind generated `cstring` values; kept for the process so a
  ## domain's values never dangle

proc cstringDomain(h: StringHints): Domain[cstring] =
  ## nil, then the string domain's values without a NUL (a NUL ends a
  ## cstring, so a value holding one is its prefix, already in the set).
  ## RFC-0016 INT-87: nil is a value of the type (`len` 0, `$` "", equal
  ## only to nil), which a caller passes as readily as any string.
  var vs: seq[cstring] = @[cstring(nil)]
  for s in stringDomainValues(h):
    if '\0' notin s:
      cstringArena.add s
      vs.add cstring(cstringArena[^1])
  Domain[cstring](values: vs, exhaustive: false)

const
  seqDomainCap* = 2048
    ## the most values a collection domain holds, whatever the hints
  collCoreMax* = 8
    ## the element core: up to this many spread values of the element domain
  collExtraMax = 6
    ## and up to this many more an ordinal gets from the SUT's own literals
  seqFixedLens = [4, 5, 8]
  seqTripleFull = 512
    ## length-3 sequences are the full product of the core up to this many,
    ## else an all-pairs array

proc pairsExceed*(sizes: seq[int]; limit: int): bool =
  ## whether the two largest of `sizes` multiply to more than `limit`
  var a, b = 0
  for s in sizes:
    if s > a: b = a; a = s
    elif s > b: b = s
  a > 0 and b > 0 and a > limit div b

# --- the float domain (K9d-8) ----------------------------------------------
#
# `boundaryOf(float64)` and `boundaryOf(float32)` (and `cfloat`, `cdouble`, a
# float `range`, a distinct float through its base) are a deterministic finite
# set in the parameter's own width, never the whole type, at most
# `seqDomainCap` values, in priority order, each value once by its bits (so
# -0.0 and 0.0 are two values and NaN is one):
#
# - the specials: +-0, +-1, NaN (quiet), +-Inf, 0.5, +-the smallest
#   subnormal, +-the smallest normal, +-the largest finite, the two
#   neighbours of 1;
# - the SUT's own float and integer literals (`StringHints.nums`, at most
#   `floatMaxLiterals`, in source order), each in the parameter's width with
#   its neighbour either way (a float32 neighbour is one float32 step, not a
#   float64 step rounded back), then each negated with its neighbours;
# - the tail: +-the largest subnormal, the step above the smallest normal,
#   -0.5, the neighbours of -1, +-2, the rounding ties 1.5 and 2.5, 0.1, 3,
#   10, 100, 1e10, 1e-10, the step below the largest finite, and 2^e - 1,
#   2^e and both its neighbours, negated too, at the integer-exactness and
#   integer-width edges (e in 7, 8, 15, 16, 24, 31, 32, 53, 63, 64); a
#   float64 domain also holds float32's largest finite and the step above it,
#   float32's smallest subnormal and half of it (a narrowing conversion's
#   overflow and underflow edges).
#
# A float `range` keeps the values inside it and NaN, which Nim's range check
# (`x < lo or x > hi`) passes (RFC-0016 int6). A float
# thinned to cross with other fields keeps its first `stringCore` values:
# the specials and the leading literals with their neighbours.

const
  floatMaxLiterals* = 32
    ## the SUT's float and integer literals a float domain takes
  floatCoreLiterals = 16
    ## the leading literals placed before the negations and the fixed tail

proc floatsOfBits*(bs: openArray[uint64]): seq[float64] =
  ## the harvested literals, carried as their bits (`hintsExpr`)
  for b in bs: domPut(result, cast[float64](b))

proc fStep[F: float32 | float64](x: F; up: bool): F =
  when F is float32:
    type U = uint32
  else:
    type U = uint64
  if x != x: return x
  if x == F(0.0):
    let m = cast[F](U(1))
    return (if up: m else: -m)
  if (up and x == F(Inf)) or (not up and x == F(-Inf)): return x
  let b = cast[U](x)
  if (x > F(0.0)) == up: cast[F](b + 1) else: cast[F](b - 1)

proc fNextUp*[F: float32 | float64](x: F): F =
  ## the next float of `x`'s width above it (IEEE-754 nextUp; NaN stays)
  fStep(x, true)

proc fNextDown*[F: float32 | float64](x: F): F =
  ## the next float of `x`'s width below it
  fStep(x, false)

proc floatKey[F: float32 | float64](x: F): uint64 {.inline.} =
  when F is float32: uint64(cast[uint32](x)) else: cast[uint64](x)

proc floatDomainValues*[F: float32 | float64](nums: seq[float64]): seq[F] =
  ## The float domain of one width for these literals (see above).
  var seen = initHashSet[uint64]()
  template put(v: F) =
    block:
      let x = v
      if system.len(result) < seqDomainCap and
         not seen.containsOrIncl(floatKey(x)):
        domPut(result, x)
  template nb(v: F) =
    block:
      let y = v
      put y
      put fNextUp(y)
      put fNextDown(y)
  when F is float32:
    let negZero = cast[float32](0x8000_0000'u32)
    let minNormal = cast[float32](0x0080_0000'u32)
  else:
    let negZero = cast[float64](0x8000_0000_0000_0000'u64)
    let minNormal = cast[float64](0x0010_0000_0000_0000'u64)
  let one = F(1.0)
  let minSub = fNextUp(F(0.0))
  let maxSub = fNextDown(minNormal)
  let maxFin = fNextDown(F(Inf))
  for x in [F(0.0), negZero, one, -one, F(NaN), F(Inf), F(-Inf), F(0.5),
            minSub, -minSub, minNormal, -minNormal, maxFin, -maxFin,
            fNextUp(one), fNextDown(one)]:
    put x
  var lits: seq[F]
  for f in nums:
    if domLen(lits) >= floatMaxLiterals: break
    if f == f and f - f == 0.0: domPut(lits, F(f))
  let lead = min(domLen(lits), floatCoreLiterals)
  for i in 0 ..< lead: nb lits[i]
  for i in 0 ..< lead: nb -lits[i]
  for x in [maxSub, -maxSub, fNextUp(minNormal), F(-0.5), fNextUp(-one),
            fNextDown(-one), F(2.0), F(-2.0), F(1.5), F(-1.5), F(2.5),
            F(-2.5), F(0.1), F(-0.1), F(3.0), F(10.0), F(100.0), F(1e10),
            F(-1e10), F(1e-10), fNextDown(maxFin), -fNextDown(maxFin)]:
    put x
  for e in [7, 8, 15, 16, 24, 31, 32, 53, 63, 64]:
    let t = if e == 64: 18446744073709551616.0 else: float64(1'u64 shl e)
    for s in [1.0, -1.0]:
      put F(s * (t - 1.0))
      nb F(s * t)
      put F(s * (t + 1.0))
  when F is float64:
    let f32max = float64(fNextDown(float32(Inf)))
    let f32sub = float64(fNextUp(float32(0.0)))
    for x in [f32max, fNextUp(f32max), -f32max, -fNextUp(f32max), f32sub,
              f32sub / 2.0, -f32sub]:
      put x
  for i in lead ..< domLen(lits):
    nb lits[i]
    nb -lits[i]

proc harvestInto(n: NimNode; dir: string; h: var StringHints;
                 seen: var HashSet[string]) =
  const skipCalls = ["symexTarget", "newException", "echo", "symexLabel"]
  case n.kind
  of nnkStrLit, nnkRStrLit, nnkTripleStrLit:
    if n.strVal notin h.strs: h.strs.add n.strVal
  of nnkCharLit:
    let s = $char(n.intVal)
    if s notin h.strs: h.strs.add s
  of nnkIntLit .. nnkInt64Lit, nnkUIntLit .. nnkUInt64Lit:
    if n.intVal in 1 .. 256 and int(n.intVal) notin h.ints:
      h.ints.add int(n.intVal)
    let f = if n.kind in nnkUIntLit .. nnkUInt64Lit: float64(cast[uint64](n.intVal))
            else: float64(n.intVal)
    if f notin h.nums and h.nums.len < floatMaxLiterals: h.nums.add f
  of nnkFloatLit .. nnkFloat128Lit:
    let f = n.floatVal
    if f == f and f - f == 0.0 and h.nums.len < floatMaxLiterals and
       not h.nums.anyIt(cast[uint64](it) == cast[uint64](f)):
      h.nums.add f
  of nnkSym:
    if n.symKind in {nskProc, nskFunc, nskMethod, nskIterator, nskConverter,
                     nskConst}:
      let li = n.lineInfoObj
      let key = n.strVal & "@" & li.filename & ":" & $li.line
      if li.filename.parentDir == dir and not seen.containsOrIncl(key):
        harvestInto(n.getImpl, dir, h, seen)
  of nnkCall, nnkCommand, nnkCallStrLit:
    if n[0].kind == nnkSym and n[0].strVal in skipCalls: return
    if n[0].kind == nnkSym and n[0].strVal in ["re", "rex"] and n.len >= 2:
      var a = n[1]
      while a.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and a.len > 0:
        a = a[^1]
      if a.kind in {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
        if a.strVal notin h.pats: h.pats.add a.strVal
        for c in n[2 .. ^1]: harvestInto(c, dir, h, seen)
        return
    for c in n: harvestInto(c, dir, h, seen)
  else:
    for c in n: harvestInto(c, dir, h, seen)

proc harvest(fn: NimNode): StringHints =
  ## the string and char literals and small integer literals of the SUT's
  ## body and of the routines and consts it names that live beside it
  var seen = initHashSet[string]()
  let li = fn.lineInfoObj
  harvestInto(fn, li.filename.parentDir, result, seen)

proc hintsExpr(h: StringHints): NimNode =
  var ss = newNimNode(nnkBracket)
  for s in h.strs: ss.add newLit(s)
  var ii = newNimNode(nnkBracket)
  for i in h.ints: ii.add newLit(i)
  # a float literal as its bits: a decimal rendering of -0.0 or of a value
  # at the edge of the type would not be the same float read back
  var nn = newNimNode(nnkBracket)
  for f in h.nums: nn.add newLit(cast[uint64](f))
  let nums = newCall(bindSym"floatsOfBits", nn)
  var pp = newNimNode(nnkBracket)
  for p in h.pats: pp.add newLit(p)
  nnkObjConstr.newTree(bindSym"StringHints",
    nnkExprColonExpr.newTree(ident"strs", nnkPrefix.newTree(ident"@", ss)),
    nnkExprColonExpr.newTree(ident"ints", nnkPrefix.newTree(ident"@", ii)),
    nnkExprColonExpr.newTree(ident"nums", nums),
    nnkExprColonExpr.newTree(ident"pats", nnkPrefix.newTree(ident"@", pp)))

macro harvestLiterals*(fn: typed): untyped =
  ## the SUT's string, char and small integer literals as `StringHints`
  hintsExpr(harvest(fn))

template prefixDomain*(T: typedesc): bool =
  ## a type whose generated domain is in priority order (its prefix is its core)
  T is string or T is cstring or T is seq or T is array or T is set or
    T is Table or T is HashSet or T is SomeFloat or T is ref or T is ptr or
    T is pointer

proc thinDomain*[T](d: var Domain[T]) =
  ## A field of an aggregate too large to cross in full keeps its extremes and
  ## its middle (an ordinal's low end, zero and high end): at most nine values.
  let n = domLen(d.values)
  if n <= 16: return
  when prefixDomain(T):
    # the domain is in priority order: its prefix is the core
    system.setLen(d.values, min(n, stringCore))
    d.exhaustive = false
    return
  var keep: seq[int]
  for i in [0, 1, 2, n div 2 - 1, n div 2, n div 2 + 1, n - 3, n - 2, n - 1]:
    if not domHas(keep, i): domPut(keep, i)
  var vs: seq[T]
  for j in 0 ..< domLen(keep): domPut(vs, d.values[keep[j]])
  d.values = vs
  d.exhaustive = false

proc thinForPairs*[T](d: var Domain[T]) =
  ## a string or collection domain too large to cross with another such
  ## parameter is cut to its core; other types are left whole
  when prefixDomain(T): thinDomain(d)

proc selector(f: NimNode; o: NimNode): NimNode =
  if f.kind == nnkIntLit: nnkBracketExpr.newTree(o, f) else: newDotExpr(o, f)

proc boundaryOf*[T](t: typedesc[T]): Domain[T]
  ## forward: the generated domain code binds it here (open, so a suite's
  ## own overload still applies) and does not name it in the suite's scope

proc freeBlock*[T](p: ptr T) =
  ## a zeroed block an aggregate's value was built in (`domLeaf`), released
  `=destroy`(p[])
  dealloc(p)

template declarable*(T: typedesc): bool =
  ## `var x: T` compiles (a field such as `range[1..100]` has no default;
  ## `compiles(default(T))` does not see it)
  compiles((block:
    var x {.used.}: T))

proc protoOf*[T](t: typedesc[T]): ptr T = nil
  ## read only under `typeof` (`objectDomain`'s field types), never run

type DomCtx = object
  ty, vals, exh, proto: NimNode
  depth: int
  refTy: NimNode   ## non-nil: each value is built as a cell of this ref type

proc domLeaf(cx: DomCtx; fields: seq[NimNode];
             discs: seq[(NimNode, NimNode)]): NimNode =
  let body = newStmtList()
  var ds: seq[NimNode]
  var sizes = nnkBracket.newTree()
  let exh = cx.exh
  let vals = cx.vals
  let ty = cx.ty
  for i, f in fields:
    let d = genSym(nskVar, "fd" & $i)
    ds.add d
    body.add newVarStmt(d, newCall(bindSym("boundaryOf", brOpen),
      newCall(ident"typeof", selector(f, cx.proto))))
  let thin = newStmtList()
  for d in ds:
    sizes.add newCall(bindSym"domLen", newDotExpr(d, ident"values"))
    thin.add newCall(bindSym("thinDomain", brOpen), d)
  body.add quote do:
    if exceeds(@`sizes`, fieldProductFull): `thin`
  for d in ds:
    body.add quote do:
      if not `d`.exhaustive: `exh` = false
  let fr = genSym(nskLet, "fr")
  let row = genSym(nskForVar, "row")
  let o = genSym(if cx.refTy != nil: nskVar else: nskLet, "o")
  let od = nnkDerefExpr.newTree(o)
  let ov = genSym(nskVar, "ov")
  let decl = bindSym"declarable"
  body.add quote do:
    let `fr` = fieldRows(@`sizes`)
    if not `fr`.full: `exh` = false
  let setup = newStmtList()
  let refTy = cx.refTy
  if refTy != nil:
    # INT-81: a hierarchy object is built in its cell, never copied by
    # value (`objectRefDomain`)
    setup.add quote do:
      var `o`: `refTy`
      new(`o`)
  else:
    setup.add quote do:
      # a type with no default (a field such as `range[1..100]`) is built
      # in a zeroed block, every field assigned below; any other in a
      # declared value (an inheritable object's block would lack its type
      # header)
      when `decl`(`ty`):
        var `ov`: `ty`
        let `o` = addr `ov`
      else:
        let `o` = cast[ptr `ty`](alloc0(sizeof(`ty`)))
  for (dn, dv) in discs:
    let asg = newAssignment(selector(dn, od), dv)
    setup.add nnkPragmaBlock.newTree(
      nnkPragma.newTree(nnkCast.newTree(newEmptyNode(), ident"uncheckedAssign")),
      newStmtList(asg))
  for i, f in fields:
    setup.add newAssignment(selector(f, od),
      nnkBracketExpr.newTree(newDotExpr(ds[i], ident"values"),
                             nnkBracketExpr.newTree(row, newLit(i))))
  let put = bindSym"domPut"
  let free = bindSym"freeBlock"
  if refTy != nil:
    setup.add quote do:
      `put`(`vals`, `o`)
  else:
    setup.add quote do:
      `put`(`vals`, `o`[])
      when not `decl`(`ty`): `free`(`o`)
  body.add nnkForStmt.newTree(row, newDotExpr(fr, ident"rows"), setup)
  result = newStmtList(nnkBlockStmt.newTree(newEmptyNode(), body))

proc freshCond(c: NimNode): NimNode =
  ## a branch condition as an untyped literal (the typed one is of the
  ## discriminator's type; the generated case is over its ordinal)
  case c.kind
  of nnkIntLit .. nnkInt64Lit: newIntLitNode(c.intVal)
  of nnkRange, nnkInfix:
    let r = newNimNode(nnkRange)
    for i in (if c.kind == nnkInfix: 1 else: 0) ..< c.len:
      r.add freshCond(c[i])
    r
  else:
    error("pinFind: unsupported variant branch condition " & $c.kind, c)
    c

proc domEmit(cx: var DomCtx; items: seq[NimNode]; fields: seq[NimNode];
             discs: seq[(NimNode, NimNode)]): NimNode =
  var items = items
  var fields = fields
  while items.len > 0:
    let it = items[0]
    items.delete(0)
    case it.kind
    of nnkIdentDefs:
      for i in 0 ..< it.len - 2: fields.add it[i]
    of nnkRecList:
      var pre: seq[NimNode]
      for c in it: pre.add c
      items = pre & items
    of nnkRecCase:
      inc cx.depth
      let exh = cx.exh
      let dname = it[0][0]
      let dd = genSym(nskLet, "dd" & $cx.depth)
      let dv = genSym(nskForVar, "dv" & $cx.depth)
      let cs = nnkCaseStmt.newTree(newCall(ident"ord", dv))
      for bi in 1 ..< it.len:
        let br = it[bi]
        var bodyItems: seq[NimNode]
        let b = br[^1]
        if b.kind == nnkRecList:
          for c in b: bodyItems.add c
        else: bodyItems.add b
        let inner = domEmit(cx, bodyItems & items, fields,
                            discs & (dname, dv))
        let nb = br.kind.newTree()
        for ci in 0 ..< br.len - 1: nb.add freshCond(br[ci])
        nb.add inner
        cs.add nb
      if it[^1].kind != nnkElse:
        # the generated case is over the discriminator's ordinal
        cs.add nnkElse.newTree(newStmtList(nnkDiscardStmt.newTree(newEmptyNode())))
      result = newStmtList()
      result.add newLetStmt(dd, newCall(bindSym("boundaryOf", brOpen),
        newCall(ident"typeof", selector(dname, cx.proto))))
      result.add quote do:
        if not `dd`.exhaustive: `exh` = false
      result.add nnkForStmt.newTree(dv, newDotExpr(dd, ident"values"),
                                    newStmtList(cs))
      return
    of nnkNilLit, nnkEmpty: discard
    else:
      error("pinFind: cannot generate a domain for record item " &
            $it.kind, it)
  domLeaf(cx, fields, discs)

proc domItemsOf(t: NimNode): seq[NimNode] =
  var impl = t.getTypeImpl
  # an ancestor named by its ref type (`ref object of Base`, Base a ref)
  if impl.kind == nnkRefTy: impl = impl[0].getTypeImpl
  if impl.kind != nnkObjectTy:
    error("pinFind: no generated domain for " & t.repr &
          "; pin this call with pinExact and an explicit domain", t)
  if impl[1].kind == nnkOfInherit: result = domItemsOf(impl[1][0])
  result.add impl[2]

macro objectDomain(T: typedesc): untyped =
  ## The domain of a tuple or plain object type as code: for each case-object
  ## branch (each value of each discriminator's domain) the fields that exist
  ## together are crossed by `fieldRows`; a variant object is the union of its
  ## branches, each built with its discriminator set.
  let ty = T.getType[1]
  let vals = genSym(nskVar, "vals")
  let exh = genSym(nskVar, "exh")
  # the field types are read off a typed nil (no value of the type is
  # declared: a field such as `range[1..100]` has no default)
  let proto = nnkDerefExpr.newTree(newCall(bindSym"protoOf", T))
  var cx = DomCtx(ty: T, vals: vals, exh: exh, proto: proto)
  var gen: NimNode
  if ty.kind == nnkBracketExpr and ty[0].eqIdent("tuple"):
    var fs: seq[NimNode]
    for i in 1 ..< ty.len: fs.add newLit(i - 1)
    gen = domLeaf(cx, fs, @[])
  else:
    gen = domEmit(cx, domItemsOf(ty), @[], @[])
  result = quote do:
    block:
      var `vals`: seq[`T`]
      var `exh` = true
      `gen`
      Domain[`T`](values: `vals`, exhaustive: `exh`)

macro objectRefDomain(R: typedesc): untyped =
  ## INT-81. `objectDomain` of a hierarchy object type `R`'s pointee, each
  ## value built in a cell of `R` (in the same order). A value of such a
  ## type is never copied whole: Nim's C backend generates a broken `=copy`
  ## for a descendant of a case object (it assigns the case parent `Sup` an
  ## integer), so the ref domain builds and copies its cells by reference.
  let r = R.getType[1]
  let pointee = newCall(ident"typeof", nnkDerefExpr.newTree(
    newCall(ident"default", R)))
  let vals = genSym(nskVar, "vals")
  let exh = genSym(nskVar, "exh")
  let proto = nnkDerefExpr.newTree(newCall(bindSym"protoOf", pointee))
  var cx = DomCtx(ty: pointee, vals: vals, exh: exh, proto: proto, refTy: R)
  let gen = domEmit(cx, domItemsOf(r), @[], @[])
  result = quote do:
    block:
      var `vals`: seq[`R`]
      var `exh` = true
      `gen`
      Domain[`R`](values: `vals`, exhaustive: `exh`)

# --- the collection domains (K9d-7) -----------------------------------------
#
# A `seq`, `array`, `set`, `Table` or `HashSet` domain is a deterministic
# finite set, never the type. Each is built from the element type's own
# domain cut to a CORE of at most `collCoreMax` values (`coreOf`: the extremes
# and the middle of an ordinal's range, a string's first values and the SUT's
# literals, a char or integer the SUT names with its neighbours) and listed
# in priority order, at most `seqDomainCap` values (the prefix a nested
# collection is cut to is the first `stringCore`).

# (the domain size constants are declared above the float domain)


proc coreIdx*(n, limit: int): seq[int] =
  ## the indices of an `n`-value domain kept in its core: all of them when
  ## `n <= limit`, else the low end, the middle and the high end
  if n <= limit:
    for i in 0 ..< n: result.add i
    return
  let want = if limit >= 8: @[0, 1, 2, n div 2 - 1, n div 2, n - 3, n - 2, n - 1]
             elif limit >= 4: @[0, 1, n div 2, n - 1]
             else: @[0, n - 1, n div 2]
  for i in want:
    if i >= 0 and i < n and i notin result and result.len < limit: result.add i

proc coreOf*[E](d: Domain[E]; limit: int; spread: var int): seq[E] =
  ## `spread` is how many leading values are the domain's own (the rest are
  ## the SUT's literals); `d` cut to at most `limit` values, plus (for an ordinal other than a
  ## boolean or enum) the integer or char literals of the SUT and each one's
  ## neighbours, at most `collExtraMax` more
  let n = domLen(d.values)
  when E is string:
    for i in 0 ..< min(n, 3): domPut(result, d.values[i])
    for s in stringHintsCur.strs:
      if domLen(result) >= limit: break
      if s.len > 0 and not domHas(result, s) and domHas(d.values, s):
        domPut(result, s)
    spread = domLen(result)
  elif E is SomeFloat:
    # the specials, then the SUT's first two literals with their neighbours
    # (the domain holds them; a float range only those inside it)
    for i in 0 ..< min(n, limit): domPut(result, d.values[i])
    spread = domLen(result)
    when sizeof(E) == 4:
      type B = float32
    else:
      type B = float64
    var added = 0
    for li in 0 ..< min(domLen(stringHintsCur.nums), 2):
      let y = B(stringHintsCur.nums[li])
      for c in [y, fNextUp(y), fNextDown(y)]:
        for i in 0 ..< n:
          if added < collExtraMax and floatKey(B(d.values[i])) == floatKey(c) and
             not domHas(result, d.values[i]):
            domPut(result, d.values[i])
            inc added
  elif prefixDomain(E):
    for i in 0 ..< min(n, limit): domPut(result, d.values[i])
    spread = domLen(result)
  else:
    let ci = coreIdx(n, limit)
    for j in 0 ..< domLen(ci): domPut(result, d.values[ci[j]])
    spread = domLen(result)
    when not (E is distinct) and (E is char or
         (E is Ordinal and not (E is enum) and not (E is bool))):
      var seeds: seq[int]
      when E is char:
        for s in stringHintsCur.strs:
          if s.len == 1 and not domHas(seeds, ord(s[0])) and domLen(seeds) < 2:
            domPut(seeds, ord(s[0]))
      else:
        for k in stringHintsCur.ints:
          if not domHas(seeds, k) and domLen(seeds) < 2: domPut(seeds, k)
      var added = 0
      for si in 0 ..< domLen(seeds):
        let k = seeds[si]
        for x in [k, k - 1, k + 1]:
          let inRange =
            when E is SomeUnsignedInt: x >= 0 and uint64(x) <= uint64(high(E))
            else: x >= ord(low(E)) and x <= ord(high(E))
          if inRange and added < collExtraMax and not domHas(result, E(x)):
            domPut(result, E(x))
            inc added

proc coreOf*[E](d: Domain[E]; limit: int): seq[E] =
  var spread = 0
  coreOf(d, limit, spread)

proc lengthPatterns*(m, n: int): seq[seq[int]] =
  ## index vectors of length `n` over a core of `m` values: all-equal (low,
  ## high, middle), ascending, descending, one outlier at each end (of either
  ## kind), and adjacent duplicates ascending
  if m <= 0 or n <= 0: return
  let hi = m - 1
  let idx = toSeq(0 ..< n)
  result.add idx.mapIt(0)
  result.add idx.mapIt(hi)
  result.add idx.mapIt(hi div 2)
  result.add idx.mapIt(it * m div n)
  result.add idx.mapIt(hi - it * m div n)
  result.add idx.mapIt(if it == 0: hi else: 0)
  result.add idx.mapIt(if it == n - 1: hi else: 0)
  result.add idx.mapIt(if it == 0: 0 else: hi)
  result.add idx.mapIt(if it == n - 1: 0 else: hi)
  result.add idx.mapIt((it div 2) * m div ((n + 1) div 2))

proc seqShapes*(m: int; thresholds: seq[int]; spread = -1): seq[seq[int]] =
  ## The sequences over a core of `m` values, as index vectors in priority
  ## order: empty; each single; the leading pairs and triples; at each of the
  ## SUT's integer literals `k` (and 4, 5, 8) the lengths k-1, k and k+1 filled
  ## with `lengthPatterns`; every pair; every triple (all pairs of positions
  ## when the product is large). The patterns' high end is the last of the
  ## `spread` leading core values (the SUT's own literals follow them).
  let sp = if spread < 0: m else: min(spread, m)
  var seen = initHashSet[seq[int]]()
  template put(v: seq[int]) =
    block:
      let vv = v
      if result.len < seqDomainCap and not seen.containsOrIncl(vv):
        result.add vv
  put newSeq[int](0)
  if m == 0: return
  var lens: seq[int]
  for k in thresholds:
    if k in 1 .. 256:
      for n in [k - 1, k, k + 1]:
        if n >= 1 and n notin lens: lens.add n
  for n in seqFixedLens:
    if n notin lens: lens.add n
  # one sequence of each literal length first (K9d-10): a domain thinned to
  # its prefix to cross with another parameter keeps every length the SUT
  # names (a `symexAssume(data.len == 12)` otherwise rejects every run)
  var early = 0
  for n in lens:
    if n > 3 and early < 16:
      let ps = lengthPatterns(sp, n)
      if ps.len > 0:
        put ps[0]
        inc early
  for a in 0 ..< m: put @[a]
  let q = min(m, 4)
  for a in 0 ..< q:
    for b in 0 ..< q: put @[a, b]
  let q3 = min(m, 3)
  for a in 0 ..< q3:
    for b in 0 ..< q3:
      for c in 0 ..< q3: put @[a, b, c]
  for n in lens:
    for p in lengthPatterns(sp, n): put p
  for a in 0 ..< m:
    for b in 0 ..< m: put @[a, b]
  for r in fieldRows(@[m, m, m], seqTripleFull).rows: put r

proc arrayShapes*(n, m: int; spread = -1): tuple[rows: seq[seq[int]], full: bool] =
  ## The fixed-length-`n` arrays over a core of `m` values: all pairs of
  ## positions (the full product when it is small), every all-equal array, plus
  ## `lengthPatterns`
  if n == 0: return (@[newSeq[int](0)], true)
  if m == 0: return (@[], true)
  var seen = initHashSet[seq[int]]()
  var full = false
  template put(v: seq[int]) =
    block:
      let vv = v
      if result.rows.len < seqDomainCap and not seen.containsOrIncl(vv):
        result.rows.add vv
  if n <= 32:
    let fr = fieldRows(newSeqWith(n, m), fieldProductFull)
    for r in fr.rows: put r
    full = fr.full
  for v in 0 ..< m: put newSeqWith(n, v)
  for p in lengthPatterns(if spread < 0: m else: min(spread, m), n): put p
  result.full = full and result.rows.len < seqDomainCap

proc orderShapes*(m: int): seq[seq[int]] =
  ## The key insertion sequences (index vectors, no repeats) over a core of
  ## `m` keys: empty, each single, every ordered pair of the first eight, every
  ## ascending and descending triple of the first five, all keys either way
  var seen = initHashSet[seq[int]]()
  template put(v: seq[int]) =
    block:
      let vv = v
      if not seen.containsOrIncl(vv): result.add vv
  put newSeq[int](0)
  for a in 0 ..< m: put @[a]
  let q = min(m, 8)
  for a in 0 ..< q:
    for b in 0 ..< q:
      if a != b: put @[a, b]
  let q3 = min(m, 5)
  for a in 0 ..< q3:
    for b in a + 1 ..< q3:
      for c in b + 1 ..< q3:
        put @[a, b, c]
        put @[c, b, a]
  if m > 3:
    put toSeq(0 ..< m)
    put toSeq(0 ..< m).reversed

proc valueShapes*(l, vc: int): seq[seq[int]] =
  ## the value index vectors for `l` entries over `vc` core values: each
  ## single; else all-equal, ascending, descending and an outlier at each end
  if vc <= 0: return
  if l == 0: return @[newSeq[int](0)]
  var seen = initHashSet[seq[int]]()
  template put(v: seq[int]) =
    block:
      let vv = v
      if not seen.containsOrIncl(vv): result.add vv
  if l == 1:
    for v in 0 ..< vc: put @[v]
    return
  let idx = toSeq(0 ..< l)
  for v in 0 ..< vc: put idx.mapIt(v)
  put idx.mapIt(it mod vc)
  put idx.mapIt(vc - 1 - it mod vc)
  if vc >= 2:
    put idx.mapIt(if it == 0: vc - 1 else: 0)
    put idx.mapIt(if it == l - 1: vc - 1 else: 0)

proc seqDomain[E](t: typedesc[seq[E]]): Domain[seq[E]] =
  var spread = 0
  let cv = coreOf(boundaryOf(E), collCoreMax, spread)
  for row in seqShapes(domLen(cv), stringHintsCur.ints, spread):
    var s = newSeq[E](row.len)
    for i, ix in row: s[i] = cv[ix]
    domPut(result.values, s)

proc arrayDomain[I, E](t: typedesc[array[I, E]]): Domain[array[I, E]] =
  let ed = boundaryOf(E)
  var spread = 0
  let cv = coreOf(ed, collCoreMax, spread)
  var probe: array[I, E]
  let (rows, full) = arrayShapes(probe.len, domLen(cv), spread)
  for row in rows:
    var a: array[I, E]
    var j = 0
    for ix in low(I) .. high(I):
      a[ix] = cv[row[j]]
      inc j
    domPut(result.values, a)
  result.exhaustive = full and ed.exhaustive and domLen(cv) == domLen(ed.values)

proc setDomain[E](t: typedesc[set[E]]): Domain[set[E]] =
  let ed = boundaryOf(E)
  let cv = coreOf(ed, collCoreMax)
  # Every value of `E`: for an enum its declared values (`low .. high` of a
  # holey enum spans its holes, which are no members; RFC-0016 INT-84).
  var full: set[E]
  when E is enum:
    for v in declaredValues(E): full.incl v
  else:
    full = {low(E) .. high(E)}
  var seen = initHashSet[set[E]]()
  template put(v: set[E]) =
    block:
      let vv = v
      if not seen.containsOrIncl(vv): domPut(result.values, vv)
  let m = domLen(cv)
  put default(set[E])
  put full
  for i in 0 ..< m: put {cv[i]}
  for i in 0 ..< m:
    for j in i + 1 ..< m: put {cv[i], cv[j]}
  for i in 0 ..< m: put full - {cv[i]}
  var all: set[E]
  for i in 0 ..< m: all.incl cv[i]
  put all
  result.exhaustive = ed.exhaustive and domLen(ed.values) <= 4 and
                      m == domLen(ed.values)

proc tableDomain[K, V](t: typedesc[Table[K, V]]): Domain[Table[K, V]] =
  let kc = coreOf(boundaryOf(K), collCoreMax)
  let vc = coreOf(boundaryOf(V), 3)
  for ko in orderShapes(domLen(kc)):
    for vs in valueShapes(ko.len, domLen(vc)):
      if domLen(result.values) >= seqDomainCap: return
      var tb = initTable[K, V]()
      for i, ki in ko: tb[kc[ki]] = vc[vs[i]]
      domPut(result.values, tb)

proc hashSetDomain[E](t: typedesc[HashSet[E]]): Domain[HashSet[E]] =
  let cv = coreOf(boundaryOf(E), collCoreMax)
  for ko in orderShapes(domLen(cv)):
    var hs = initHashSet[E]()
    for ki in ko: sets.incl(hs, cv[ki])
    domPut(result.values, hs)

# --- the ref and ptr domains (K9d-10) ----------------------------------------
#
# A `ref T` domain is a POOL of heap cells, one pool per pointee type and per
# `setStringHints` (built on first use, then reused), so two parameters, a field
# and a parameter, or two elements of one collection that draw from it meet
# the SAME cells: the parameter product holds both the aliased case (one cell
# at both positions) and the distinct one. The pool, in priority order:
#   nil;
#   fresh cells, one per value of the pointee's own domain core;
#   for a pointee holding a field of the pool's own type (`Node.next`): a cell
#   whose such fields point back at itself (a cycle), a cell pointing at the
#   first fresh cell (a chain of two, so a parameter can be the next of
#   another) and a cell pointing at that one (a chain of three);
#   a second cell holding the first core value (distinct cells, equal values).
# While a pool is built its own type's fields are nil (a recursive pointee's
# core is generated with its ref fields at nil, then linked as above).
# Every cell is snapshotted once its pool is linked, and `nativeRun` restores
# every snapshot before each run: a SUT that writes through a parameter does
# not leak the write into the next run.
# A `ptr T` domain is nil and the addresses of the `ref T` pool's cells (so a
# `ptr T` and a `ref T` parameter can alias); `pointer` is nil and the
# addresses of the `ref int` pool's cells.

const refCoreMax* = 4   ## fresh cells per pool, one per pointee core value

var heapRestores {.threadvar.}: seq[proc () {.closure.}]
var heapIds {.threadvar.}: Table[pointer, int]
var heapEpoch {.threadvar.}: int

proc newHeapEpoch() =
  ## A pool's pointee core holds the SUT's literals (`setStringHints`), so a
  ## new set of hints starts new pools: the old cells are dropped from the
  ## restore list (a value a suite still holds keeps its cell alive).
  inc heapEpoch
  heapRestores.setLen 0
  heapIds.clear()

proc restoreHeapDomain*() =
  for i in 0 ..< system.len(heapRestores): heapRestores[i]()

proc heapIdOf*(p: pointer): int =
  heapIds.getOrDefault(p, -1)

proc registerCell(p: pointer; restore: proc () {.closure.}) =
  ## (not generic: bound here, whatever `add` or `len` a suite declares)
  heapIds[p] = heapIds.len
  heapRestores.add restore

macro hierObject(R: typedesc): bool =
  ## INT-81: `R` is a ref to an object declared `of` another (`RootObj`
  ## included), whose cells `refDomain` builds and copies by reference
  var t = R.getType[1].getTypeImpl
  if t.kind == nnkRefTy: t = t[0].getTypeImpl
  newLit(t.kind == nnkObjectTy and t[1].kind == nnkOfInherit)

proc levelObjType(sym: NimNode): NimNode =
  ## the object type a level of a hierarchy names: a ref alias's pointee
  let impl = sym.getTypeImpl
  if impl.kind == nnkRefTy: impl[0] else: sym

macro copyCellInto(R: typedesc; dst, src: typed): untyped =
  ## INT-81. `dst[]` gets `src[]`'s value without a whole-object copy of
  ## `R`'s pointee (see `objectRefDomain`): the plain fields of each level
  ## one by one (by `fieldPairs`, which reaches a field another module does
  ## not export), and the deepest level holding a `case` (with everything
  ## above it) as that level's own object, whose copy is sound.
  result = newStmtList()
  var names = nnkBracket.newTree()
  var sym = R.getType[1]
  var caseLevel: NimNode = nil
  while true:
    var t = sym.getTypeImpl
    if t.kind == nnkRefTy: t = t[0].getTypeImpl
    if t.kind != nnkObjectTy:
      error("copyCellInto: not an object type: " & sym.repr, sym)
    var hasCase = false
    var own: seq[string]
    proc scan(n: NimNode) =
      case n.kind
      of nnkIdentDefs:
        for i in 0 ..< n.len - 2:
          var nn = n[i]
          if nn.kind == nnkPostfix: nn = nn[1]
          if nn.kind == nnkPragmaExpr: nn = nn[0]
          own.add nn.strVal
      of nnkRecCase: hasCase = true
      of nnkRecList:
        for c in n: scan(c)
      else: discard
    scan(t[2])
    if hasCase:
      caseLevel = levelObjType(sym)
      break
    for nm in own: names.add newLit(nm)
    if t[1].kind != nnkOfInherit: break
    let par = t[1][0]
    if par.kind == nnkSym and par.strVal in ["RootObj", "RootRef"]: break
    sym = par
  if caseLevel != nil:
    result.add quote do:
      cast[ptr `caseLevel`](addr `dst`[])[] =
        cast[ptr `caseLevel`](addr `src`[])[]
  if names.len > 0:
    let n1 = genSym(nskForVar, "n1")
    let f1 = genSym(nskForVar, "f1")
    let n2 = genSym(nskForVar, "n2")
    let f2 = genSym(nskForVar, "f2")
    result.add quote do:
      for `n1`, `f1` in fieldPairs(`dst`[]):
        when `n1` in `names`:
          for `n2`, `f2` in fieldPairs(`src`[]):
            when `n1` == `n2`: `f1` = `f2`

proc cellCopy[R](v: R): R =
  ## INT-81: a new cell holding `v[]`'s value, copied by reference
  new(result)
  copyCellInto(R, result, v)

proc snapshotOf[R](r: R): proc () {.closure.} =
  ## restores `r[]` to what it holds now (a proc of its own per cell: a
  ## closure made in a loop would share the loop's one environment)
  when hierObject(R):
    let saved = cellCopy(r)   # INT-81: by reference
    result = proc () = copyCellInto(R, r, saved)
  else:
    let saved = r[]
    result = proc () = r[] = saved

proc linkSelfFields[R](x: R; to: R) =
  ## every field of `x[]` of the pool's own type `R` set to `to`
  for _, f in fieldPairs(x[]):
    when f is R: f = to

proc fieldOfType(n, r: NimNode): bool =
  case n.kind
  of nnkIdentDefs: sameType(n[^2], r)
  of nnkRecCase:
    if fieldOfType(n[0], r): return true
    for i in 1 ..< n.len:
      if fieldOfType(n[i][^1], r): return true
    false
  else:
    for c in n:
      if fieldOfType(c, r): return true
    false

macro selfLinked(R: typedesc): bool =
  ## the pointee, an object, holds a field of type `R` in some branch or
  ## ancestor (a recursive type)
  let r = R.getType[1]
  var t = r.getTypeImpl
  if t.kind != nnkRefTy: return newLit(false)
  t = t[0].getTypeImpl
  while t.kind == nnkObjectTy:
    if fieldOfType(t[2], r): return newLit(true)
    if t[1].kind != nnkOfInherit: break
    t = t[1][0].getTypeImpl
    if t.kind == nnkRefTy: t = t[0].getTypeImpl
  newLit(false)

proc refDomain[R: ref](t: typedesc[R]): Domain[R] =
  var pool {.global.}: seq[R]
  var state {.global.}: int   # 0 unbuilt, 1 being built, 2 built
  var epoch {.global.}: int
  if state == 2 and epoch != heapEpoch: state = 0
  if state == 1:
    # the pointee's own core asks for this pool while it is built: nil
    return Domain[R](values: @[R(nil)], exhaustive: false)
  if state == 0:
    state = 1
    epoch = heapEpoch
    type P = typeof(default(R)[])
    when hierObject(R):
      # INT-81: a hierarchy object's core is built in cells and copied by
      # reference (`objectRefDomain`), the values `coreOf` keeps of
      # `objectDomain` in the same order
      let full = objectRefDomain(R)
      let ci = coreIdx(domLen(full.values), refCoreMax)
      var core: seq[R]
      for j in 0 ..< domLen(ci): domPut(core, full.values[ci[j]])
      proc cell(v: R): R = cellCopy(v)
    else:
      # an integer pointee keeps its eight boundary points (zero, -1 and 7
      # among them) plus the SUT's literals; any other its core
      let core = coreOf(boundaryOf(P), when P is Ordinal: 8 else: refCoreMax)
      proc cell(v: P): R =
        new(result)
        result[] = v
    var cells: seq[R]
    for i in 0 ..< domLen(core): domPut(cells, cell(core[i]))
    var linked: seq[R]
    when P is object:
      when selfLinked(R):
        if domLen(core) > 0:
          let cyc = cell(core[0])
          linkSelfFields(cyc, cyc)
          let chain = cell(core[min(1, domLen(core) - 1)])
          linkSelfFields(chain, cells[0])
          let chain3 = cell(core[0])
          linkSelfFields(chain3, chain)
          linked = @[cyc, chain, chain3]
    var dup: seq[R]
    if domLen(core) > 0: dup = @[cell(core[0])]
    pool = @[R(nil)]
    # priority order: nil, two fresh, the linked shapes, the rest, the twin
    for i in 0 ..< min(2, domLen(cells)): domPut(pool, cells[i])
    for i in 0 ..< domLen(linked): domPut(pool, linked[i])
    for i in 2 ..< domLen(cells): domPut(pool, cells[i])
    for i in 0 ..< domLen(dup): domPut(pool, dup[i])
    for i in 1 ..< domLen(pool):
      registerCell(cast[pointer](pool[i]), snapshotOf(pool[i]))
    state = 2
  Domain[R](values: pool, exhaustive: false)

proc ptrDomain[Q: ptr](t: typedesc[Q]): Domain[Q] =
  type P = typeof(default(Q)[])
  let refs = refDomain(ref P)
  for i in 0 ..< domLen(refs.values):
    let r = refs.values[i]
    # a cell's address is the ref's own (its "#k" is the cell's); the pool
    # keeps the cell alive for the process
    if r == nil: domPut(result.values, Q(nil))
    else: domPut(result.values, cast[Q](addr r[]))
  result.exhaustive = false

proc pointerDomain[T: pointer](t: typedesc[T]): Domain[pointer] =
  let ps = ptrDomain(ptr int)
  for i in 0 ..< domLen(ps.values): domPut(result.values, cast[pointer](ps.values[i]))
  result.exhaustive = false

proc absorbSubtype*[A, B](da: var Domain[A]; db: Domain[B]) =
  ## `da` gains `db`'s non-nil cells as `A` when `B` is a proper descendant
  ## ref type of `A` (one object, two static types); otherwise nothing
  when A is ref and B is ref and B is A and not (A is B):
    for i in 0 ..< domLen(db.values):
      let x = db.values[i]
      if x != nil and not domHas(da.values, A(x)): domPut(da.values, A(x))

macro underlyingName(T: typedesc): string =
  ## the type behind an alias, for the "no generated domain" message
  newLit(T.getType[1].repr)

proc boundaryOf*[T](t: typedesc[T]): Domain[T] =
  ## The generated domain of one parameter type: every value of `bool`, of a
  ## one-byte ordinal and of an ordinal spanning at most 256 values (so a
  ## `range` is exhaustive when small); every declared value of an enum
  ## (holes excluded); a distinct type's base domain, converted; otherwise the
  ## boundary sample (`boundaryInts`' points that lie in the type).
  when T is bool:
    exhaustive([false, true])
  elif T is enum:
    # every declared value; a holey enum's holes are not values of the type
    var vs: seq[T]
    when T is Ordinal:
      # no holes, so every ordinal from low to high is declared; this is
      # also the form an enum subrange (`range[red .. green]`) takes, whose
      # type node is the range, not the declared values (K9d-11b)
      for v in low(T) .. high(T): domPut(vs, v)
    else:
      for v in declaredValues(T): domPut(vs, v)
    exhaustive(vs)
  elif T is distinct:
    # the base type's domain, each value converted
    let base = boundaryOf(distinctBase(T))
    var vs: seq[T]
    for i in 0 ..< domLen(base.values): domPut(vs, T(base.values[i]))
    Domain[T](values: vs, exhaustive: base.exhaustive)
  elif T is ref:
    refDomain(T)
  elif T is ptr:
    ptrDomain(T)
  elif T is pointer:
    pointerDomain(T)
  elif sizeof(T) == 1 and T is Ordinal:
    var vs: seq[T]
    for v in low(T) .. high(T): domPut(vs, v)
    exhaustive(vs)
  elif T is SomeUnsignedInt:
    var vs: seq[T]
    for x in [low(T), low(T) + 1, T(1), T(7), high(T) - 1, high(T)]:
      if not domHas(vs, x): domPut(vs, x)
    sampled(vs)
  elif T is Ordinal:
    let lo = ord(low(T))
    let hi = ord(high(T))
    var vs: seq[T]
    if hi div 2 - lo div 2 <= 128:
      for v in low(T) .. high(T): domPut(vs, v)
      return exhaustive(vs)
    for x in [lo, lo + 1, -1, 0, 1, 7, hi - 1, hi]:
      if x >= lo and x <= hi and not domHas(vs, T(x)): domPut(vs, T(x))
    sampled(vs)
  elif T is SomeFloat:
    # in the parameter's own width; a float range keeps what lies inside it
    when sizeof(T) == 4:
      let base = floatDomainValues[float32](stringHintsCur.nums)
    else:
      let base = floatDomainValues[float64](stringHintsCur.nums)
    # appended to the result's own field (a local `seq[T]` would not do:
    # `cfloat` and `float32` are one Nim type but two C types, and the
    # instances they share do not compile in C, as in K9d-7b)
    for i in 0 ..< domLen(base):
      let x = base[i]
      when T is range:
        # Nim's check rejects `x < lo or x > hi`: NaN is a value (int6)
        if not (float64(x) < float64(low(T)) or float64(x) > float64(high(T))):
          domPut(result.values, T(x))
      else:
        domPut(result.values, T(x))
    result.exhaustive = false
  elif T is string:
    sampled(stringDomainValues(stringHintsCur))
  elif T is cstring:
    cstringDomain(stringHintsCur)
  elif T is seq:
    seqDomain(T)
  elif T is array:
    arrayDomain(T)
  elif T is set:
    setDomain(T)
  elif T is Table:
    tableDomain(T)
  elif T is HashSet:
    hashSetDomain(T)
  elif T is tuple or (T is object and not (T is ref)):
    objectDomain(T)
  else:
    {.error: "pinFind: no generated domain for " & $T & " (" & underlyingName(T) & ")" &
             "; pin this call with pinExact and an explicit domain".}

proc pinFindJudges*[T](res: SymexResult[T]; tgt: SymexTarget): bool =
  ## Whether `pinFind` judges `res` natively: a definite, trusted, replayable
  ## verdict. Anything else (a decline is K9c's, an undefined-behaviour target
  ## is K10's) is returned as it came, with no record, and no native domain
  ## is built for it: a parameter the walker declines need not have one.
  if res.status == sxUnknown or not res.trusted or
     tgt.kind == stkUndefined or
     (res.status == sxSat and res.soundness.witnessUnsafe):
    return false
  # A nil dereference is a SIGSEGV natively, which no `except` sees
  # (RFC-0005 S8cu): its witness would end this process. It is pinned in a
  # child (`tsymex_rfc0005_s8cu_nil`), never replayed here (K9d-10).
  not (res.status == sxRaised and
       res.raisedTypeId.endsWith("NilAccessDefect"))

proc pinFindJudge*[T](res: SymexResult[T]; key: CellKey; tgt: SymexTarget;
                      file: string; runW: proc (w: T): NativeRun;
                      runD: proc (hit: proc (n: NativeRun): bool;
                                  cap: int): string;
                      combos: int; exh: bool; desc: string): SymexResult[T] =
  ## A verdict `pinFindJudges` admits is judged by `pinJudge` and recorded;
  ## anything else is returned as it came, with no record.
  if not pinFindJudges(res, tgt):
    return res
  let n = min(combos, pinFindCap)
  var idx = newSeq[int](n)
  for i in 0 ..< n: idx[i] = i
  let dom = Domain[int](values: idx, exhaustive: exh and combos <= pinFindCap)
  let d = (if dom.exhaustive: "exhaustive" else: "sampled") & "[" & $n &
          "]: " & desc
  pinJudge(res, key, tgt, dom, file, runW,
           proc (vals: seq[int]; hit: proc (n: NativeRun): bool): string =
             runD(hit, vals.len),
           "symexFind", domDesc = d)

proc convWitness*[T, W](t: typedesc[T]; x: W): T =
  ## The walker's witness value `x` as the declared parameter type `T`. The
  ## witness tuple holds a `range` as its base type, also inside a container
  ## (`seq[range[1..100]]` is witnessed as a `seq[int]`), which no type
  ## conversion turns back: a container and a set are converted
  ## element by element, each element checked against its range (a witness
  ## outside it raises natively, as the SUT's own conversion would). A value
  ## with no conversion fails the pin when it is replayed: it was never
  ## replaced by a default, which could hit or miss by accident.
  when compiles(T(x)):
    T(x)
  elif T is seq and W is seq:
    type E = typeof(default(T)[0])
    for i in 0 ..< system.len(x): domPut(result, convWitness(E, x[i]))
  elif T is array and W is array:
    type E = typeof(default(T)[low(T)])
    var k = 0
    for ix in low(T) .. high(T):
      result[ix] = convWitness(E, x[low(x) + k])
      inc k
  elif T is Table and W is Table:
    # the element types through the iterators (`genericParams` does not
    # read a `range` argument)
    type K = typeof(tables.keys(default(T)))
    type V = typeof(tables.values(default(T)))
    result = initTable[K, V]()
    for k, v in tables.pairs(x): result[convWitness(K, k)] = convWitness(V, v)
  elif T is HashSet and W is HashSet:
    type E = typeof(sets.items(default(T)))
    result = initHashSet[E]()
    for e in sets.items(x): sets.incl(result, convWitness(E, e))
  elif T is set and W is set:
    type E = typeof(system.items(default(T)))
    for e in system.items(x): result.incl convWitness(E, e)
  else:
    # (a tuple holding a ranged container lands here: a field-wise copy
    # into it does not compile in C, the `seq[range]` field and the
    # `seq[int]` one sharing a `=sink` instance)
    raise newException(PinFailure, "pinFind: the witness's " & $W &
      " has no conversion to the parameter type " & $T)

proc holeOf*[T](x: T): string =
  ## "" when no holey enum inside `x` holds a hole; else the hole, named. A
  ## hole is no value of its type (no caller can pass one), and converting
  ## to a holey enum does not check holes, so a witness holding one would
  ## replay an input that does not exist (K9d-11a, INT-84). Read through
  ## fields, elements, keys and values; not through a ref or ptr.
  when T is enum:
    when T isnot Ordinal:
      if x notin declaredValues(T):
        return $T & " ordinal " & $ord(x)
  elif T is seq:
    for i in 0 ..< system.len(x):
      let h = holeOf(x[i])
      if h.len > 0: return h
  elif T is array:
    for i in low(x) .. high(x):
      let h = holeOf(x[i])
      if h.len > 0: return h
  elif T is set:
    for e in system.items(x):
      let h = holeOf(e)
      if h.len > 0: return h
  elif T is Table:
    for k, v in tables.pairs(x):
      let h = holeOf(k) & holeOf(v)
      if h.len > 0: return h
  elif T is HashSet:
    for e in sets.items(x):
      let h = holeOf(e)
      if h.len > 0: return h
  elif (T is object or T is tuple) and compiles(block:
                                                  for f in fields(x): discard):
    for f in fields(x):
      let h = holeOf(f)
      if h.len > 0: return h

proc holeChecked*[T](x: sink T): T =
  let h = holeOf(x)
  if h.len > 0:
    raise newException(PinFailure, "pinFind: the witness holds " & h &
      ", a hole: not a value of the type, so no native input reproduces it")
  x

template witnessAs*(T: typedesc; x: untyped): untyped =
  ## the witness element as the declared parameter type (`convWitness`); a
  ## type the walker does not model (`cstring`: the SUT declines) is never
  ## replayed, and a replay of one fails the pin; a holey enum's hole fails
  ## the pin (`holeOf`)
  holeChecked(convWitness(T, x))

proc fnParamTypes(fn: NimNode): seq[NimNode] =
  let ty = fn.getTypeInst
  doAssert ty.kind in {nnkProcTy, nnkLambda} or ty.len > 0,
    "pinFind: cannot read the parameter list of " & fn.repr
  let fp = ty[0]
  for i in 1 ..< fp.len:
    for _ in 0 ..< fp[i].len - 2:
      let t = fp[i][^2]
      var u = if t.kind == nnkVarTy: t[0] else: t
      # `sink T` / `lent T` are ownership annotations, not part of the type
      if u.kind == nnkBracketExpr and u.len == 2 and
         (u[0].eqIdent("sink") or u[0].eqIdent("lent")): u = u[1]
      # an `openArray[T]` / `varargs[T]` parameter is passed a `seq[T]`
      if u.kind == nnkBracketExpr and u.len == 2 and
         (u[0].eqIdent("openArray") or u[0].eqIdent("varargs")):
        u = nnkBracketExpr.newTree(ident"seq", u[1])
      result.add u

proc unsizedNative(t: NimNode; seen: var HashSet[string]): string =
  ## The type inside `t` (itself, an element, a field, a generic argument, a
  ## ref's or ptr's target) that has no native domain, "" if none. That is
  ## `c_longdouble` (`clongdouble`): Nim declares it `BiggestFloat`, so it
  ## sizes it as 8 bytes, while C stores a `long double` (16 on x86-64). A
  ## `seq` of one is allocated at Nim's size and indexed at C's, so filling
  ## it overruns the heap block (K9d: the dealloc SIGSEGV a `c_longdouble`
  ## parameter's domain once caused).
  case t.kind
  of nnkSym:
    if t.symKind == nskType and t.eqIdent("clongdouble") and
       t.owner.strVal in ["system", "ctypes"]:
      return t.strVal
    if t.symKind != nskType: return ""
    # (a builtin's or generic's symbol is a fresh one at each look, so the
    # key is its name and owner, not its signature hash)
    let h = t.strVal & "/" & t.owner.strVal
    if h in seen: return ""
    seen.incl h
    let impl = t.getTypeImpl
    # a builtin's impl is its own name again (a fresh symbol each time)
    if impl.kind == nnkSym and impl.strVal == t.strVal: return ""
    unsizedNative(impl, seen)
  of nnkIdentDefs:
    unsizedNative(t[^2], seen)
  of nnkEmpty, nnkIdent, nnkLiterals: ""
  else:
    for c in t:
      let r = unsizedNative(c, seen)
      if r.len > 0: return r
    ""

proc unsizedNative(t: NimNode): string =
  var seen: HashSet[string]
  unsizedNative(t, seen)

macro unsizedNativeOf*(T: typedesc): string =
  ## `unsizedNative` of `T` at compile time, for the K9d self-test
  newLit(unsizedNative(T.getTypeInst[1]))

proc namesQuit(n: NimNode): bool =
  ## the routine body calls `quit` (system's): it ends the process that runs it
  if n.kind == nnkSym and n.strVal == "quit" and n.symKind == nskProc and
     n.owner.strVal == "system":
    return true
  for c in n:
    if namesQuit(c): return true

macro pinFind*(fn: typed; target: untyped;
               rest: varargs[untyped]): untyped =
  ## `symexFind(fn, target, rest...)`, its result returned as is, with a
  ## definite verdict pinned natively (`pinFindJudge`). The cell is
  ## `family:generic:k9d/<file>/<fn>/<target>`. A SUT whose own body calls
  ## `quit` is refused at compile time: its native runs are in this process,
  ## which the first one would end (a routine it calls is not inspected).
  let impl = (if fn.kind == nnkSym: fn.getImpl else: fn)
  if impl.kind in RoutineNodes and namesQuit(impl.body):
    error("pinFind: " & fn.repr & " calls quit, which would end the process " &
          "its native runs share; pin it in a child (pinCrash) or leave it " &
          "unpinned", fn)
  let types = fnParamTypes(fn)
  let file = lineInfoObj(fn).filename.splitFile.name
  let key = "k9d/" & file & "/" & fn.repr & "/" & target.repr
  let find = newCall(ident"symexFind", fn, target)
  for a in rest: find.add a
  let res = genSym(nskLet, "res")
  # A parameter type with no native domain (`unsizedNative`) is never given
  # one: the call is returned as it came when it is not judged (the walker
  # declines such a parameter), and a definite verdict over it fails the pin,
  # since no native run could reproduce it.
  for i, t in types:
    let u = unsizedNative(t)
    if u.len > 0:
      let msg = "pinFind: no native domain for parameter " & $(i + 1) &
        " of " & fn.repr & " (" & t.repr & " holds " & u & ", which Nim " &
        "sizes as a float64 while C stores a long double), so a definite " &
        "verdict over it cannot be pinned"
      return quote do:
        block:
          let `res` = `find`
          if pinFindJudges(`res`, `target`):
            raise newException(PinFailure, `msg`)
          `res`
  let w = genSym(nskParam, "w")
  let hit = genSym(nskParam, "hit")
  let cap = genSym(nskParam, "cap")
  let found = genSym(nskVar, "found")
  let count = genSym(nskVar, "count")
  let rejected = genSym(nskVar, "rejected")
  # Witness replay: each field copied into a variable, so `var` params bind.
  let wbody = newStmtList()
  let wcall = newCall(fn)
  # The declared parameter types, as local aliases: the witness tuple holds a
  # `range` as its base type, so the domain and the replay go through these.
  let tdefs = newStmtList()
  var tsyms: seq[NimNode]
  for i in 0 ..< types.len:
    let ts = genSym(nskType, "P" & $i)
    tsyms.add ts
    tdefs.add nnkTypeSection.newTree(
      nnkTypeDef.newTree(ts, newEmptyNode(), types[i]))
  for i in 0 ..< types.len:
    let a = genSym(nskVar, "a" & $i)
    wbody.add nnkVarSection.newTree(nnkIdentDefs.newTree(a, tsyms[i],
      newCall(bindSym("witnessAs", brOpen), tsyms[i], nnkBracketExpr.newTree(w, newLit(i)))))
    wcall.add a
  # A SUT with a result: the native run discards it.
  let rty = fn.getTypeInst[0][0]
  let returns = rty.kind != nnkEmpty and not rty.eqIdent("void")
  template used(c: NimNode): NimNode =
    (if returns: nnkDiscardStmt.newTree(c) else: c)
  wbody.add newCall(bindSym("nativeRun", brOpen), used(wcall))
  # The domain: one generated domain per parameter, nested loops, capped.
  let doms = newStmtList()
  let hints = harvest(fn)
  doms.add newCall(bindSym("setStringHints", brOpen), hintsExpr(hints))
  var domSyms: seq[NimNode]
  var sizesLit = nnkBracket.newTree()
  var exh: NimNode = newLit(true)
  var desc: NimNode = newLit("")
  for i in 0 ..< types.len:
    let d = genSym(nskVar, "d" & $i)
    domSyms.add d
    # The parameter's type as the witness tuple holds it (a type symbol
    # spliced from `getTypeInst` does not bind as a `typedesc` argument).
    doms.add newVarStmt(d, newCall(bindSym("boundaryOf", brOpen), tsyms[i]))
    sizesLit.add newCall(bindSym"domLen", newDotExpr(d, ident"values"))
    exh = infix(exh, "and", newDotExpr(d, ident"exhaustive"))
    let part = newCall(bindSym("describe", brOpen), d)
    desc = if i == 0: part else: infix(infix(desc, "&", newLit(" x ")), "&", part)
  if types.len == 0: desc = newLit("no parameters")
  # which regex constructs the SUT's patterns put in the domain (K9d-9)
  let rxs = regexSummary(hints.pats)
  if rxs.len > 0: desc = infix(desc, "&", newLit(rxs))
  # The parameter product is run in full up to the cap; beyond it, an
  # all-pairs covering array over the parameters' domains (the product's
  # leading rows would otherwise leave the last parameters unvaried).
  let rows = genSym(nskLet, "rows")
  let rowv = genSym(nskForVar, "row")
  # A ref parameter whose type is an ancestor of another's (`b: Base`,
  # `d: Mid`) also ranges over the other's cells, converted: its dynamic type
  # may be the descendant, and the two may be one object (K9d-10).
  for i in 0 ..< types.len:
    for j in 0 ..< types.len:
      if i != j:
        doms.add newCall(bindSym("absorbSubtype", brOpen), domSyms[i], domSyms[j])
  # Two string parameters would cross to more runs than the cap: each is cut
  # to its core first (a string domain is in priority order).
  let thin = newStmtList()
  for d in domSyms: thin.add newCall(bindSym("thinForPairs", brOpen), d)
  doms.add quote do:
    if pairsExceed(@`sizesLit`, pinFindCap): `thin`
  let sizesNow = nnkBracket.newTree()
  for d in domSyms: sizesNow.add newCall(bindSym"domLen", newDotExpr(d, ident"values"))
  doms.add quote do:
    let `rows` = fieldRows(@`sizesNow`, pinFindCap)
    clearStringHints()
  let combos = newDotExpr(newDotExpr(rows, ident"rows"), ident"len")
  exh = infix(exh, "and", newDotExpr(rows, ident"full"))
  let inner = newStmtList()
  var callVars: seq[NimNode]
  var loopVars: seq[NimNode]
  for i in 0 ..< types.len:
    loopVars.add genSym(nskLet, "v" & $i)
    let a = genSym(nskVar, "x" & $i)
    inner.add newLetStmt(loopVars[i], nnkBracketExpr.newTree(
      newDotExpr(domSyms[i], ident"values"),
      nnkBracketExpr.newTree(rowv, newLit(i))))
    inner.add newVarStmt(a, loopVars[i])
    callVars.add a
  let dcall = newCall(fn)
  for a in callVars: dcall.add a
  var shown = newLit("input (")
  for i, v in loopVars:
    shown = infix(shown, "&", newCall(bindSym("showArg", brOpen), v))
    if i < loopVars.high: shown = infix(shown, "&", newLit(","))
  shown = infix(shown, "&", newLit(")"))
  let dused = used(dcall)
  inner.add quote do:
    if `found`.len == 0 and `count` < `cap`:
      inc `count`
      let nr = nativeRun(`dused`)
      if nr.rejected: inc `rejected`
      elif `hit`(nr): `found` = `shown`
  let loops = nnkForStmt.newTree(rowv, newDotExpr(rows, ident"rows"),
                                 newStmtList(inner))
  quote do:
    block:
      let `res` = `find`
      `tdefs`
      `doms`
      pinFindJudge(`res`, cellKey(faGeneric, `key`), `target`, `file` & ".nim",
        proc (`w`: typeof(`res`.witness)): NativeRun = `wbody`,
        proc (`hit`: proc (n: NativeRun): bool; `cap`: int): string =
          var `found` = ""
          var `count` = 0
          var `rejected` = 0
          `loops`
          if `count` > 0 and `rejected` == `count`:
            raise newException(PinFailure, "pinFind: every one of the " &
              $`count` & " generated runs was rejected by symexAssume; " &
              "the pin is vacuous")
          `found`,
        `combos`, `exh`, `desc`)

# --- pinDecline ------------------------------------------------------------

proc pinDeclineJudge*[T](res: SymexResult[T]; key: CellKey; tgt: SymexTarget;
                         kind: SymexErrorKind; file: string;
                         needle: string = "";
                         excluding: set[SymexErrorKind] = {}) =
  let cell = render(key)
  if res.trusted:
    pinFail("pinDecline " & cell & ": the verdict " & $res.status &
            " is trusted; it should decline with " & $kind)
  # An internal walker fault is never an acceptable decline, of any severity.
  for e in res.errors:
    if e.kind == weInternalWalkerFault:
      pinFail("pinDecline " & cell & ": an internal walker fault was recorded: " &
              e.msg)
  # A kind in `excluding` must not be recorded at any severity: the decline
  # has to come from `kind`, not from a broader fallback that also fires.
  for e in res.errors:
    if e.kind in excluding:
      pinFail("pinDecline " & cell & ": " & $e.kind &
              " was recorded and is excluded: " & e.msg)
  if not res.errors.named(kind):
    pinFail("pinDecline " & cell & ": not trusted, but no " & $kind &
            " was recorded; errors: " & kindsOf(res.errors))
  if needle.len > 0:
    var found = false
    for e in res.errors:
      if e.kind == kind and taintsRun(e) and needle in e.msg: found = true
    if not found:
      pinFail("pinDecline " & cell & ": no " & $kind & " message contains \"" &
              needle & "\"; errors: " & show(res.errors))
  writePinRecord(PinRecord(testFile: file, entry: "symexFind", cell: key,
    target: describeTarget(tgt), domain: "-", verdict: pvDeclined,
    walker: $res.status, declineKind: $kind,
    native: "not run: the cell declines"))

template pinDecline*(fn: untyped; key: CellKey; kind: SymexErrorKind;
                     target: untyped = tLabel("hit"); needle: string = "";
                     excluding: set[SymexErrorKind] = {}) =
  ## The cell declines: the verdict is not trusted, `kind` was recorded, no
  ## internal walker fault was, no kind in `excluding` was, and, when
  ## `needle` is given, a `kind` message contains it.
  block:
    let pdRes = symexFind(fn, target, pinSettingsConst)
    pinDeclineJudge(pdRes, key, target, kind, instantiationInfo(-1).filename,
                    needle, excluding)

# --- pinUndefined ----------------------------------------------------------

template pinUndefined*(fn: untyped; key: CellKey; kind: UbKind;
                       tgt: untyped = tLabel("hit")) =
  ## RFC-0016 K10a-axis. The run reaches the label past an operation that is
  ## undefined in `kind` and the verdict carries it (`Soundness.witnessUndefined`
  ## by `kind`): not trusted, a `sxSat`. Recorded as a `pvDeclined` record whose
  ## `declineKind` is `kind`, which is what evidences `errorkind:<kind>` for a
  ## kind that rides a witness instead of halting (no error carries it).
  block:
    let puRes = symexFind(fn, tgt, pinSettingsConst)
    if puRes.trusted:
      pinFail("pinUndefined " & render(key) & ": the verdict is trusted")
    if puRes.status != sxSat:
      pinFail("pinUndefined " & render(key) & ": expected sxSat, got " &
              $puRes.status & "; errors: " & show(puRes.errors))
    if kind notin puRes.soundness.undefinedKinds:
      pinFail("pinUndefined " & render(key) & ": the verdict does not carry " &
              $kind & ": " & $puRes.soundness)
    writePinRecord(PinRecord(testFile: instantiationInfo(-1).filename,
      entry: "symexFind", cell: key, target: describeTarget(tgt),
      domain: "-", verdict: pvDeclined, walker: $puRes.status,
      declineKind: $kind,
      native: "not run: the cell is undefined behaviour"))

# --- pinCap ----------------------------------------------------------------

func capExpectation*(cap: string): tuple[kind: SymexErrorKind, needle: string] =
  ## What a run cut by `cap` records: the kind and a phrase of the message at
  ## its one producing site (`CapKind` is private to `runtime.nim`, so the cap
  ## is named by its member's text; `tsymex_0016_k7a_survivors` pins one site
  ## per member). A cap not listed here has no pin yet.
  case cap
  of "ckFrontier": (beBudgetExhaustedPrune, "path-frontier cap")
  of "ckCallDepth": (beBudgetExhaustedUnmodelled, "call-inlining depth budget")
  of "ckLoopUnwind": (beBudgetExhausted, "while-loop k-unroll budget exhausted")
  of "ckLoopUnwindFollow": (beBudgetExhausted, "following a concrete replay")
  of "ckHeapDepth": (heDepthExhausted, "heap depth budget")
  of "ckVariantForks": (beBudgetExhaustedUnmodelled, "variant constructor fork budget")
  of "ckVariantFieldAllocs": (beBudgetExhaustedUnmodelled, "field-allocation budget")
  of "ckWalkWork": (beBudgetExhaustedPrune, "walk work cap")
  of "ckTermWalkRead": (feUnsupportedOpHavoc, "isIndex: an array of")
  of "ckTermWalkWrite": (feUnsupportedStmtKind, "isIndexAssign: an array of")
  else:
    raise newException(PinFailure, "pinCap: no expectation for cap " & cap)

proc pinCapJudge*[T](res: SymexResult[T]; cap: string; tgt: SymexTarget;
                     file: string) =
  ## The run was cut by `cap`: not trusted, and a tainting error of the cap
  ## site's kind with the site's message was recorded. Writes a `pvDeclined`
  ## record carrying `cap`, so K1's join can evidence `capkind:<cap>`.
  let ex = capExpectation(cap)
  if res.trusted:
    pinFail("pinCap " & cap & ": the verdict " & $res.status & " is trusted")
  var found = false
  for e in res.errors:
    if e.kind == ex.kind and taintsRun(e) and ex.needle in e.msg: found = true
  if not found:
    pinFail("pinCap " & cap & ": no " & $ex.kind & " message contains \"" &
            ex.needle & "\"; errors: " & show(res.errors))
  writePinRecord(PinRecord(testFile: file, entry: "symexFind",
    cell: CellKey(scope: axConstruct, key: "cap/" & cap),
    target: describeTarget(tgt), domain: "-", verdict: pvDeclined,
    walker: $res.status, declineKind: $ex.kind, cap: cap,
    native: "not run: the run is cut by " & cap))

template pinCap*(fn: untyped; cap: static string;
                 target: untyped = tLabel("hit");
                 settings: untyped = pinSettingsConst) =
  ## The run of `fn` is cut by `cap` (a `CapKind` member's name): see
  ## `pinCapJudge`. `settings` lowers the cap where the default cannot reach it.
  block:
    let pcRes = symexFind(fn, target, settings)
    pinCapJudge(pcRes, cap, target, instantiationInfo(-1).filename)

proc pinCapConcolicJudge*(errors: seq[SymexErrorInfo]; cap, desc,
                          file: string) =
  ## RFC-0016 K7c. A concolic replay was cut by `cap`: the collect result's
  ## own `errors` hold a tainting error of the cap site's kind and message
  ## (a collect has no verdict, so there is no `trusted` to read). Writes the
  ## `pvDeclined` record carrying `cap`, entry `concolic`.
  let ex = capExpectation(cap)
  var found = false
  for e in errors:
    if e.kind == ex.kind and taintsRun(e) and ex.needle in e.msg: found = true
  if not found:
    pinFail("pinCapConcolic " & cap & ": no " & $ex.kind & " message " &
            "contains \"" & ex.needle & "\"; errors: " & show(errors))
  writePinRecord(PinRecord(testFile: file, entry: "concolic",
    cell: CellKey(scope: axConstruct, key: "cap/" & cap),
    target: desc, domain: "-", verdict: pvDeclined,
    walker: "concolicCollect", declineKind: $ex.kind, cap: cap,
    native: "not run: the replay is cut by " & cap))

template pinCapConcolic*(fn: untyped; cap: static string; trace, bindings,
                         settings: untyped) =
  ## The `concolicCollect` replay of `fn` over `trace` is cut by `cap`: see
  ## `pinCapConcolicJudge`.
  block:
    let pccRes = concolicCollect(fn, trace, bindings, settings)
    pinCapConcolicJudge(pccRes.errors, cap, astToStr(fn),
                        instantiationInfo(-1).filename)

# --- pinCrash and skipCell -------------------------------------------------

proc crashClassOn*(rc: int; output: string; expect: CrashExpect;
                   windows: bool): bool =
  ## Pure: is `rc` with `output` the `expect` class on that platform? A Nim
  ## program on Windows rarely dies with the raw SEH code: the CRT maps the
  ## divide fault 0xC0000094 to SIGFPE and the access violation to SIGSEGV,
  ## and Nim's handler prints the report and quits with 1. So the class is
  ## decided by evidence: the raw code, or exit 1 plus Nim's own report.
  ## 0xC0000095 (INT_MIN idiv -1) is not mapped by the CRT and arrives raw.
  if windows:
    let code = cast[uint32](int32(rc))
    case expect
    of ceDivTrap:
      code == 0xC0000094'u32 or code == 0xC0000095'u32 or
        (rc == 1 and "SIGFPE: Arithmetic error" in output)
    of ceSegv:
      code == 0xC0000005'u32 or
        # Stack exhaustion: on POSIX the guard page's SIGSEGV, on Windows the
        # raw STACK_OVERFLOW, which the CRT does not map to a signal.
        code == 0xC00000FD'u32 or
        (rc == 1 and "SIGSEGV: Illegal storage access" in output)
    of ceDefect: rc != 0 and "Defect]" in output
    of ceAbnormal: rc != 0
  else:
    case expect
    of ceDivTrap: rc == 128 + 8      # SIGFPE
    of ceSegv: rc == 128 + 11        # SIGSEGV
    of ceDefect: rc != 0 and "Defect]" in output
    of ceAbnormal: rc != 0

proc crashClass(rc: int; output: string; expect: CrashExpect): bool =
  crashClassOn(rc, output, expect, defined(windows))

when defined(windows):
  proc setErrorMode(mode: uint32): uint32
    {.importc: "SetErrorMode", stdcall, dynlib: "kernel32".}

proc appTestFile(): string = splitFile(getAppFilename()).name & ".nim"

proc pinRefused*(key: CellKey; probe: string; flags: openArray[string];
                 mustMention: string) =
  ## The build-cell form of a decline (RFC-0016 section 8.3, Refusals): the
  ## probe is built in a child with `flags` and the BUILD must be refused,
  ## i.e. the compile fails and its output contains `mustMention` (the refused
  ## field, by name). A child that compiles, or that fails without naming the
  ## field (a different error), fails the pin. Recorded as `pvDeclined` with
  ## entry `admitBuild`.
  let pb = prepareProbe("pinRefused", probe, flags)
  let (cout, crc) = execCmdEx(pb.cmd)
  removeDir(pb.dir)
  if crc == 0:
    pinFail("pinRefused " & render(key) & ": the probe compiled; the build " &
            "was not refused")
  if mustMention notin cout:
    pinFail("pinRefused " & render(key) & ": the compile failed, but not by " &
            "naming " & mustMention & ":\n" & cout)
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "admitBuild", cell: key, target: "-", domain: "-",
    verdict: pvDeclined, declineKind: "refused:" & mustMention,
    native: "compile refused", flags: @(pb.args) & @[pb.backend]))

proc runCrashChild(exe: string; args: openArray[string]
                  ): tuple[rc: int, output: string, timedOut: bool] =
  ## Runs `exe` with `args` under a wall-clock budget, stderr into stdout.
  # A fault must die at once with its code, not wait in the error-reporting
  # dialog (the child inherits the error mode).
  when defined(windows):
    let prevMode = setErrorMode(0x0001'u32 or 0x0002'u32)  # FAILCRITICALERRORS, NOGPFAULTERRORBOX
  let p = startProcess(exe, args = args, options = {poStdErrToStdOut})
  when defined(windows): discard setErrorMode(prevMode)
  # Explicit wall-clock budget: waitForExit's timeout path terminates the
  # child with code 0 on Windows, which would read as a clean exit.
  let t0 = epochTime()
  while p.running and epochTime() - t0 < 20.0: sleep(20)
  result.timedOut = p.running
  if result.timedOut: p.kill()
  result.rc = if result.timedOut: -1 else: p.peekExitCode()
  result.output = if result.timedOut: "" else: p.outputStream.readAll()
  p.close()

proc judgeCrash(who: string; rc: int; output: string; timedOut: bool;
                expect: CrashExpect) =
  if timedOut: pinFail(who & ": the probe did not finish")
  if rc == 0:
    pinFail(who & ": the probe exited 0; expected " & $expect & "\n" & output)
  if not crashClass(rc, output, expect):
    pinFail(who & ": exit " & $rc & " is not the expected " & $expect &
            "\n" & output)

proc pinCrash*(key: CellKey; probe: string; flags: openArray[string];
               expect: CrashExpect; kind = "") =
  ## Compiles `probe` in a child with the host's build-relevant defines plus
  ## `flags`, runs it, and asserts the exit class. `probe` is a path to a Nim
  ## file, or the source text itself when it contains a newline. A child that
  ## exits 0 fails. The record is `pvCrashed`: it bypasses every public entry
  ## point, so K1 may use it for a `declined` or `never` cell only. `kind`
  ## is the `SymexErrorKind` the cell declares, when it declares one: a crash
  ## record evidences a cell with a kind only if it names that kind (L-M4).
  let pb = prepareProbe("pinCrash", probe, flags)
  let dir = pb.dir
  let exe = pb.exe
  let args = pb.args
  let backend = pb.backend
  let (cout, crc) = execCmdEx(pb.cmd)
  if crc != 0: pinFail("pinCrash " & render(key) & ": probe build failed:\n" & cout)
  let (rc, output, timedOut) = runCrashChild(exe, [])
  removeDir(dir)
  judgeCrash("pinCrash " & render(key), rc, output, timedOut, expect)
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "pinCrash", cell: key, target: "-", domain: "-",
    verdict: pvCrashed, declineKind: kind,
    native: "rc=" & $rc & " expected=" & $expect,
    flags: @args & @[backend]))

# --- pinCrashSelf: the suite's own SUT, run natively in a child ------------
#
# `pinCrash` builds a probe from source, so the code it crashes is a copy of
# the SUT. `pinCrashSelf` runs THIS test binary again as the child, which
# runs the suite's own SUT on a named input (a "form") and dies there: the
# native truth of a crash claim (a Defect under `--panics:on`, a nil
# dereference) that no in-process run can establish, since the first such
# run would end the process the suite runs in (K9d-12).
#
# The suite dispatches its forms at module level, before its first suite:
#
#   crashForms:
#     case crashForm()
#     of "overflow": sut(high(int))
#     else: discard
#
# A form that returns (or a name no branch knows) exits 0, which fails the pin.

const crashFormArg = "--nelli-crash-form:"

proc crashForm*(): string =
  ## The form this process runs as `pinCrashSelf`'s child, else "".
  if paramCount() >= 1 and paramStr(1).startsWith(crashFormArg):
    paramStr(1)[crashFormArg.len .. ^1]
  else: ""

template crashForms*(body: untyped) =
  ## Module level: in `pinCrashSelf`'s child, run `body` (which reads
  ## `crashForm()`) and exit 0 if it returns; otherwise nothing.
  if crashForm().len > 0:
    body
    echo "NELLI_CRASH_FORM_RETURNED"
    quit 0

proc pinCrashSelf*(key: CellKey; form: string; expect: CrashExpect;
                   kind = "") =
  ## Runs this test binary as a child on `form` (`crashForms`) and asserts
  ## its exit class, as `pinCrash` does for a probe. A child that returns or
  ## exits 0 fails. Recorded as `pinCrash`'s `pvCrashed`, with the form as
  ## the domain: one native input, the one the suite names.
  let who = "pinCrashSelf " & render(key) & " " & form
  let (rc, output, timedOut) = runCrashChild(getAppFilename(),
                                             [crashFormArg & form])
  judgeCrash(who, rc, output, timedOut, expect)
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "pinCrash", cell: key, target: "-", domain: "form:" & form,
    verdict: pvCrashed, declineKind: kind,
    native: "rc=" & $rc & " expected=" & $expect,
    flags: @["self"]))

proc runCrashForm*(form: string): tuple[rc: int, output: string,
                                       timedOut: bool] =
  ## Runs this test binary as a child on `form` (`crashForms`), as
  ## `pinCrashSelf` does, and returns its exit, for a probe whose answer is
  ## either way (RFC-0016 INT-89's MSVC `/Od` probe). A form that returns
  ## exits 0 and prints `NELLI_CRASH_FORM_RETURNED`.
  runCrashChild(getAppFilename(), [crashFormArg & form])

proc skipCell*(key: CellKey; why: string) =
  ## Not run on this build, and why. K2a's census fails a bare `skip(`.
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "skipCell", cell: key, target: "-", domain: "-",
    verdict: pvSkipped, why: why))

proc skipUnadmitted*() =
  ## Not run on this host: `hostAdmission` refused it (a Z3 outside 4.13.4/5.1,
  ## or a build no verified row covers, e.g. cpp under Z3 4.13.4), so a
  ## `symexFind` verdict is `feHostUnadmitted` by design. Recorded as a
  ## `skipCell` on the refusal's own build cell (`z3/unverified` for the Z3,
  ## `profile/unprojectable` for the row), never a bare `skip(`.
  let r = hostAdmission()
  if r.isNone: return
  let k = if r.get.field == bfZ3: "z3/unverified" else: "profile/unprojectable"
  skipCell(CellKey(scope: axBuild, key: k), "host unadmitted by design: " & r.get.reason)

proc pinAdmission*(key: CellKey; refusal: Option[BuildRefusal];
                   field: BuildField; mustMention: string) =
  ## RFC-0016 K5b. The build-cell form of a decline for a configuration this
  ## host cannot build (32-bit, big-endian, arm64, macOS, an unpatched Nim, an
  ## unverified Z3): the caller runs the decision function (`admitBuild` or
  ## `admitHost`) over a SYNTHETIC build description and passes its answer.
  ## The platform is never faked; only the description is. The refusal must be
  ## `field` and its message must contain `mustMention`. Recorded as
  ## `pvDeclined` with entry `admitBuild`, like `pinRefused`.
  if refusal.isNone:
    pinFail("pinAdmission " & render(key) & ": the build was admitted")
  let r = refusal.get
  if r.field != field:
    pinFail("pinAdmission " & render(key) & ": refused on field " & $r.field &
            ", expected " & $field)
  if mustMention notin r.reason:
    pinFail("pinAdmission " & render(key) & ": the reason does not name " &
            mustMention & ": " & r.reason)
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "admitBuild", cell: key, target: "-", domain: "-",
    verdict: pvDeclined, declineKind: "refused:" & $field,
    native: "decision function (synthetic build)"))

proc pinNever*(key: CellKey; holds: bool; native: string) =
  ## RFC-0016 K5b. A `never` cell: a behaviour that stays as it is (by design
  ## or by platform), with `native` saying what the host showed and `holds` the
  ## check the caller made of it. A false `holds` fails the pin. Recorded as
  ## `pvDeclined` with entry `pinNever`, which only a `never` cell accepts.
  if not holds:
    pinFail("pinNever " & render(key) & ": the claim does not hold: " & native)
  writePinRecord(PinRecord(testFile: appTestFile(),
    entry: "pinNever", cell: key, target: "-", domain: "-",
    verdict: pvDeclined, declineKind: "never", native: native))

const floorMeasuredRow* = "linux-c"
  ## The row the floors were measured on (the local run's row). A full run on
  ## it, or a local run (no row), holds a figure to its floor exactly; other
  ## rows are held only at or above it, since a row may legitimately exercise
  ## more (the build axis is row-dependent).

func ratchetsOn*(legRow: string; partial: bool): bool =
  not partial and legRow in ["", floorMeasuredRow]
