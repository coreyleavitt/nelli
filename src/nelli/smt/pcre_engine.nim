## RFC-0005 S8bj. Which engine std/re's libpcre runs an unanchored call on.
##
## `std/re`'s `re()` studies every pattern with PCRE_STUDY_JIT_COMPILE when
## the linked libpcre reports `PCRE_CONFIG_JIT` (Windows builds and most
## Linux distributions' do), and `pcre_exec` then runs the JIT for every
## call without PCRE_ANCHORED. The JIT's start-of-match scan and its match
## limit differ from the interpreter's. So the walker asks, at walk time,
## the library std/re would load: the same names as Nim's `pcre` wrapper,
## `pcre_config(PCRE_CONFIG_JIT)`. A library it cannot load or ask is not a
## verified one (below).
##
## RFC-0005 S8bt (SOUNDNESS). The model is PCRE 8.45's interpreter, checked
## against other builds; the walker reads a regex only when std/re's library
## is one of them (`pcreLibs`), and declines every regex call otherwise
## (`unverifiedLibReason`, read by `pcre_syntax.parseSpec`). S8bj recorded
## the library in the cache key but read every one with 8.45's model.
## RFC-0005 S8bt: a verified build names the engine model its unanchored
## calls are read with (`VerifiedLib.model`, `pcreSearchEngine`): 8.37's
## JIT is modelled (`pcre_jit.nim`, `pcre_select`'s `peJit837`), so its
## searches are decided rather than declined.
import std/[dynlib, strutils, options]
import ./types
import ./admission

type
  PcreEngine* = enum
    ## RFC-0005 S8bt. The engine an unanchored call runs on: the
    ## interpreter (pcre_exec.c, the model's reference), or PCRE 8.37's
    ## JIT. Anchored calls always run on the interpreter (PCRE_ANCHORED is
    ## not a JIT option).
    peInterp, peJit837


const pcreConfigJit = 9'i32   ## pcre.h's PCRE_CONFIG_JIT

when defined(windows):
  when defined(nimOldDlls):
    const pcreLib = "pcre.dll"
  elif defined(cpu64):
    const pcreLib = "pcre64.dll"
  else:
    const pcreLib = "pcre32.dll"
elif defined(macosx):
  const pcreLib = "libpcre(.3|.1|).dylib"
else:
  const pcreLib = "libpcre.so(.3|.1|)"

type PcreConfig = proc (what: int32; where: pointer): int32 {.cdecl, gcsafe.}

var engineKnown {.threadvar.}: bool
var engineJit {.threadvar.}: bool

# RFC-0005 S8bt: a test can stand in another library (`overridePcreLib`).
# A plain global, not a threadvar: the walker may run on another thread.
var libOverride: tuple[on: bool, version: string, jit: bool]

proc overridePcreLib*(version: string; jit: bool) =
  ## RFC-0005 S8bt. Makes `pcreVersion` / `pcreRunsJit` report `version` and
  ## `jit` instead of the loaded library's (tests).
  {.cast(gcsafe).}:
    libOverride = (true, version, jit)

proc clearPcreLibOverride*() =
  {.cast(gcsafe).}:
    libOverride = (false, "", false)

proc overridden(): tuple[on: bool, version: string, jit: bool] =
  {.cast(gcsafe).}:
    result = libOverride

proc probeJit(): bool =
  let h = loadLibPattern(pcreLib)
  if h == nil: return true
  let f = cast[PcreConfig](symAddr(h, "pcre_config"))
  if f == nil: return true
  var v: int32 = 0
  if f(pcreConfigJit, addr v) != 0: return true
  v != 0

proc pcreRunsJit*(): bool =
  ## RFC-0005 S8bj. Whether std/re's unanchored calls run on PCRE's JIT
  ## (true when the library cannot be asked). Cached per thread.
  let o = overridden()
  if o.on: return o.jit
  if not engineKnown:
    engineJit = probeJit()
    engineKnown = true
  engineJit

type PcreVersion = proc (): cstring {.cdecl, gcsafe.}

var versionKnown {.threadvar.}: bool
var versionStr {.threadvar.}: string

proc pcreVersion*(): string =
  ## RFC-0005 S8bj. std/re's libpcre's `pcre_version()` ("8.45 2021-06-15"),
  ## "" when it cannot be asked. Cached per thread.
  let o = overridden()
  if o.on: return o.version
  if not versionKnown:
    versionKnown = true
    let h = loadLibPattern(pcreLib)
    if h != nil:
      let f = cast[PcreVersion](symAddr(h, "pcre_version"))
      if f != nil: versionStr = $f()
  versionStr

proc pcreOlderThan*(major, minor: int): bool =
  ## RFC-0005 S8bt. Whether std/re's libpcre is older than `major.minor`
  ## (true when it cannot be asked).
  let v = pcreVersion()
  var ma, mi = 0
  var i = 0
  while i < v.len and v[i] in {'0'..'9'}:
    ma = ma * 10 + ord(v[i]) - ord('0')
    inc i
  if i >= v.len or v[i] != '.': return true
  inc i
  while i < v.len and v[i] in {'0'..'9'}:
    mi = mi * 10 + ord(v[i]) - ord('0')
    inc i
  ma < major or (ma == major and mi < minor)

proc pcreBefore838*(): bool =
  ## RFC-0005 S8bj. Whether std/re's libpcre is older than 8.38 (true when
  ## it cannot be asked). PCRE 8.37 (the Windows legs') drops the caseless
  ## flag of a required character after a `{0}` item: `x{0}(?i)a` does not
  ## match "A" there, and does in 8.45 (probed).
  pcreOlderThan(8, 38)

proc pcreEngineName*(): string =
  ## The engine as the symex cache key records it (with the version).
  (if pcreRunsJit(): "pcre-jit-" else: "pcre-interp-") &
    pcreVersion().split(' ')[0]

type PcreSite* = enum
  pcSearch                ## the walker's regex model, reading the library

func pcreLibKey(version: string; jit: bool): string =
  version & "|" & (if jit: "jit" else: "interp")

func pcreRow(version: string; jit: bool; model: PcreEngine;
             evidence: string): tuple[key: string,
                                      row: Row[PcreSite, PcreEngine]] =
  (pcreLibKey(version, jit), modelled[PcreSite, PcreEngine](
    model, {pcSearch}, evidence))

const pcreLibs* = axisTable[PcreSite, PcreEngine](axBuild, [
  ## RFC-0016 ADM-1 (was RFC-0005 S8bt's `pcreLibs`). A libpcre build the
  ## model has been checked against: its `pcre_version()` string and engine
  ## (the key), the engine model its unanchored calls are read with (the
  ## payload), and the evidence (the note).
  pcreRow("8.45 2021-06-15", false, peInterp,
    "the model's own reference: every regex suite (Linux test image)"),
  pcreRow("8.37 2015-04-28", true, peJit837,
    "every regex suite on the Windows legs (Nim's pcre64.dll, JIT), the " &
    "S8bj tri-oracle and the S8bj suites against a local JIT build"),
  pcreRow("8.37 2015-04-28", false, peInterp,
    "the S8bj tri-oracle: identical to 8.45's interpreter on 56764 verb " &
    "patterns, and the start-of-match data on 142108 patterns but the " &
    "declined `{0}` case")])

func admitPcreLib*(version: string; jit: bool): Admit[PcreEngine] =
  ## RFC-0005 S8bt, on the admission interface. The library `version` on
  ## that engine, admitted with the engine model its unanchored calls are
  ## read with. Absent is `psUnverifiedLib`, which is the walker's
  ## `psUnknown` (a `PcreParse` status), not a `SymexErrorKind`: the decline
  ## carries no kind.
  pcreLibs.admit(pcreLibKey(version, jit), pcSearch, absent = none(SymexErrorKind))

proc isVerifiedLib*(version: string; jit: bool): bool =
  ## RFC-0005 S8bt. Whether `version` on that engine is a verified build.
  admitPcreLib(version, jit).admitted

proc pcreLibVerified*(): bool =
  ## RFC-0005 S8bt. Whether std/re's libpcre is a verified build.
  isVerifiedLib(pcreVersion(), pcreRunsJit())

proc unverifiedLibReason*(): string =
  ## RFC-0005 S8bt. Why the walker declines every regex call with std/re's
  ## libpcre, "" when it is a verified build.
  if pcreLibVerified(): return ""
  var known: seq[string]
  for k in pcreLibs.keys:
    let p = k.split('|')
    known.add p[0].split(' ')[0] & (if p[1] == "jit": " JIT" else: "")
  "std/re's libpcre (" &
    (if pcreVersion().len == 0: "a version the walker cannot ask"
     else: pcreVersion()) &
    (if pcreRunsJit(): ", JIT" else: ", interpreter") &
    ") is not a build the regex model is verified against (" &
    known.join(", ") & "): psUnverifiedLib"

proc pcreSearchEngine*(): PcreEngine =
  ## RFC-0005 S8bt. The engine model of std/re's unanchored calls (`find`,
  ## `contains`, `findBounds`, `replace`): the verified build's. (An
  ## unverified library declines every call before this is asked.)
  let a = admitPcreLib(pcreVersion(), pcreRunsJit())
  if a.admitted: a.payload else: peInterp
