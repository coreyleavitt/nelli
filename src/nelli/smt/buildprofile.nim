## RFC-0016 W1-c1a (section 8.3). The one place this build's compile-time
## options are read for the Wave-1 fields: the runtime checks, `--panics`, the
## memory model, the backend and `--exceptions`, plus the `danger`/`release`
## defines and the threads and trace switches the cache key's `|bf=` segment
## renders. Everything else that wants to know "what build is this" asks
## `buildSemantics`; `buildSegment` is the text the cache key carries.
##
## `check_options.nim`'s `defaultOn` model is unchanged: it reads
## `buildSemantics.checks` as its command-line baseline, and `routineChecks`
## stays an absolute deviation from `defaultOn`, not from this profile.
##
## `buildSemantics` is a constant of THIS module, evaluated where it is first
## compiled. A module that imports nelli under a `{.push fieldChecks: off.}` (or
## any other push of a check option) therefore records those checks as off in
## the profile, and nothing in nelli can tell that from a command line that set
## them off: `compileOption` is all the compiler offers a library, and it
## answers for the push. The profile is NOT a fail-closed disagreement and the
## walker does not decline (`feCheckOption`) for it; it takes the push as the
## build. For `overflowChecks` that means `buildWraps()` holds and the walker
## models the unchecked arithmetic of a checks-off build (`ubSignedOverflow`),
## for every routine of a program whose real build checks overflow. Pinned by
## `tsymex_0016_wa_importpush`. Import nelli before the push.
##
## RFC-0016 K5a (part 1). The profile is split by when a fact is known:
## `BuildSemantics` (compile time, `const buildSemantics`), `HostSemantics`
## (run time: the Z3 version and the PCRE engine, read once at the first
## `symexFind`) and `BuildProvenance` (rendered on findings, never keyed).
## `rowOf` projects a build onto the rows the cells claim, and `admitBuild`
## refuses by name a build that no row covers. `-d:nelliFwrapv` is PRODUCED
## here (`{.passC: "-fwrapv".}`), never read: `querySetting` cannot see
## `--passC`, so a `-fwrapv` a consumer passes by hand is invisible and is not
## trusted.
##
## This module imports no `z3`: `symex.nim` asks `admitBuild` before it
## imports `z3`, and `import nelli` stays Z3-free. The Z3 version is therefore
## passed in (`z3VersionOf(fullVersion)`), read by `symex.nim`.
import std/[strutils, algorithm, options]
import ./pcre_engine
export pcre_engine.PcreEngine

type
  CheckOption* = enum
    coField = "fieldChecks"
    coOverflow = "overflowChecks"
    coRange = "rangeChecks"
    coBound = "boundChecks"
    coObj = "objChecks"
    coNan = "nanChecks"
    coInf = "infChecks"
    coAssert = "assertions"
      ## Never a deviation: it is read only where the walker models an assert of
      ## its own (`assertsMaybeOff`). `checks` turns it with the rest.

  MemModel* = enum
    mmOrc = "orc", mmArc = "arc", mmAtomicArc = "atomicArc", mmRefc = "refc",
    mmMarkAndSweep = "markAndSweep", mmBoehm = "boehm", mmGo = "go",
    mmNone = "none", mmOther = "other"

  ExcMode* = enum
    exGoto = "goto", exSetjmp = "setjmp", exQuirky = "quirky", exCpp = "cpp",
    exDefault = "default"

  Backend* = enum
    beC = "c", beCpp = "cpp", beObjc = "objc", beJs = "js"

  OptLevel* = enum
    ## The C compiler's optimisation level. Only `optUnknown` exists: Nim's
    ## `--opt` is readable (`compileOption("opt", ...)`), but the `-O` level the
    ## C compiler ends up with is not. A `--passC:-O2`, a `nim.cfg` or a
    ## `{.localPassC.}` is invisible to `querySetting`, so reporting `--opt`
    ## would be a guess that a hidden flag silently falsifies. A member is
    ## added only when a source for it can be produced, as `nelliFwrapv` is.
    optUnknown = "unknown"

  Cpu* = enum
    cpuAmd64 = "amd64", cpuI386 = "i386", cpuArm64 = "arm64", cpuArm = "arm",
    cpuOther = "other"

  Os* = enum
    osLinux = "linux", osWindows = "windows", osMacosx = "macosx",
    osOther = "other"

  Endian* = enum
    enLittle = "little", enBig = "big"

  CaseObjMode* = enum
    ## `-d:nimOldCaseObjects` keeps a case object's old fields across a
    ## discriminant change; the default zeroes them.
    cmStrict = "strict", cmOld = "old"

  Z3Version* = enum
    ## The libz3 the process loaded. `z3Unread` until the host is read.
    z3Unread = "unread", z3v4_13_4 = "4.13.4", z3v5_1 = "5.1",
    z3Other = "other"

  CcFamily* = enum
    ccGcc = "gcc", ccClang = "clang", ccVcc = "vcc", ccOther = "other"

  CFlag* = enum
    ## C compiler flags that change what a signed or float operation means and
    ## that nelli cannot see (`querySetting` does not report `--passC`).
    cfFwrapv = "-fwrapv", cfTrapv = "-ftrapv", cfFastMath = "-ffast-math",
    cfSanitize = "-fsanitize"

  BuildRow* = enum
    ## The rows a cell claims. Z3 5.1 is the Z3 of the two Linux rows, so it is
    ## not a row of its own; `brZ3v4_13_4` is Linux c under Z3 4.13.4.
    brLinuxC = "linux-c", brLinuxCpp = "linux-cpp",
    brZ3v4_13_4 = "linux-c-z3-4.13.4", brMingw = "mingw", brMsvc = "msvc"

  BuildSemantics* = object
    ## What the build compiles in that changes what the native `fn` does.
    checks*: set[CheckOption]   ## the command line's checks, `nilChecks` aside
    panics*: bool               ## `--panics:on`
    mm*: MemModel
    exceptions*: ExcMode
    backend*: Backend
    opt*: OptLevel              ## always `optUnknown`, see `OptLevel`
    fwrapv*: bool               ## `-d:nelliFwrapv`: produced, see below
    ptrBits*: int               ## `sizeof(pointer) * 8`; Nim's `int` has this width
    cpu*: Cpu
    os*: Os
    endian*: Endian
    caseObjects*: CaseObjMode
    danger*, release*: bool     ## code may branch on them with `when defined`
    threads*, stackTrace*, lineTrace*: bool

  HostSemantics* = object
    ## Run time, read once at the first `symexFind` call.
    pcre*: PcreEngine           ## `peUnverified` for a libpcre not in `verifiedLibs`
    z3*: Z3Version

  BuildProvenance* = object
    ## Rendered on findings and pin records, never keyed.
    ccFamily*: CcFamily
    nimVersion*, patchset*: string  ## `patchset` is "": the compiler cannot report it
    assumedAbsent*: set[CFlag]      ## flags nelli assumes the build does not pass

when defined(nelliFwrapv) and not defined(vcc):
  {.passC: "-fwrapv".}

const buildSemantics*: BuildSemantics = block:
  var b: BuildSemantics
  when compileOption("fieldChecks"): b.checks.incl coField
  when compileOption("overflowChecks"): b.checks.incl coOverflow
  when compileOption("rangeChecks"): b.checks.incl coRange
  when compileOption("boundChecks"): b.checks.incl coBound
  when compileOption("objChecks"): b.checks.incl coObj
  when compileOption("nanChecks"): b.checks.incl coNan
  when compileOption("infChecks"): b.checks.incl coInf
  when compileOption("assertions"): b.checks.incl coAssert
  b.panics = defined(nimPanics)
  b.mm =
    when compileOption("mm", "orc"): mmOrc
    elif compileOption("mm", "arc"): mmArc
    elif compileOption("mm", "atomicArc"): mmAtomicArc
    elif compileOption("mm", "refc"): mmRefc
    elif compileOption("mm", "markAndSweep"): mmMarkAndSweep
    elif compileOption("mm", "boehm"): mmBoehm
    elif compileOption("mm", "go"): mmGo
    elif compileOption("mm", "none"): mmNone
    else: mmOther
  b.exceptions =
    when compileOption("exceptions", "goto"): exGoto
    elif compileOption("exceptions", "setjmp"): exSetjmp
    elif compileOption("exceptions", "quirky"): exQuirky
    elif compileOption("exceptions", "cpp"): exCpp
    else: exDefault
  b.backend =
    when defined(js): beJs
    elif defined(cpp): beCpp
    elif defined(objc): beObjc
    else: beC
  b.opt = optUnknown
  b.fwrapv = defined(nelliFwrapv)
  b.ptrBits = sizeof(pointer) * 8
  b.cpu =
    when defined(amd64): cpuAmd64
    elif defined(i386): cpuI386
    elif defined(arm64): cpuArm64
    elif defined(arm): cpuArm
    else: cpuOther
  b.os =
    when defined(linux): osLinux
    elif defined(windows): osWindows
    elif defined(macosx): osMacosx
    else: osOther
  b.endian = (when cpuEndian == littleEndian: enLittle else: enBig)
  b.caseObjects = (when defined(nimOldCaseObjects): cmOld else: cmStrict)
  b.danger = defined(danger)
  b.release = defined(release)
  b.threads = compileOption("threads")
  b.stackTrace = compileOption("stackTrace")
  b.lineTrace = compileOption("lineTrace")
  b

func checkNames*(cs: set[CheckOption]): seq[string] =
  ## Alphabetical, as the key has always listed them.
  for c in cs: result.add $c
  result.sort()

func renderBuildFlags*(checksOn: seq[string]; danger, release: bool;
                       mm, backend, exceptions: string;
                       threads, stackTrace, lineTrace: bool;
                       fwrapv = false): string =
  ## The `|bf=` text, from already-rendered parts (the explicit-argument form
  ## `buildFlagsSegment` keeps for tests that vary one part).
  "ck=" & checksOn.join(",") &
    (if danger: "+danger" else: "") &
    (if release: "+release" else: "") &
    "+mm=" & mm &
    "+be=" & backend &
    "+ex=" & exceptions &
    (if threads: "+thr" else: "") &
    (if stackTrace: "+st" else: "") &
    (if lineTrace: "+lt" else: "") &
    (if fwrapv: "+fwrapv" else: "")   ## rendered only when on: default keys hold

func buildSegment*(b: BuildSemantics = buildSemantics): string =
  ## The cache key's `|bf=` segment for build `b` (this build by default).
  renderBuildFlags(checkNames(b.checks), b.danger, b.release, $b.mm,
                   $b.backend, $b.exceptions, b.threads, b.stackTrace,
                   b.lineTrace, b.fwrapv)

const buildProvenance*: BuildProvenance = block:
  var p: BuildProvenance
  p.ccFamily =
    when defined(vcc): ccVcc
    elif defined(clang): ccClang
    elif defined(gcc): ccGcc
    else: ccOther
  p.nimVersion = NimVersion
  p.patchset = ""
  # nelli cannot read the C flags a build passes; it assumes none of these is
  # present, except the one it produces itself.
  p.assumedAbsent = {cfFwrapv, cfTrapv, cfFastMath, cfSanitize}
  when defined(nelliFwrapv) and not defined(vcc): p.assumedAbsent.excl cfFwrapv
  p

func z3VersionOf*(fullVersion: string): Z3Version =
  ## `z3FullVersion()` ("4.13.4.0", "5.1.0.0") as a profile member. The two
  ## versions the suite runs against are members; any other is `z3Other`.
  let parts = fullVersion.strip().split('.')
  if parts.len >= 3 and parts[0] == "4" and parts[1] == "13" and parts[2] == "4":
    z3v4_13_4
  elif parts.len >= 2 and parts[0] == "5" and parts[1] == "1":
    z3v5_1
  else:
    z3Other

type
  BuildField* = enum
    ## The build fields `admitBuild` can refuse. Its string value is the name
    ## the refusal message and the `pinRefused` probes quote.
    bfMm = "mm"
    bfPtrBits = "ptrBits"
    bfEndian = "endian"
    bfFwrapv = "fwrapv"
    bfRow = "row"
    bfOs = "os"
    bfCpu = "cpu"
    bfZ3 = "z3"

  BuildRefusal* = object
    field*: BuildField
    reason*: string

func rowOf*(b: BuildSemantics; h: HostSemantics; p: BuildProvenance
           ): Option[BuildRow] =
  ## RFC-0016 K5a (section 8.3). The one projection of a build onto the rows
  ## cells claim, `none` when no row covers it. Every field is accounted for:
  ## it selects the row, it makes the build unprojectable, or it is neutral
  ## with the reason written here (each claim is pinned by K5b's cross-build
  ## cfg suites, not by this function). `h.z3 == z3Unread` is the compile-time
  ## question ("can any host make this a row?"): it takes the Z3 the row's CI
  ## image provisions.
  ##
  ## Neutral, and why:
  ##  * `checks`, `panics`, `danger`, `release`, `threads`, `stackTrace`,
  ##    `lineTrace`: they change verdicts, which is why the cache key carries
  ##    them, but every cell is pinned per check set and `release`/`danger`
  ##    act only through `checks`. They pick no row.
  ##  * `opt`: neutral except through undefined behaviour (K10); and it is
  ##    unreadable, so it is `optUnknown` on every build.
  ##  * `mm`: arc, atomicArc and orc agree except for the cycle collector (a
  ##    `never` cell, S8cs). The other models are not pinned: unprojectable.
  ##  * `exceptions`: goto and setjmp are pinned (K5b); `cpp` is the cpp
  ##    backend's own mode and `default` follows the backend. `quirky` drops
  ##    raise semantics the walker models: unprojectable.
  ##  * `fwrapv`: defines `+`, `-`, `*` and negation, which the walker models
  ##    (`ubSignedOverflow` is not raised); K5b pins it. `vcc` has no such
  ##    flag, so it is unprojectable there.
  ##  * `caseObjects`: the old mode keeps fields across a discriminant change;
  ##    no cell is pinned under it: unprojectable.
  ##  * `host.pcre`: an unverified libpcre declines each regex call by itself
  ##    (`psUnverifiedLib`), so it is not a reason to refuse the build.
  ##  * `provenance.nimVersion`, `patchset`, `assumedAbsent`: reported, not
  ##    projected.
  if b.ptrBits != 64 or b.endian != enLittle or b.cpu != cpuAmd64:
    return none(BuildRow)
  if b.caseObjects != cmStrict: return none(BuildRow)
  case b.mm
  of mmOrc, mmArc, mmAtomicArc: discard
  of mmRefc, mmMarkAndSweep, mmBoehm, mmGo, mmNone, mmOther:
    return none(BuildRow)
  case b.exceptions
  of exGoto, exSetjmp, exCpp, exDefault: discard
  of exQuirky: return none(BuildRow)
  if b.fwrapv and p.ccFamily == ccVcc: return none(BuildRow)
  case b.os
  of osLinux:
    # gcc and clang: rows are keyed by OS and backend, not by the Linux C
    # compiler (the family is provenance, never keyed); K10's UBSan leg runs
    # both. Any other Linux compiler has no leg at all.
    if p.ccFamily notin {ccGcc, ccClang}: return none(BuildRow)
    case b.backend
    of beC:
      case h.z3
      of z3Unread, z3v5_1: some(brLinuxC)
      of z3v4_13_4: some(brZ3v4_13_4)
      of z3Other: none(BuildRow)
    of beCpp:
      case h.z3
      of z3Unread, z3v5_1: some(brLinuxCpp)
      of z3v4_13_4, z3Other: none(BuildRow)
    of beObjc, beJs: none(BuildRow)
  of osWindows:
    if b.backend != beC: return none(BuildRow)
    if h.z3 notin {z3Unread, z3v4_13_4}: return none(BuildRow)
    case p.ccFamily
    of ccGcc: some(brMingw)
    of ccVcc: some(brMsvc)
    of ccClang, ccOther: none(BuildRow)
  of osMacosx, osOther: none(BuildRow)

const unreadHost*: HostSemantics = HostSemantics(pcre: peUnverified, z3: z3Unread)
  ## What the compile-time half of `admitBuild` knows of the host: nothing.

func admitBuild*(b: BuildSemantics = buildSemantics;
                 p: BuildProvenance = buildProvenance): Option[BuildRefusal] =
  ## RFC-0016 W1-c1b, K5a (section 8.3, Refusals). `none` when `nelli/symex`
  ## runs on build `b`, else the first refusal, by `BuildField`. The
  ## compile-time half: pure and compile-time evaluable; `symex.nim` calls it
  ## once, before it imports `z3`, since under refc the `z3` import is the
  ## first thing to fail. `--mm:refc` is D-0016-7 (its heap and destructor
  ## timing are not a verified build, and nim-z3's `=destroy` hooks do not
  ## compile under it). arm64 and macOS are refused until a CI leg runs the
  ## suite there. The host half (an unverified Z3) is `admitHost`.
  if b.mm == mmRefc:
    return some(BuildRefusal(field: bfMm,
      reason: "mm=refc is not a verified build (D-0016-7); use --mm:orc or --mm:arc"))
  if b.ptrBits != 64:
    return some(BuildRefusal(field: bfPtrBits,
      reason: "a " & $b.ptrBits & "-bit int is not a verified build; " &
              "only 64-bit targets have a CI leg"))
  if b.endian != enLittle:
    return some(BuildRefusal(field: bfEndian,
      reason: "a big-endian target is not a verified build"))
  if b.os == osMacosx:
    return some(BuildRefusal(field: bfOs,
      reason: "macOS is not a verified build until a CI leg runs the suite there"))
  if b.cpu in {cpuArm64, cpuArm}:
    return some(BuildRefusal(field: bfCpu,
      reason: $b.cpu & " is not a verified build until a CI leg runs the " &
              "suite there"))
  if b.fwrapv and p.ccFamily == ccVcc:
    return some(BuildRefusal(field: bfFwrapv,
      reason: "-d:nelliFwrapv has no effect under vcc, which has no " &
              "-fwrapv; signed overflow stays undefined there"))
  if rowOf(b, unreadHost, p).isNone:
    return some(BuildRefusal(field: bfRow,
      reason: "no verified build row covers this profile (" &
              "os=" & $b.os & ", cpu=" & $b.cpu & ", backend=" & $b.backend &
              ", mm=" & $b.mm & ", exceptions=" & $b.exceptions &
              ", caseObjects=" & $b.caseObjects & ", cc=" & $p.ccFamily &
              "); rows: linux c, linux cpp, z3 4.13.4, mingw, msvc"))
  none(BuildRefusal)

func admitHost*(h: HostSemantics; b: BuildSemantics = buildSemantics;
                p: BuildProvenance = buildProvenance): Option[BuildRefusal] =
  ## RFC-0016 K5a. The host half of the refusal: a Z3 that no row covers. Pure.
  ## NOT wired into `symexFind` in part 1 (what a refused first call returns
  ## is a decision; see the handoff).
  if h.z3 == z3Other:
    return some(BuildRefusal(field: bfZ3,
      reason: "the loaded libz3 is not a verified version (4.13.4, 5.1)"))
  if rowOf(b, h, p).isNone:
    return some(BuildRefusal(field: bfRow,
      reason: "no verified build row covers this build under z3=" & $h.z3))
  none(BuildRefusal)

func refusalMessage*(a: BuildRefusal): string =
  ## The compile-time error text for a refused build.
  "nelli/symex: this build is refused: " & a.reason & " [field: " & $a.field & "]"
