## RFC-0016 W1-c1a (section 8.3). The one place this build's compile-time
## options are read for the Wave-1 fields: the runtime checks, `--panics`, the
## memory model, the backend and `--exceptions`, plus the `danger`/`release`
## defines and the threads and trace switches the cache key's `|bs=` segment
## (`buildSegment`) renders. Everything else that wants to know "what build is this" asks
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
import ./admission
import ./errorkind
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
    cfSanitize = "-fsanitize", cfFpContract = "-ffp-contract=fast",
    cfNoStrictAliasing = "-fno-strict-aliasing"

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
    pcreVersion*: string        ## `pcre_version()` up to its first space ("8.45"), "" if unaskable
    pcreJit*: bool              ## whether std/re's unanchored calls run on the JIT
    z3*: Z3Version
    z3Full*: string             ## `z3FullVersion()` as loaded ("4.13.4.0"); "" until read
      ## The last three keep the cache key as fine as it was: `pcre` maps 8.37
      ## without the JIT and 8.45 both to `peInterp`, and `z3` maps every
      ## unverified version to `z3Other`. Two libraries that differ keep two keys.

  BuildProvenance* = object
    ## Rendered on findings and pin records, never keyed.
    ccFamily*: CcFamily
    nimVersion*: string
    patchset*: string               ## the backports the probes below saw ("" on a stock Nim)
    stockNim*: bool                 ## RFC-0016 K5b: the probes saw an unpatched Nim
    assumedAbsent*: set[CFlag]      ## flags nelli assumes the build does not pass

const buildIsExecutable* = not (compileOption("app", "lib") or
                                compileOption("app", "staticlib"))
  ## RFC-0016 PRC-02b/02m. This build links as an executable. The patched
  ## compiler writes the method dispatch and subtype-hook table accessors for
  ## executables only, so a library build must not import them
  ## (`replayproc.hasMethodTable`, `hasSubtypeTable`). Read here with every
  ## other build read (K5a).

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

func renderField(v: set[CheckOption]): string =
  checkNames(v).join(",")

func renderField(v: bool): string =
  if v: "1" else: "0"

func renderField(v: string): string =
  escape(v)

func renderField[T: enum | SomeInteger](v: T): string =
  $v

const buildSegmentTag* = "bs1"
  ## The segment's version. A change of how a field is rendered, or of the
  ## separators, bumps it; a new or renamed field needs no bump, since the
  ## field's name is in the text.

func buildSegment*(b: BuildSemantics; h: HostSemantics): string =
  ## RFC-0016 K5a (section 8.3). The cache key's build segment: every field of
  ## `BuildSemantics` and `HostSemantics`, by `fieldPairs`, as `name=value`
  ## under a versioned tag. A field added to either object is keyed by being
  ## added; none can be forgotten. (Nim's `$` on an object changes with any
  ## field rename or reorder, so it is not used.) Example, Linux c:
  ##
  ##   bs1<build:checks=assertions,...;panics=0;mm=orc;...|host:pcre=...>
  result = buildSegmentTag & "<build:"
  var first = true
  for name, v in b.fieldPairs:
    if not first: result.add ';'
    first = false
    result.add name & "=" & renderField(v)
  result.add "|host:"
  first = true
  for name, v in h.fieldPairs:
    if not first: result.add ';'
    first = false
    result.add name & "=" & renderField(v)
  result.add '>'

# RFC-0016 K5b. The compiler cannot report which patches it carries (no define
# or version string says), so the patched Nim 2.2.10 is identified by what it
# DOES: each probe is a program a stock 2.2.10 rejects and the toolchain's
# backport accepts. `compiles` evaluates them where this module is compiled.
# They cover two of the seven backports (the ones a `compiles` can reach: both
# are semantic-pass fixes); the others (a codegen fix, the allocator) are not
# probed, so a toolchain carrying only those would read as stock and be
# refused, never the reverse.
type
  ProbeBox[T] {.requiresInit, used.} = object
    v: T
  ProbeObj {.used.} = ref object
    x: int

func probeMake[T](_: typedesc[ProbeBox[T]]; v: T): ProbeBox[T] {.used.} =
  ProbeBox[T](v: v)

let probeG {.used.}: ProbeObj = ProbeObj(x: 1)

const
  probe25858 = compiles(
    block:
      proc probeF(): ProbeBox[int] =
        probeMake(typeof(result), 1)
      discard probeF())
    # nim-lang/Nim#25858: `typeof(result)` in a `requiresInit` return type is
    # no use-before-init.
  probe26093 = compiles(
    block:
      proc probeConsumer(): int {.gcsafe.} =
        {.cast(gcsafe).}:
          let a = probeG.x
          {.cast(gcsafe).}:
            discard probeG.x
          let c = probeG.x
          a + c
      discard probeConsumer())
    # nim-lang/Nim#26093: leaving a nested `cast(gcsafe)` block keeps the
    # enclosing block's cast for the statements after it.

const buildProvenance*: BuildProvenance = block:
  var p: BuildProvenance
  p.ccFamily =
    when defined(vcc): ccVcc
    elif defined(clang): ccClang
    elif defined(gcc): ccGcc
    else: ccOther
  p.nimVersion = NimVersion
  var patches: seq[string]
  if probe25858: patches.add "backport-25858"
  if probe26093: patches.add "backport-26093"
  p.patchset = patches.join(",")
  p.stockNim = patches.len < 2
  # nelli cannot read the C flags a build passes; it assumes none of these is
  # present, except the one it produces itself.
  p.assumedAbsent = {cfFwrapv, cfTrapv, cfFastMath, cfSanitize, cfFpContract,
                     cfNoStrictAliasing}
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

proc readHost*(z3Full: string): HostSemantics =
  ## The host this process runs on: the Z3 the caller loaded (`z3FullVersion()`;
  ## `symex.nim` and `runtime.nim` import `z3`, this module does not) and
  ## std/re's libpcre, asked the way `pcre_engine` asks it.
  result.z3Full = z3Full
  result.z3 = z3VersionOf(z3Full)
  result.pcre = pcreHostEngine()
  result.pcreVersion = pcreVersion().split(' ')[0]
  result.pcreJit = pcreRunsJit()

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
    bfNim = "nim"

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
  ##  * `provenance.stockNim`: an unpatched Nim is unprojectable (K5b): the
  ##    cells were decided on the patched toolchain (`nimVersion`, `patchset`
  ##    are reported; `assumedAbsent` is not projected).
  if b.ptrBits != 64 or b.endian != enLittle or b.cpu != cpuAmd64:
    return none(BuildRow)
  if b.caseObjects != cmStrict: return none(BuildRow)
  if p.stockNim: return none(BuildRow)
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
  if p.stockNim:
    return some(BuildRefusal(field: bfNim,
      reason: "an unpatched Nim " & p.nimVersion & " is an unverified " &
              "toolchain: the cells were decided on the patched 2.2.10 " &
              "(ghcr.io/coreyleavitt/nim)"))
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
  ## Wired once, at the first run (`hostAdmission`, runtime.nim); a refusal is
  ## an `sxUnknown` with `feHostUnadmitted`, never a raise. A libpcre that is
  ## not in `verifiedLibs` is NOT refused here: it declines each regex call by
  ## itself (`psUnverifiedLib`), and refusing the host would end runs that
  ## never touch a regex (see `rowOf`).
  if h.z3 == z3Other:
    var shown = h.z3Full
    if shown.endsWith(".0") and shown.count('.') == 3:
      shown.setLen(shown.len - 2)
    return some(BuildRefusal(field: bfZ3,
      reason: "z3 " & shown & " is not a verified Z3 (4.13.4, 5.1)"))
  if rowOf(b, h, p).isNone:
    return some(BuildRefusal(field: bfRow,
      reason: "no verified build row covers this build under z3=" & $h.z3))
  none(BuildRefusal)

func refusalMessage*(a: BuildRefusal): string =
  ## The compile-time error text for a refused build.
  "nelli/symex: this build is refused: " & a.reason & " [field: " & $a.field & "]"

func assumedAbsentNote*(p: BuildProvenance = buildProvenance): string =
  ## RFC-0016 K10c (section 8.1, C flags). The C flags nelli cannot see and
  ## assumes the build does not pass, as one sentence for a finding or a
  ## message that states a verdict about the C the build compiles. Empty when
  ## nothing is assumed absent.
  var names: seq[string]
  for f in p.assumedAbsent: names.add $f
  if names.len == 0: return ""
  "assumes the C build passes none of " & names.join(", ") &
    " (nelli cannot read --passC)"

# ---------------------------------------------------------------------------
# RFC-0016 K5b: the build axis's own cells (section 8.1, 8.2).
# ---------------------------------------------------------------------------

type BuildSite* = enum
  bsBuild                 ## the build as `symexFind` meets it

const buildCells* = axisTable[BuildSite, bool](axBuild, [
  ## The cells of the build axis that are not a PCRE library (`pcreLibs`) or a
  ## `BuildRow`: the build configurations the profile REFUSES (a `never` cell
  ## is a configuration that stays refused; a `declined` one is refused until
  ## a CI leg runs it), the cross-build cfg suites that pin `rowOf`'s neutrality
  ## claims, and the documented hazards that no run can fix. The key is the
  ## text a pin record names (`pinRefused`'s `mm=refc` is one).
  ##
  # Refusals.
  ("mm=refc", refused[BuildSite, bool](none(SymexErrorKind),
    "refc is not a verified build (D-0016-7): its heap and destructor timing " &
    "are unpinned and nim-z3's `=destroy` hooks do not compile under it",
    iNever, nrByDesign)),
  ("ptrBits=32", refused[BuildSite, bool](none(SymexErrorKind),
    "Nim's `int` is hard-coded as a 64-bit vector (W-14); no 32-bit CI leg",
    iNever, nrPlatform)),
  ("endian=big", refused[BuildSite, bool](none(SymexErrorKind),
    "byte layout is read as little-endian; no big-endian CI leg",
    iNever, nrPlatform)),
  ("cpu=arm64", refused[BuildSite, bool](none(SymexErrorKind),
    "refused until a CI leg runs the suite on arm64 (a compile-only leg " &
    "cannot satisfy section 12)")),
  ("os=macosx", refused[BuildSite, bool](none(SymexErrorKind),
    "refused until a CI leg runs the suite on macOS (a compile-only leg " &
    "cannot satisfy section 12)")),
  ("fwrapv/vcc", refused[BuildSite, bool](none(SymexErrorKind),
    "-d:nelliFwrapv under vcc: cl.exe has no -fwrapv, so the wrap would be " &
    "claimed and not given", iNever, nrPlatform)),
  ("nim/unpatched", refused[BuildSite, bool](none(SymexErrorKind),
    "an unpatched Nim 2.2.10 is an unverified toolchain: the cells were " &
    "decided on the patched one (the macro VM the parser runs in included)")),
  ("z3/unverified", refused[BuildSite, bool](none(SymexErrorKind),
    "a Z3 other than 4.13.4 and 5.1 is refused at the first run " &
    "(`admitHost`), as `sxUnknown` with `feHostUnadmitted`")),
  ("pcre/unverified", refused[BuildSite, bool](none(SymexErrorKind),
    "a libpcre not in `pcreLibs` declines each regex call (`psUnverifiedLib`) " &
    "and does not refuse the build: runs that touch no regex are unaffected")),
  ("profile/unprojectable", refused[BuildSite, bool](none(SymexErrorKind),
    "a profile no `BuildRow` covers (an unpinned memory model, `quirky` " &
    "exceptions, `nimOldCaseObjects`, a C compiler with no leg) is refused " &
    "by name, never borrowed onto a row")),
  # Hazards that stay by design or by platform; each has a native check.
  ("finally/returnOnRaise", refused[BuildSite, bool](none(SymexErrorKind),
    "STY-01 (A-10): `return` in a `finally` on a raised path re-raises on the " &
    "c backend and returns on cpp; the two backends disagree natively",
    iNever, nrPlatform)),
  ("z3/deepUnsat", refused[BuildSite, bool](none(SymexErrorKind),
    "STY-08 (HRV-63): whether a deep term is decided or cut off depends on " &
    "the Z3 version's own recursion; the 4.13.4 and 5.1 rows are separate " &
    "legs, and no SUT-level pin can force it", iNever, nrUnobservable)),
  ("setting/isLoose", refused[BuildSite, bool](none(SymexErrorKind),
    "AUD-01: `isLoose` leaves an `isIntOffset` parameter unstamped; opt-in " &
    "unsound by ADR-0001 and carrying its banner", iNever, nrByDesign)),
  ("sizeof/host", refused[BuildSite, bool](none(SymexErrorKind),
    "W-52: `sizeof` and shift widths are facts of the host the walker " &
    "reads from its own build, not modelled per target",
    iNever, nrPlatform)),
  # C flags `querySetting` cannot see (K10c): nelli assumes them absent
  # (`BuildProvenance.assumedAbsent`), so no SUT-level pin can observe them.
  ("cflags/sanitize", refused[BuildSite, bool](none(SymexErrorKind),
    "-fsanitize=* is invisible to `querySetting`; a UBSan build changes only " &
    "what C does when an undefined operation runs (it faults), never the " &
    "defined ones, so the table is checked under it (K10c). mingw gcc and " &
    "MSVC have no UBSan runtime", iNever, nrUnobservable)),
  ("cflags/fpContract", refused[BuildSite, bool](none(SymexErrorKind),
    "-ffp-contract=fast is gcc's default but only fuses `a * b + c` on a " &
    "target with a fused multiply-add: baseline x86-64 has none, so the " &
    "Linux row computes two roundings, as the walker does; `-mfma` would " &
    "differ and is not claimed (K10c pins the row against " &
    "-ffp-contract=off)", iNever, nrUnobservable)),
  # The cross-build cfg suites (W-58): `rowOf` calls each of these neutral,
  # and each is pinned by exact verdicts under that configuration.
  ("mm=arc", modelled[BuildSite, bool](true, {bsBuild},
    "arc agrees with orc except for the cycle collector (S8cs)")),
  ("mm=atomicArc", modelled[BuildSite, bool](true, {bsBuild},
    "atomicArc agrees with arc; it differs in reference-count atomicity only")),
  ("useMalloc", modelled[BuildSite, bool](true, {bsBuild},
    "-d:useMalloc swaps the allocator, not the value semantics")),
  ("exceptions/setjmp", modelled[BuildSite, bool](true, {bsBuild},
    "setjmp exceptions: c backend, Linux only (the cpp backend cannot build " &
    "them; the Windows walk crashes entering the fiber, INT-12)")),
  ("release", modelled[BuildSite, bool](true, {bsBuild},
    "-d:release acts only through `checks`, which it leaves on")),
  ("fwrapv", modelled[BuildSite, bool](true, {bsBuild},
    "-d:nelliFwrapv with checks on is the default build's verdicts")),
  ("rangeChecks=off", modelled[BuildSite, bool](true, {bsBuild},
    "--rangeChecks:off compiles the plain C cast: signed narrowing and " &
    "`chr` truncate, a `range` or enum conversion keeps its value, and an " &
    "array indexed by its own out-of-range type is an unchecked access, " &
    "halted as undefined (`ubArrayOutOfBounds`; PRC-07)")),
  ("boundChecks=off", modelled[BuildSite, bool](true, {bsBuild},
    "--boundChecks:off compiles `s[i]` and `a[i]` of a seq, string, " &
    "openArray or array as a plain C subscript: an index outside the " &
    "container is undefined, halted (`ubArrayOutOfBounds`), where a checked " &
    "build raises `IndexDefect`; the in-bounds side is exact (PRC-07)")),
  ("objChecks=off", modelled[BuildSite, bool](true, {bsBuild},
    "--objChecks:off compiles `Derived(b)` of a `ref` with no " &
    "`isObjDisplayCheck`: a conversion to a type the object is not succeeds " &
    "and is type confusion, undefined, halted (`ubInvalidObjConversion`), " &
    "where a checked build raises `ObjectConversionDefect`; the subtype " &
    "side is exact (PRC-07)")),
  ("fieldChecks=off", modelled[BuildSite, bool](true, {bsBuild},
    "--fieldChecks:off compiles a variant field access as a plain union " &
    "member access: outside its branch it is undefined on the cpp backend " &
    "(`ubInactiveVariantField`) and the overlapping bytes on the c backend, " &
    "exact where the active arm's int/char/bool fields cover them and " &
    "declined path-locally otherwise (`fieldChecksOffLayout`); the in-branch side is " &
    "exact (PRC-07)"))])
