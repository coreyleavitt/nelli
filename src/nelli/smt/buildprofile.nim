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
## the profile. That profile fails closed: it disagrees with the build's real
## checks, so the walker declines (`feCheckOption`) rather than answer for a
## program it does not model. Import nelli before the push.
import std/[strutils, algorithm]

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

  BuildSemantics* = object
    ## What the build compiles in that changes what the native `fn` does.
    checks*: set[CheckOption]   ## the command line's checks, `nilChecks` aside
    panics*: bool               ## `--panics:on`
    mm*: MemModel
    exceptions*: ExcMode
    backend*: Backend
    danger*, release*: bool     ## code may branch on them with `when defined`
    threads*, stackTrace*, lineTrace*: bool

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
                       threads, stackTrace, lineTrace: bool): string =
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
    (if lineTrace: "+lt" else: "")

func buildSegment*(b: BuildSemantics = buildSemantics): string =
  ## The cache key's `|bf=` segment for build `b` (this build by default).
  renderBuildFlags(checkNames(b.checks), b.danger, b.release, $b.mm,
                   $b.backend, $b.exceptions, b.threads, b.stackTrace,
                   b.lineTrace)

type Admission* = tuple[ok: bool, field, reason: string]

func admitBuild*(b: BuildSemantics = buildSemantics): Admission =
  ## RFC-0016 W1-c1b (section 8.3, Refusals). Whether `nelli/symex` runs on
  ## build `b` at all. The only Wave-1 refusal is the memory model: D-0016-7
  ## refuses `--mm:refc` by name (its heap and destructor timing are not a
  ## verified build, and nim-z3's `=destroy` hooks do not compile under it).
  ## Pure and compile-time evaluable; `symex.nim` calls it once, before it
  ## imports `z3`, since under refc the `z3` import is the first thing to fail.
  if b.mm == mmRefc:
    return (false, "mm",
      "mm=refc is not a verified build (D-0016-7); use --mm:orc or --mm:arc")
  (true, "", "")

func refusalMessage*(a: Admission): string =
  ## The compile-time error text for a refused build.
  "nelli/symex: this build is refused: " & a.reason & " [field: " & a.field & "]"
