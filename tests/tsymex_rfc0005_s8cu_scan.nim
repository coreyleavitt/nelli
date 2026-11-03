## RFC-0005 S8cu -- the source scan on its own, at compile time.
##
## These rows have no native column because no build of them exists: a file that
## cannot be read, a filter, a parse failure. The forms that do compile have theirs
## in `tsymex_rfc0005_s8cu_forms`. `parseStmt` needs a file that exists to attach line
## info to, so every text here reads as this file.
import std/[unittest, os, strutils, macros]
import nelli/smt/check_options
import nelli/smt/runtime

# As the compiler reports it (`\\` on Windows): the scan reads by this path and
# compares normalised.
const self = currentSourcePath()
const here = self.parentDir

proc devAt(text: string; line: int): set[CheckOption] {.compileTime.} =
  deviation(stateAt(scanModuleText(self, text), self, line, 0))

const missing = scanModule("/s8cu/no/such/file.nim").unknownReason
const filtered = scanModule(here / "s8cu_fix_filtered.nim").unknownReason
const includeMissing =
  scanModuleText(self, "include s8cu_no_such_file\n").unknownReason
const includeOdd =
  scanModuleText(self, "include foo(bar)\n").unknownReason
const includeFiltered =
  scanModuleText(self, "include s8cu_fix_filtered\n").unknownReason
const unparsable = scanModuleText(self, "proc (((\n").unknownReason

const balanced = """
when c:
  {.push fieldChecks: off.}
proc a() = discard
when c:
  {.pop.}
proc b() = discard
"""
const balancedA = devAt(balanced, 3)
const balancedB = devAt(balanced, 6)

const elseBranch = """
when c:
  {.push fieldChecks: off.}
else:
  {.push overflowChecks: off.}
proc a() = discard
{.pop.}
proc b() = discard
"""
const elseA = devAt(elseBranch, 5)
const elseB = devAt(elseBranch, 7)

const nestedWhen = """
when c:
  when true:
    {.push rangeChecks: off.}
proc a() = discard
"""
const nestedA = devAt(nestedWhen, 4)

proc fiveConds(): string {.compileTime.} =
  for i in 1 .. 5: result.add "when c" & $i & ":\n  {.push fieldChecks: off.}\n"
  for i in 1 .. 5: result.add "when c" & $i & ":\n  {.pop.}\n"
  result.add "proc a() = discard\n"
const pastLimit = devAt(fiveConds(), 21)

proc fourConds(): string {.compileTime.} =
  for i in 1 .. 4: result.add "when c" & $i & ":\n  {.push fieldChecks: off.}\n"
  for i in 1 .. 4: result.add "when c" & $i & ":\n  {.pop.}\n"
  result.add "proc a() = discard\n"
const atLimit = devAt(fourConds(), 17)

const decided = """
when hostOS == "no such os":
  {.push fieldChecks: off.}
proc a() = discard
when not (hostOS == "no such os"):
  {.push overflowChecks: off.}
proc b() = discard
"""
const decidedA = devAt(decided, 3)
const decidedB = devAt(decided, 6)

const strayPop = devAt("{.pop.}\nproc a() = discard\n", 2)

const notALiteral = devAt("{.push fieldChecks: someConst.}\nproc a() = discard\n{.pop.}\n", 2)

const inRegion = """
{.push fieldChecks: off.}
{.pop.}
template t() =
  proc a() = discard
proc b() = discard
"""
const regionA = devAt(inRegion, 4)
const regionB = devAt(inRegion, 5)

const hiddenText = """
proc before() = discard
template t() =
  {.push fieldChecks: off.}
proc after() = discard
"""
const hiddenA = devAt(hiddenText, 1)
const hiddenB = devAt(hiddenText, 4)

const leaking = importLeak(scanModuleText(self, "{.push overflowChecks: off.}\nimport foo\n{.pop.}\n"))
const leakingFrom = importLeak(scanModuleText(self, "{.push boundChecks: off.}\nfrom a/foo import bar\n{.pop.}\n"))
const notLeaking = importLeak(scanModuleText(self, "import foo\n{.push overflowChecks: off.}\n{.pop.}\n"))

# A routine's own checks, through the entry the parser uses. Nelli's runtime pushes
# `fieldChecks: off` around `ptrAimInto` (S8bw) and is excluded by its path: on
# Windows that path reaches here with `\\`, so this pin fails there if the
# exclusion compares an unnormalised path.
macro checksOf(fn: typed): untyped =
  let impl = (if fn.kind == nnkSym: fn else: fn[0]).getImpl
  let c = routineChecks(impl)
  newLit($c.checks & "|" & c.why)

{.push fieldChecks: off.}
proc userUnderPush(v: int): int = v
{.pop.}
proc userClean(v: int): int = v

const runtimeOwn = checksOf(ptrAimInto)
const userOff = checksOf(userUnderPush)
const userOn = checksOf(userClean)

suite "S8cu scan: a routine's own checks":

  test "nelli's own runtime under its push does not decline":
    check runtimeOwn == "{}|"

  test "a user routine under the same push does; one outside it does not":
    check userOff == "{fieldChecks}|"
    check userOn == "{}|"

suite "S8cu scan: what cannot be read":

  test "a missing file":
    check "cannot read" in missing

  test "a source filter":
    check "source filter" in filtered

  test "an include that cannot be found, or placed, or is filtered":
    check "cannot place" in includeMissing
    check "cannot place" in includeOdd
    check "source filter" in includeFiltered

  test "text that does not parse":
    check "cannot parse" in unparsable

suite "S8cu scan: when":

  test "a push and a pop under one condition balance":
    check balancedA == {coField}
    check balancedB == {}

  test "an else branch: both on the way, each popped after":
    check elseA == {coField, coOverflow}
    check elseB == {}

  test "nested in an undecided condition":
    check nestedA == {coRange}

  test "up to the limit of conditions each is its own reading":
    check atLimit == {}

  test "past it, what is below the pops stays merged: an over-decline, not a miss":
    check pastLimit == {coField}

  test "a decided condition":
    check decidedA == {}
    check decidedB == {coOverflow}

suite "S8cu scan: the rest":

  test "a pop with nothing pushed is harmless":
    check strayPop == {}

  test "a value that is no literal reads as off":
    check notALiteral == {coField}

  test "a template's body is read at its union, what follows it at its place":
    check regionA == {coField}
    check regionB == {}

  test "a pragma in a template applies from its definition on":
    check hiddenA == {}
    check hiddenB == {coField}

  test "an import under a push leaks; one outside it does not":
    check leaking == {coOverflow}
    check leakingFrom == {coBound}
    check notLeaking == {}
