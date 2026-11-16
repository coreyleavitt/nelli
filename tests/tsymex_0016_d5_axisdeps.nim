## RFC-0016 0.10.0 review D5 -- the axis modules share one key/verb leaf and
## do not lean on each other; `check_options` splits its pure scan from its
## compile-time I/O.
##
## (a) No axis module imports another axis module. The shared machinery (row
##     builders, the magic axis's proof type) is `axis_key`, a leaf. Derived
##     from the source text, so a new lateral import fails here.
## (b) The pure scan (`check_scan`) holds no file, environment or compiler
##     setting access; `check_options` is the adapter that gathers them.
## (c) The pure scan runs on literal inputs: a text and an in-memory source
##     environment, no disk.
import std/[unittest, os, strutils, tables]
import nelli/smt/check_scan
import nelli/smt/buildprofile

const root = currentSourcePath().parentDir() / ".." / "src" / "nelli" / "smt"

const axisModules = ["constructaxes", "pragmaaxes", "readonlyaxes",
                     "typeaxes", "magic_rows", "definedness", "stdlib_rows"]

proc code(path: string): seq[string] =
  ## The non-comment lines of a source file.
  for l in readFile(path).splitLines:
    let t = l.strip
    if t.len > 0 and not t.startsWith("#"): result.add t

proc importedModules(path: string): seq[string] =
  ## The `./name` modules a file imports or exports, however spelled.
  for t in code(path):
    if t.startsWith("import ") or t.startsWith("from ") or
       t.startsWith("export "):
      var s = t
      let hash = s.find('#')
      if hash >= 0: s = s[0 ..< hash]
      for part in s.split({' ', ',', '[', ']'}):
        if part.startsWith("./"): result.add part[2 .. ^1]

suite "D5: axis modules do not import one another":
  test "no lateral import between axis modules":
    for m in axisModules:
      for dep in importedModules(root / m & ".nim"):
        check dep notin axisModules
        if dep in axisModules: echo m, " imports axis module ", dep
  test "the shared leaf imports no axis module":
    for dep in importedModules(root / "axis_key.nim"):
      check dep notin axisModules
  test "every axis module with row builders reads them from the leaf":
    # every axis module (R2-6/L2: the list was 4 of the 7)
    for m in axisModules:
      checkpoint m
      check "axis_key" in importedModules(root / m & ".nim")

suite "D5: the pure scan has no compile-time I/O":
  test "check_scan names none of the I/O procs":
    let src = code(root / "check_scan.nim").join("\n")
    for banned in ["staticRead", "querySetting", "readFile", "getEnv",
                   "existsEnv", "fileExists", "dirExists", "compilesettings",
                   "std/os", "std/[os", ", os,", "[os,",
                   # R2-6/L2: the other compile-time and process I/O doors
                   "slurp", "gorge", "staticExec", "open(", "osproc"]:
      check banned notin src
  test "check_options is the adapter: it imports the pure half":
    check "check_scan" in importedModules(root / "check_options.nim")

# ---- (c) the pure scan on literal inputs --------------------------------------

var memFiles {.compileTime.}: Table[string, string]

proc memExists(p: string): bool = p in memFiles
proc memRead(p: string): string = memFiles[p]
proc memAnchor(p: string): string = p

const memEnv = SourceEnv(exists: memExists, read: memRead, anchor: memAnchor)

static:
  memFiles["mem/pushes.nim"] = "{.push overflowChecks: off.}\n"

const
  plain = scanModuleText("mem/a.nim", "proc f() = discard\n", memEnv)
  pushed = scanModuleText("mem/a.nim",
    "{.push overflowChecks: off.}\nproc f() = discard\n{.pop.}\nproc g() = discard\n",
    memEnv)
  included = scanModuleText("mem/a.nim",
    "include pushes\nproc f() = discard\n", memEnv)
  missing = scanModuleText("mem/a.nim", "include nowhere\n", memEnv)
  unparsable = scanModuleText("mem/a.nim", "proc (((\n", memEnv)
  leaking = importLeak(scanModuleText("mem/a.nim",
    "{.push boundChecks: off.}\nimport foo\n{.pop.}\n", memEnv))

suite "D5: scanModuleText on literal inputs":
  test "no push: no deviation, nothing unknown":
    check deviation(stateAt(plain, "mem/a.nim", 1, 0)) == {}
    check plain.unknownReason == ""
  test "a push moves the state inside it and the pop restores it":
    check coOverflow in deviation(stateAt(pushed, "mem/a.nim", 2, 0))
    check deviation(stateAt(pushed, "mem/a.nim", 4, 0)) == {}
  test "an include is read through the environment":
    check coOverflow in deviation(stateAt(included, "mem/a.nim", 2, 0))
  test "an include the environment cannot give is unknown":
    check missing.unknownReason.len > 0
  test "text that does not parse is unknown":
    check unparsable.unknownReason.startsWith("cannot parse")
  test "an import under a push leaks it":
    check coBound in leaking
