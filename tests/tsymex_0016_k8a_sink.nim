## RFC-0016 K8a-sink (§10): the triage sink. A planted disagreement reduces to
## a smaller program that still disagrees and is keyed to its cell; several
## seeds hitting one cell file once and comment after (scripts/k8a-sink.sh in
## --dry-run, the only mode a test runs: no `gh` is ever called); a findings
## file with no disagreements files nothing; the workflow gives `issues: write`
## to the sink job alone and honours `file_issues=false`.
import std/[unittest, os, osproc, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8a_sink

let tmp = (getTempDir() / ("k8a_sink_" & $getCurrentProcessId())).replace("\\", "/")
createDir(tmp)
putEnv("NELLI_PIN_DIR", tmp)

# The planted program: `a mod 1 != 0` over uint, unsat; the plant flips it.
const planted = Case(
  prog: Prog(id: 0, shape: shDivLit, ty: "uint64", op: "mod",
             lit: Lit(kind: lkNum, n: 1), cmp: "!=",
             k: Lit(kind: lkNum, n: 7)),
  tw: twDead)

# REAL engine, planted lie: every candidate of one reduction round compiles
# (type changes, narrowed domains) and runs; the plant makes each disagree.
const roundCs = roundCases(candidates(planted))
genCases(roundCs, true, "sink")

const stub = "#!/bin/sh\necho \"$@\" >> \"" & "GHLOG" & "\"\nexit 1\n"

proc bashExe(): string =
  ## The bash that runs scripts/*.sh. On Windows a bare `bash` resolves to
  ## System32's WSL launcher (which only prints "no installed distributions"),
  ## so Git for Windows' own bash is taken from beside `git`, and a missing one
  ## is a loud failure, never a skip.
  when defined(windows):
    let g = findExe("git")
    if g.len > 0:
      let b = g.parentDir.parentDir / "bin" / "bash.exe"
      if fileExists(b): return b
    let pf = getEnv("ProgramFiles", r"C:\Program Files") / "Git" / "bin" / "bash.exe"
    doAssert fileExists(pf), "Git for Windows' bash.exe not found"
    pf
  else:
    "bash"

var runSeq = 0

proc runBash(args: seq[string]; stdinText = ""): (string, int) =
  ## bash with `args`, stderr merged into the output. No shell sits between us
  ## and bash, so quoting means the same on every platform. Stdin and output go
  ## through files, not pipes: reading a Git Bash child's stdout pipe on Windows
  ## came back truncated after its first line.
  inc runSeq
  let inF = tmp / ("in" & $runSeq & ".txt")
  let outF = tmp / ("out" & $runSeq & ".txt")
  writeFile(inF, stdinText)
  let p = startProcess(bashExe(),
    args = @["-c", "o=\"$1\"; i=\"$2\"; shift 2; bash \"$@\" > \"$o\" 2>&1 < \"$i\"",
             "bash", outF, inF] & args,
    options = {poStdErrToStdOut, poUsePath})
  let rc = p.waitForExit()
  p.close()
  (readFile(outF), rc)

proc sink(args: string; ghlog: string): string =
  ## Runs scripts/k8a-sink.sh with a `gh` on PATH that records every call and
  ## fails: a dry run must never reach it.
  let bin = tmp / "bin"
  createDir(bin)
  writeFile(bin / "gh", stub.replace("GHLOG", ghlog))
  setFilePermissions(bin / "gh", {fpUserExec, fpUserRead, fpUserWrite})
  if not getEnv("PATH").startsWith(bin):
    putEnv("PATH", bin & $PathSep & getEnv("PATH"))
  let (o, rc) = runBash(@["scripts/k8a-sink.sh", "file"] &
                        args.splitWhitespace & @["--dry-run"])
  check rc == 0
  o

suite "K8a-sink":
  test "RED: a planted disagreement reduces to a smaller program that still disagrees":
    # a fake oracle: the planted bug is "mod": every candidate keeping `mod`
    # still disagrees, a candidate that changed the op does not
    var calls = 0
    let oracle = proc (cs: seq[Case]): seq[string] =
      inc calls
      for c in cs:
        result.add (if c.prog.op == "mod": "walker says sxSat ... does not hit natively" else: "")
    let r = reduce(planted, "start", oracle)
    check r.steps > 0
    check measure(r.c) < measure(planted)
    check r.c.tw == twNone                 # twin dropped
    check r.c.prog.ty == "uint8"           # type simplified
    check r.c.prog.op == "mod"             # what the bug needs survives
    check r.c.prog.cmp == "=="             # predicate simplified
    check r.c.prog.k == Lit(kind: lkNum, n: 0)
    check domainList(r.c.prog).len == 1    # domain narrowed to one value
    check render(r.c.prog).len < render(planted.prog).len or
          domainList(r.c.prog).len < domainList(planted.prog).len
    check calls >= r.steps
    # the reduced case round-trips through the text the rounds pass along
    check decodeCase(encodeCase(r.c)) == r.c
    check decodeCase(encodeCase(planted)) == planted

  test "reduction stops where the disagreement stops reproducing":
    let never = proc (cs: seq[Case]): seq[string] = newSeq[string](cs.len)
    let r = reduce(planted, "start", never)
    check r.c == planted
    check r.steps == 0

  test "every reduction candidate is strictly smaller":
    for c in candidates(planted): check measure(c) < measure(planted)
    check candidates(Case(prog: planted.prog, tw: twNone)).len > 0

  test "RED: the real engine disagrees on every planted candidate, keyed to the cell":
    let outs = runBatch_sink()
    check outs.len == roundCs.len
    var disagreeing = 0
    for i, c in candidates(planted):
      var p = c.prog
      p.id = i
      let mine = outs.filterIt(it.progId == i)
      let fs = findings(@[p], mine, 99)
      if fs.len > 0:
        inc disagreeing
        let pair = verdictPair(fs[0])
        check pair.startsWith("sx")
        check pair.endsWith("|native-miss") or pair.endsWith("|native-hit")
        check dedupKey(p.shape, "linux-c", pair) ==
          "construct:k8a-gen/DivLit|linux-c|" & pair
    check disagreeing > 0

  test "keying: cell, row and verdict pair; the marker carries the key":
    check cellOf(shDivLit) == "construct:k8a-gen/DivLit"
    check cellOf(shExcept) == "construct:k8a-gen/Except"
    check verdictPair("x walker says sxUnsat for t but (1,1) hits it natively") ==
      "sxUnsat|native-hit"
    check verdictPair("metamorphic: original sxSat vs twin sxUnsat\n--- original") ==
      "meta:sxSat|sxUnsat"
    check dedupKey(shNeg, "linux-cpp", "sxSat|native-miss") !=
      dedupKey(shNeg, "linux-c", "sxSat|native-miss")
    check dedupKey(shNeg, "linux-c", "sxSat|native-miss") !=
      dedupKey(shOvf, "linux-c", "sxSat|native-miss")
    check keyMarker("a|b").startsWith("<!--") and keyMarker("a|b").endsWith("-->")

  test "the shell twin of verdictPair agrees on every finding shape":
    for f in ["x walker says sxSat for t but the witness does not hit natively: h",
              "walker says sxUnsat for t but (1,1) hits it natively",
              "walker says sxRaised(OverflowDefect) but the witness natively did",
              "metamorphic: original sxSat vs twin sxUnsat\n--- original\nproc",
              "annotationViolations: 2", "something else"]:
      let p = tmp / "pairin.txt"
      writeFile(p, f)
      let (o, rc) = runBash(@["scripts/k8a-sink.sh", "pair"], readFile(p))
      check rc == 0
      check o.strip() == verdictPair(f)

  let finding = "FINDING seed=SEED prog=P variant=orig shape=shDivLit\n" &
    "native differential: pinExact construct:k8a-gen/DivLit: walker says sxSat " &
    "for hit but the witness does not hit natively: hits=[] raised=-\n" &
    "proc gx_P_orig(a, b: uint) =\n  let r = (a mod uint(1))\n" &
    "  if r != uint(0): symexTarget(\"hit\")\n"

  test "two seeds hitting one cell: one filing, then a comment (dry run)":
    let ghlog = tmp / "gh1.log"
    let ex = tmp / "existing1.tsv"
    writeFile(tmp / "s1.txt", finding.replace("SEED", "1").replace("P", "0") &
                              finding.replace("SEED", "1").replace("P", "5"))
    writeFile(tmp / "s2.txt", finding.replace("SEED", "2").replace("P", "3"))
    let o1 = sink("--findings " & tmp / "s1.txt" & " --row linux-c --existing " &
                  ex & " --no-reduce", ghlog)
    check o1.count("DRYRUN gh issue create") == 1     # two programs, one key
    check o1.count("DRYRUN gh issue comment") == 0
    check "--label rfc-0016-intake" in o1
    check "<!-- k8a-sink-key: construct:k8a-gen/DivLit|linux-c|sxSat|native-miss -->" in o1
    check "seed=1 prog=0" in o1 and "seed=1 prog=5" in o1
    check "-d:k8aSeed=1 -d:k8aCount=1" in o1          # the repro command
    check "proc gx_0_orig" in o1                       # the program
    let o2 = sink("--findings " & tmp / "s2.txt" & " --row linux-c --existing " &
                  ex & " --no-reduce", ghlog)
    check o2.count("DRYRUN gh issue create") == 0
    check o2.count("DRYRUN gh issue comment 9000") == 1
    check "seed=2 prog=3" in o2
    # the same cell on another build row is a different issue
    let o3 = sink("--findings " & tmp / "s2.txt" & " --row linux-cpp --existing " &
                  ex & " --no-reduce", ghlog)
    check o3.count("DRYRUN gh issue create") == 1
    check "|linux-cpp|" in o3
    check not fileExists(ghlog)                        # gh was never called

  test "a findings file with no disagreements files nothing":
    let ghlog = tmp / "gh2.log"
    writeFile(tmp / "empty.txt", "")
    let o = sink("--findings " & tmp / "empty.txt" & " --row linux-c", ghlog)
    check "DRYRUN" notin o
    check "nothing to file" in o
    check not fileExists(ghlog)
    # an absent file (the differential found nothing and wrote none) too
    let o2 = sink("--findings " & tmp / "absent.txt" & " --row linux-c", ghlog)
    check "DRYRUN" notin o2
    check not fileExists(ghlog)

  test "the shell self-test passes":
    let (o, rc) = runBash(@["scripts/k8a-sink.sh", "--self-test"])
    check rc == 0
    check "self-test: ok" in o

  test "workflow: issues:write on the sink job alone, gated by file_issues":
    var y = ""
    for l in readFile(".github/workflows/k8a-differential.yaml").splitLines:
      if not l.strip.startsWith("#"): y.add l & "\n"   # comments may name it
    check y.count("issues: write") == 1
    let sinkAt = y.find("\n  sink:")
    check sinkAt > 0
    check y.find("issues: write") > sinkAt
    check y.find("needs.differential.outputs.findings == 'true'") > sinkAt
    check y.find("inputs.file_issues != 'false'") > sinkAt
    check "file_issues:" in y[0 ..< sinkAt]
    check "scripts/k8a-sink.sh" in y[sinkAt .. ^1]
    # the top-level permissions stay read-only
    check y.find("permissions:\n  contents: read\n") in 0 .. sinkAt
    removeDir(tmp)
