## RFC-0005 S8bt (item 2) -- the concrete reference of PCRE 8.37's JIT
## (`buildNfa(.., peJit837)`: `pcre_jit.nim`'s start-of-match scan, a SKIP
## landing without the CRLF start skip, a `(*SKIP:NAME)` with no mark
## ignored in place) against the JIT itself, on the unanchored entries:
## `find` and `findBounds`' `last` at every start offset, and `replace`.
##
## The oracle is PCRE 8.37's JIT (the Windows legs' library). Where std/re
## loads it, the test compares against std/re directly. Where std/re loads
## a verified interpreter build (8.45 on the Linux image, identical to
## 8.37's interpreter on this corpus), the expected JIT result is std/re's
## with the recorded JIT-vs-interpreter delta applied
## (`s8bt_harness/jit837-delta.txt`, from `jit_oracle.nim` run against
## both 8.37 builds).
import std/[unittest, strutils, re, times, tables]
import pcre
import nelli/smt/[pcre_syntax, pcre_select, pcre_jit, pcre_code, pcre_engine]
import ./s8bt_harness/jit_corpus

const deltaText = staticRead("s8bt_harness/jit837-delta.txt")

type Delta = object
  cells: Table[(string, int), (int, int)]
  repl: Table[string, string]

proc loadDelta(): (seq[string], Table[string, Delta]) =
  var cur = ""
  for line in deltaText.splitLines():
    if line.len == 0 or line[0] == '#' or line.startsWith("S\t"): continue
    let f = line.split('\t')
    case f[0]
    of "P":
      cur = f[1].unescape()
      result[0].add cur
      result[1][cur] = Delta()
    of "C":
      result[1][cur].cells[(f[1].unescape(), parseInt(f[2]))] =
        (parseInt(f[3]), parseInt(f[4]))
    of "R":
      result[1][cur].repl[f[1].unescape()] = f[2].unescape()
    else: doAssert false, line

let (deltaPats, deltas) = loadDelta()

proc jitEngine(): bool =
  var v: cint
  discard pcre.config(pcre.CONFIG_JIT, addr v)
  v == 1

let liveJit837 = jitEngine() and pcreVersion() == "8.37 2015-04-28"

type Tally = object
  patterns, calls, declined: int
  bad: seq[string]

proc check1(p: string; subjects: seq[string]; withReplace: bool;
            t: var Tally) =
  let pr = parsePcre(p)
  doAssert pr.status == psOk, p
  let n = buildNfa(pr, peJit837)
  if not n.ok:
    inc t.declined
    t.bad.add escape(p) & " declined: " & n.why
    return
  let rx = re(p)
  inc t.patterns
  let d = deltas.getOrDefault(p)
  for s in subjects:
    for st in 0 .. s.len:
      inc t.calls
      var want = (find(s, rx, st), findBounds(s, rx, st).last)
      if not liveJit837 and (s, st) in d.cells: want = d.cells[(s, st)]
      let (rc, a, b) = pcreExec(n, s, st, false)
      let got = (if rc == 1: (a, b - 1) elif rc == -1: (-1, 0) else: (rc, 0))
      if got != want:
        t.bad.add escape(p) & " find/last(" & escape(s) & ", " & $st &
                  ") = " & $got & ", JIT: " & $want
    if withReplace:
      var want = replace(s, rx, "-")
      if not liveJit837 and s in d.repl: want = d.repl[s]
      let got = pcreReplace(n, s, "-")
      if got != want:
        t.bad.add escape(p) & " replace(" & escape(s) & ") = " & escape(got) &
                  ", JIT: " & escape(want)

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

suite "S8bt: PCRE 8.37's JIT, concretely":

  test "the oracle covers the corpus":
    check deltaPats == jitCorpus() & jitLongCorpus()
    echo "  libpcre ", pcreVersion(), (if jitEngine(): " JIT" else: ""),
         (if liveJit837: ": live oracle" else: ": recorded delta")

  test "short subjects (find, last, replace)":
    var t: Tally
    let subjects = words(shortAlpha, shortLen)
    for p in jitCorpus(): check1(p, subjects, true, t)
    echo "  ", t.patterns, " patterns, ", t.calls, " calls, ", t.declined,
         " declined, ", t.bad.len, " differ, ", lap()
    checkpoint t.bad[0 ..< min(t.bad.len, 30)].join("\n")
    check t.bad.len == 0
    check t.patterns >= 1100

  test "long prefixes, subjects up to length 5 (find, last)":
    var t: Tally
    let subjects = words(longAlpha, longLen)
    for p in jitLongCorpus(): check1(p, subjects, false, t)
    echo "  ", t.patterns, " patterns, ", t.calls, " calls, ", t.declined,
         " declined, ", t.bad.len, " differ, ", lap()
    checkpoint t.bad[0 ..< min(t.bad.len, 30)].join("\n")
    check t.bad.len == 0
    check t.patterns >= 48

suite "S8bt: the JIT's prefix scan":

  test "scan_prefix's choice on known patterns":
    proc scanOf(p: string): JitScan =
      let pr = parsePcre(p)
      jitScan(compileCode(pr), pr.utf)
    # Two known positions, no range: `fast_forward_first_n_chars` with
    # offsets 0 and 1.
    let a = scanOf(r"(*ANY)\sa")
    check a.on and a.max == 2 and a.rangeRight == -1 and a.offs == @[1]
    # Three known positions: the range.
    let b = scanOf("abab")
    check b.on and b.max == 4 and b.rangeRight == 3 and b.rangeLen == 4
    # One position: the first-character scan instead.
    check not scanOf("a").on
    check not scanOf("a*b").on
