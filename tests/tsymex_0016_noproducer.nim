## RFC-0016 L-M3: the error kinds with no producer are marked as such.
##
## `errorkind.txt` allowlists every `SymexErrorKind` no pin evidences. For 14 of
## them the reason used to say "no pinDecline asserts this kind", which is true
## and misleading: no pin CAN, because nothing under `src/` emits them. W-64
## (K10d) deletes them. This gate derives the set mechanically:
##   * PRODUCERLESS: a kind that appears in no `src/` code outside
##     `errorkind.nim` (its declaration) and the `of <kind>: dc...` arms of
##     `types.nim`'s `classOf` (a total `case`, not a producer);
##   * RETIRED: a kind whose declaration comment in `errorkind.nim` says so
##     (`retired`, `reserved/unused`, `NO LONGER EMITTED`, `NEVER EMITTED`).
## and demands that the two sets are equal, and that `errorkind.txt` carries
## the `[no-producer]` marker on exactly that set. The marker count sits under
## a ceiling in `ceilings.txt` (`no-producer=marked`, checked by
## `tsymex_0016_allowlist_ceilings`), so it only falls.
import std/[unittest, os, strutils, sequtils, sets, tables, algorithm]
import nelli/smt/types
import ./rfc0016_ids

const
  root = currentSourcePath().parentDir() / ".."
  srcDir = root / "src" / "nelli"
  errorkindDecl = srcDir / "smt" / "errorkind.nim"
  allowPath = root / "tests" / "0016-allowlist" / "errorkind.txt"
  marker* = "[no-producer]"

proc codePart(line: string): string =
  ## A source line without its comment (naive: a `#` inside a string literal
  ## is rare enough in these sources to cost only a missed reference).
  let i = line.find('#')
  if i < 0: line else: line[0 ..< i]

proc identsIn(s: string): seq[string] =
  var cur = ""
  for c in s & " ":
    if c in IdentChars: cur.add c
    else:
      if cur.len > 0: result.add cur
      cur = ""

proc retiredKinds*(declText: string; kinds: HashSet[string]): HashSet[string] =
  ## The kinds whose declaration comment marks them retired or unused. A
  ## comment attaches to the last member named on the line that opens it and
  ## runs over the `##` lines that follow.
  let lines = declText.splitLines()
  var i = 0
  while i < lines.len:
    let l = lines[i]
    let h = l.find("##")
    var members: seq[string]
    for w in identsIn(codePart(l)):
      if w in kinds: members.add w
    if h >= 0 and members.len > 0 and l.strip.len > 0 and
       not l.strip.startsWith("##"):
      var text = l[h + 2 .. ^1]
      var j = i + 1
      while j < lines.len and lines[j].strip.startsWith("##"):
        text.add "\n" & lines[j].strip[2 .. ^1]
        inc j
      let t = text.strip
      let low = t.toLowerAscii
      if low.startsWith("retired") or "reserved/unused" in low or
         "no longer emitted" in low or "never emitted" in low:
        result.incl members[^1]
    inc i

proc producerless*(files: seq[(string, string)]; kinds: seq[string]):
    HashSet[string] =
  ## `files` is (path, text). A kind is producerless when no code line outside
  ## its declaration and `classOf` mentions it.
  var used = initHashSet[string]()
  for (path, text) in files:
    if path.endsWith("errorkind.nim"): continue
    let isTypes = path.endsWith("types.nim")
    for raw in text.splitLines():
      let c = codePart(raw)
      if c.len == 0: continue
      let st = c.strip
      if isTypes and st.startsWith("of ") and ": dc" in st: continue
      for w in identsIn(c): used.incl w
  for k in kinds:
    if k notin used: result.incl k

proc markedKinds*(allowText: string): HashSet[string] =
  for a in parseAllow(allowText):
    if marker in a.reason and a.key.startsWith("errorkind:"):
      result.incl a.key["errorkind:".len .. ^1]

proc noProducerProblems*(kinds: seq[string]; retired, none, marked: HashSet[string];
                         allowed: HashSet[string]): seq[string] =
  for k in kinds:
    if k in none and k notin retired:
      result.add k & ": no producer under src/, but errorkind.nim does not " &
                 "mark it retired or reserved"
    if k in retired and k notin none:
      result.add k & ": errorkind.nim marks it retired, but src/ still " &
                 "references it outside the declaration and classOf"
    if k in none and k notin marked:
      result.add k & ": no producer, so its errorkind.txt reason must carry " &
                 marker
    if k in marked and k notin none:
      result.add k & ": carries " & marker & " but has a producer in src/"
    if k in marked and k notin allowed:
      result.add k & ": carries " & marker & " but is not allowlisted"

proc srcFiles(): seq[(string, string)] =
  for p in walkDirRec(srcDir):
    if p.endsWith(".nim"): result.add (p, readFile(p))

proc kindNames(): seq[string] =
  for k in SymexErrorKind: result.add $k

suite "L-M3: producer-less error kinds (synthetic)":
  let kinds = @["feA", "feB", "feC"]
  test "RED: a producer-less kind with no marker fails":
    let p = noProducerProblems(kinds, toHashSet(["feA"]), toHashSet(["feA"]),
                               initHashSet[string](), toHashSet(["feA"]))
    check p.len == 1 and marker in p[0]
  test "RED: a marker on a kind that has a producer fails":
    let p = noProducerProblems(kinds, initHashSet[string](),
                               initHashSet[string](), toHashSet(["feB"]),
                               toHashSet(["feB"]))
    check p.anyIt("has a producer" in it)
  test "RED: producer-less but not marked retired fails, and the converse":
    check noProducerProblems(kinds, initHashSet[string](), toHashSet(["feA"]),
             toHashSet(["feA"]), toHashSet(["feA"])).anyIt("does not mark" in it)
    check noProducerProblems(kinds, toHashSet(["feA"]), initHashSet[string](),
             initHashSet[string](), initHashSet[string]()).anyIt("still references" in it)
  test "consistent sets are clean":
    check noProducerProblems(kinds, toHashSet(["feA"]), toHashSet(["feA"]),
             toHashSet(["feA"]), toHashSet(["feA"])).len == 0
  test "producerless ignores comments, the declaration and classOf arms":
    let f = @[("x/types.nim", "  of feA: dcNoAnswer\n  # feB here\nfeC()\n"),
              ("x/errorkind.nim", "feB\nfeC\n"),
              ("x/y.nim", "let z = feC  # feB\n")]
    check producerless(f, kinds) == toHashSet(["feA", "feB"])
  test "retiredKinds reads the declaration comment":
    let d = "  feA, ## retired R1\n  feB,\n  feC ## Phase 1\n       ## NO LONGER EMITTED\n  feD ## the RETIRED fallback\n"
    check retiredKinds(d, toHashSet(["feA", "feB", "feC", "feD"])) ==
          toHashSet(["feA", "feC"])

suite "L-M3: producer-less error kinds (the tree)":
  test "the producer-less kinds are the retired kinds and carry the marker":
    let kinds = kindNames()
    let none = producerless(srcFiles(), kinds)
    let retired = retiredKinds(readFile(errorkindDecl), kinds.toHashSet)
    let allowText = readFile(allowPath)
    let allowed = parseAllow(allowText).mapIt(it.key).filterIt(
      it.startsWith("errorkind:")).mapIt(it["errorkind:".len .. ^1]).toHashSet
    let marked = markedKinds(allowText)
    let p = noProducerProblems(kinds, retired, none, marked, allowed)
    if p.len > 0: echo p.join("\n")
    check p.len == 0
    check none.len >= 14              # a rule that finds nothing is broken
