## N27 (round-6 fix round 2) — permanent regression audit closing the
## placeholder-read-totality CLASS, not just the one `lowerHofCall` instance.
## Sibling to `tsymex_phase15_N2_kindgate_audit.nim` /
## `tsymex_phase15_A2a_chokepoint_audit.nim` (same TOT-1 institutionalization
## rationale, same house scan-and-marker technique) rather than an extension
## of either: this audits placeholder-seq FIELD READS, a different
## vocabulary from both.
##
## ----------------------------------------------------------------------------
## Why a permanent test, not a one-time grep (same TOT-1 rationale N2/A2a cite)
## ----------------------------------------------------------------------------
## N27's own root cause (see `canonicalize.nim`'s `symexWalkerVersion` doc
## comment, 96->97) was exactly this failure mode: `lowerHofCall` read
## `.seqLen` with no `isUnsupportedFieldPlaceholder` check, five call sites
## after the R1 chokepoint was introduced specifically to make that
## structurally impossible. A slice-close grep proves the CURRENT inventory
## is complete once; it catches no future regression -- nothing stops a
## later edit from adding a sixth unguarded reader. This test makes that
## impossible to do silently: every future compile of the test suite
## re-scans `runtime.nim`/`runtime_strings.nim` for a bare read of
## `.seqLen`, `.seqDataRaw`, or `.isUnsupportedFieldPlaceholder`.
##
## ----------------------------------------------------------------------------
## What counts as "bare" and how it is detected
## ----------------------------------------------------------------------------
## A READ is `recv.seqLen` / `recv.seqDataRaw` / `recv.isUnsupportedField-
## Placeholder` -- a `.` immediately followed by one of the three field
## names at a word boundary (so `.seqLenXyz` or `.notSeqLen` never match; see
## `fieldNameAt`, the same separator-aware word-match idiom
## `routineVocabWordLenAt` uses in the N2 audit). Nim object-CONSTRUCTOR
## keyword args (`SymVal(seqLen: x, ...)`) have no leading `.` before the
## field name, so a WRITE/construction site never matches this scan by
## construction -- no separate allowlist category is needed for them (the
## RFC's own exclusion (ii), "allocation/construction sites", falls out of
## the pattern rather than needing to be hand-maintained).
##
## A matched line is EXEMPT (no violation) when EITHER:
##   - it is a comment line (trimmed text starts with `#`) -- prose
##     narrating these field names (there is plenty, in backticks) is not a
##     read and must never trip the scanner (same `isCommentLine` rule N2/
##     A2a use); or
##   - the SAME physical line carries the marker comment `# [placeholder-
##     audited]`, added at every legitimately-guarded existing site by the
##     N27 slice (`git log`/`git blame` on runtime.nim's `[placeholder-
##     audited]` occurrences is the audit trail for WHY each one is safe --
##     each site was individually reviewed and is one of: (a) reached only
##     after a same-proc `isUnsupportedFieldPlaceholder` check already
##     declined/returned on the placeholder branch, (b) a receiver whose
##     element type structurally can never be placeholder-flagged
##     (`isBackedSeqElemTy`-backed, e.g. `svSeq[string]`/`svSeq[ref T]`), (c)
##     a cache-key hash (`symValHash`) that never influences a verdict, or
##     (d) the R1 chokepoint's own flag-check performing the guard itself).
## This is deliberately the same "marker-driven, not context-free" design
## A2a's header discusses: `runtime.nim` legitimately reads these three
## fields in dozens of places (every `svSeq`-consuming arm needs to, once
## it has verified the flag) -- a context-free ban would be both unable to
## distinguish a guarded read from an unguarded one and unreadable by
## inspection. The marker makes each guarantee a one-line, human-reviewed,
## committed fact instead of an unstated invariant a future editor cannot
## see.
##
## ----------------------------------------------------------------------------
## `staticRead` vs `readFile` (toolchain note)
## ----------------------------------------------------------------------------
## `tsymex_phase15_N2_kindgate_audit.nim` hit an MSVC C2026 ("string too
## big") compile failure on this host when its `staticRead` corpus grew large
## enough to embed as a single C string literal. `runtime.nim` alone is
## ~565KB (vs. `dsl_parser.nim`'s ~472KB, which N2/A2a's `staticRead` corpus
## already carries without incident) -- large enough that embedding it as a
## THIRD compile-time string constant risks the same failure. This test
## sidesteps the risk entirely by reading both scanned files at TEST RUNTIME
## (`readFile`) instead of compile time (`staticRead`): no giant C string
## literal is ever generated. The path is still resolved at COMPILE time
## (`currentSourcePath`, pure string manipulation -- no file content is
## embedded) so the scan does not depend on the test binary's working
## directory when it runs.
##
## ----------------------------------------------------------------------------
## N27 site inventory (70 marked sites: 67 in runtime.nim, 3 in
## runtime_strings.nim)
## ----------------------------------------------------------------------------
## retBindEq svSeq arm (1); iekSeqLen (2); iekSeqSlice (4); iekSeqAdd (4);
## extractSeqElements (7); extractFromSymVal svSeq arm (2);
## renderContainerElemsIntoSnapshot svSeq arm (3); symValHash svSeq arm (1);
## isIndex svSeq arm (11); seqElemAt (8); concreteSeqLen (1); lowerHofCall's
## new N27 guard + its two placeholder-branch reads + the axiom-map path's
## two reads (5) in runtime.nim; joinStrSeq (2) + iekStrJoin (1) in
## runtime_strings.nim. Item 4a (round-6 re-review, walker v114) added 6 more
## in runtime.nim -- the c42721d N46-followup guard-before checks (`iteSV`'s
## svSeq arm; `placeholderCmpDecline`'s own receiver pick; `cmpBV`/`eqBV`/
## `neBV`'s R1-chokepoint guards; `svLeafEq`'s svSeq arm), each the guard
## itself (category (d) above), simply missing the marker. 49 + 6 = 55.
## N14 (9dbc3df, round-6 fix round 2 slice) added 10 more in runtime.nim for
## the new `iekSeqDel`/`isIndexAssign`/`isSeqPop` lowering -- 55 + 10 = 65,
## all correctly guarded by a same-arm `isUnsupportedFieldPlaceholder` check
## that precedes them. That slice missed two sites when marking: the
## `isIndexAssign` and `isSeqPop` receiver-REBIND lines (`newEnv[...] =
## SymVal(..., seqLen: recvSV.seqLen, ...)` / `(..., seqDataRaw:
## recvSV.seqDataRaw, ...)`) read the guarded receiver again after the store
## but were left unmarked -- caught by this audit's own scan (item 1,
## round-6 fix round 3). Both are the SAME category (a) guarantee as their
## neighboring marked reads three lines above (same `recvSV`, never
## reassigned since the arm's own placeholder decline `continue`d above);
## no guard was missing, only the marker. 65 + 2 = 67. Exact count is
## asserted below (a count drift in EITHER direction means a site was added,
## removed, or silently duplicated/split since this audit was written, and
## must be re-examined by a human).
import std/[unittest, strutils, os]
import nelli/smt/canonicalize
import audit_scan_utils

const
  runtimeNimPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                   "smt" / "runtime.nim"
  runtimeStringsNimPath = currentSourcePath.parentDir() / ".." / "src" /
                          "nelli" / "smt" / "runtime_strings.nim"
    ## Resolved at COMPILE time (pure path arithmetic on `currentSourcePath`
    ## -- no file content embedded), read at TEST RUNTIME (see header).

  targetFields = ["seqLen", "seqDataRaw", "isUnsupportedFieldPlaceholder"]
  auditMarker = "# [placeholder-audited]"

type
  Violation = object
    file:     string
    lineNo:   int
    lineText: string
    field:    string

proc fieldNameAt(s: string, i: int): string =
  ## If `s[i] == '.'` and the identifier that follows it -- after skipping
  ## any same-line whitespace between the `.` and the identifier, since both
  ## `recv . seqLen` and `recv .seqLen` are Nim-legal spaced dot-access forms
  ## and not merely `recv.seqLen` -- is, at a word boundary on both ends,
  ## exactly one of `targetFields`, return that field name; `""` otherwise.
  ## Mirrors the N2 audit's `routineVocabWordLenAt` separator-aware
  ## word-match idiom. LIMITATION (documented, not fixed): this is still a
  ## per-line, per-`splitLines` scan -- a `.` and its field name split
  ## across a line break (e.g. a dot ending one line and the field name
  ## starting the next) are NOT detected. Full tokenization/lexing to close
  ## that gap is out of scope for this text-scan audit; see the header's
  ## "what counts as bare" note.
  if i >= s.len or s[i] != '.': return ""
  var start = i + 1
  while start < s.len and (s[start] == ' ' or s[start] == '\t'):
    inc start
  if start >= s.len or not isIdentChar(s[start]): return ""
  var j = start
  while j < s.len and isIdentChar(s[j]): inc j
  let word = s[start ..< j]
  if word in targetFields: word else: ""

proc scanForBarePlaceholderFieldReads(fname, contents: string,
                                       violations: var seq[Violation]) =
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if trimmed.len == 0 or isCommentLine(trimmed):
      continue
    if trimmed.contains(auditMarker):
      continue   ## whole line exempted -- the marker covers every match on it
    var i = 0
    while i < rawLine.len:
      let field = fieldNameAt(rawLine, i)
      if field.len > 0:
        violations.add Violation(file: fname, lineNo: lineNo,
                                  lineText: rawLine, field: field)
        i += field.len + 1
      else:
        inc i

proc countMarkers(contents: string): int =
  for rawLine in contents.splitLines():
    if rawLine.contains(auditMarker):
      inc result

suite "symex N27 — permanent placeholder-field-read regression audit":

  test "zero bare .seqLen / .seqDataRaw / .isUnsupportedFieldPlaceholder reads outside the marked, reviewed sites":
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    var violations: seq[Violation]
    scanForBarePlaceholderFieldReads("src/nelli/smt/runtime.nim",
                                      runtimeSrc, violations)
    scanForBarePlaceholderFieldReads("src/nelli/smt/runtime_strings.nim",
                                      runtimeStringsSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " bare placeholder-sensitive field read(s) outside the reviewed, " &
        "marked site inventory:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & " (." & v.field &
          "):  " & v.lineText.strip() & "\n"
      report.add "Either route this read through the R1 chokepoint " &
        "(check isUnsupportedFieldPlaceholder first, decline via " &
        "declinePlaceholderInLower for a verdict-affecting read), or -- if " &
        "already legitimately guarded (e.g. reached only after a same-proc " &
        "flag check, or the element type is structurally always backed) -- " &
        "tag the line with the exact trailing comment `# [placeholder-" &
        "audited]` after review, per N27 (round-6 fix round 2, #High)."
      checkpoint(report)
    check violations.len == 0

  test "the N27 site inventory carries exactly 113 marked lines (110 runtime.nim + 3 runtime_strings.nim)":
    ## A count drift means a site was added, removed, or silently
    ## duplicated/split since this audit was written -- re-examine by hand
    ## (bump this count deliberately, in the same commit as the review).
    ##
    ## Round-6 re-review (item 4a, walker v114): the full-suite sweep found
    ## 11 unmarked violations at 6 distinct lines -- the c42721d N46-followup
    ## guard-before checks (`iteSV`'s svSeq arm, `placeholderCmpDecline`'s own
    ## receiver pick, `cmpBV`/`eqBV`/`neBV`'s R1-chokepoint guards, and
    ## `svLeafEq`'s svSeq arm). Every one IS the reviewed guard-before check
    ## routing to the R1 chokepoint (category (d) in this file's header) --
    ## marked, not rewritten. 49 + 6 = 55.
    ##
    ## N14 (9dbc3df) added 10 correctly-guarded sites for `iekSeqDel`/
    ## `isIndexAssign`/`isSeqPop`: 55 + 10 = 65. Round-6 fix round 3 (item 1)
    ## found 2 more unmarked-but-guarded reads in that same new code (the
    ## `isIndexAssign`/`isSeqPop` receiver-rebind lines) and marked them:
    ## 65 + 2 = 67.
    ##
    ## RFC-0005 S9 (walker 152) added `sameSymVal`'s svSeq arm: two lines
    ## comparing Z3 handles and the placeholder flag for identity, lowering
    ## nothing (a closure body's by-reference write check). 67 + 2 = 69.
    ##
    ## RFC-0005 S8f (walker 154) added `extractFromSymVal`'s `seq[ref T]`
    ## element cells: two lines reading `seqDataRaw` inside the `else` of the
    ## `isUnsupportedFieldPlaceholder` guard directly above them, so a
    ## placeholder never reaches them. 69 + 2 = 71.
    ##
    ## RFC-0005 S8h (walker 156) moved every ref-position walk into
    ## `collectRefPositions`: S8f's two `seq[ref T]` cell lines and the three
    ## `extractFromSymVal` seq-element lines are deleted, and four lines
    ## (the guard `not sv.isUnsupportedFieldPlaceholder` itself, then
    ## `seqDataRaw`/`seqLen` reads that only run once that guard holds) are
    ## added. 71 - 5 + 4 = 70.
    ##
    ## RFC-0005 S8p (walker 164) binds a genuine seq in `retBindEq`: four
    ## lines reading `seqLen`/`seqDataRaw` in the `else` of the
    ## `isUnsupportedFieldPlaceholder` guard directly above them, so a
    ## placeholder never reaches them. 70 + 4 = 74.
    ##
    ## RFC-0005 S8w (walker 171) added `sameSV`'s svSeq arm (the
    ## short-circuit join's env identity check): two lines comparing Z3
    ## handles and the placeholder flag for identity, lowering nothing --
    ## the same shape as S9's `sameSymVal` arm. 74 + 2 = 76.
    ##
    ## RFC-0005 S8aa added `joinSV`'s svSeq arm (the short-circuit join's
    ## seq merge): the guard `t/e.isUnsupportedFieldPlaceholder` itself, then
    ## four lines reading `seqDataRaw`/`seqLen` that only run once that guard
    ## has declined a placeholder on either side. 76 + 5 = 81.
    ##
    ## RFC-0005 S8ap added `renderHeapCompound`'s svSeq arm (a leaf-split
    ## seq heap cell's witness render): the guard
    ## `sv.isUnsupportedFieldPlaceholder` itself, then three lines reading
    ## `seqLen`/`seqDataRaw` that only run once that guard has returned on
    ## a placeholder. 81 + 4 = 85.
    ## RFC-0005 S8ar: `iekSeqAdd`'s per-kind store copies (two marked reads)
    ## became one `storeSeqElem` call (one, after the arm's placeholder
    ## guard); `iekSeqInsert` adds its guard and five reads behind it; and
    ## `extractSeqElements` gains a `seq[string]` arm (one read, beside the
    ## other element kinds'). 85 - 2 + 1 + 6 + 1 = 91.
    ## RFC-0005 S8at: `iteSV`'s svSeq arm merges two genuine seqs exactly
    ## (an array of seqs at a symbolic index): six lines reading
    ## `seqDataRaw`/`seqLen` in the `else` of the arm's own
    ## `isUnsupportedFieldPlaceholder` guard. 91 + 6 = 97.
    ## RFC-0005 S8bc: a seq of a tree element holds one data array per
    ## leaf, so the seq sites build through `seqArrs` / `withSeqArrsOf` /
    ## `mkSeqSV` / `seqStoreArrs` (seven marked reads: the two helpers'
    ## own, `conformSV`'s guard pair, truncation length and rebuild,
    ## `seqStoreArrs`' scalar store). Twenty marked reads at the sites
    ## (`retBindEq` 3, `iteSV` 4, slice 1, add 1, del 1, insert 3, `astHash`
    ## 1, `joinSV` 3, `isIndexAssign` 2, `isSeqPop` 1) became seven
    ## (`retBindEq`, `extractTreeValue`'s guard and length, `astHash`,
    ## `joinSV`, `isIndexAssign`, `isSeqPop`). 97 + 7 + 7 - 20 = 91.
    ##
    ## RFC-0005 S8be added two element-cell helpers: `withElem` writes an
    ## element of a seq the parser gave cells to, only a seq of scalars or
    ## strings (always backed); `sameSeqLen` guards both sides'
    ## `isUnsupportedFieldPlaceholder` (two lines) before comparing the
    ## length handles. 85 + 4 = 89.
    ## Batch 4 (S8bc then S8be): 91 + 4 = 95.
    ## RFC-0005 S8bl: six more, each behind its own guard -- `isSetLen`'s
    ## placeholder guard and old length (2), `collectTreeRefPositions`'
    ## guard and length (2), and `collectRefPositions`' tree-element arm's
    ## guard and length (2). 91 + 6 = 97.
    ## Batch 6 (S8bl on batch 5): 95 + 6 = 101.
    ##
    ## RFC-0005 S8bq added nine lines that read `seqDataRaw` only to ask
    ## whether its term mentions a `newSeqUninit` base: `uninitReadCond`
    ## (three; reached from `isIndex` / `isSeqPop` / `hofElemAt` after their
    ## placeholder guards), `noteUninitReturn` (five) and `svMentionsUninit`
    ## (one). None lowers or binds the data: a placeholder's inert array
    ## mentions no base, so each answers "no unwritten element" and the
    ## caller's own placeholder handling is unchanged. 85 + 9 = 94.
    ## Batch 6 (S8bq on S8bl on batch 5): 101 + 9 = 110.
    ##
    ## RFC-0005 S8bw added `svAsts`'s svSeq arm (the Z3 terms a global's
    ## value holds, scanned for its unwritten leaves): two lines collecting
    ## `seqDataRaw`/`seqLen` as terms, lowering nothing -- a placeholder's
    ## inert array and pinned length are terms like any other. 84 + 2 = 86.
    ## Batch 6 (S8bw on S8bq): its `seqDataRaw` line collects every leaf
    ## array through `seqArrs` (S8bc's audited helper) instead, so only the
    ## `seqLen` line is new. 110 + 1 = 111.
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    let runtimeCount = countMarkers(runtimeSrc)
    let runtimeStringsCount = countMarkers(runtimeStringsSrc)
    checkpoint("runtime.nim marker count: " & $runtimeCount &
               "; runtime_strings.nim marker count: " & $runtimeStringsCount)
    check runtimeCount == 111
    check runtimeStringsCount == 3

  test "scanner escape-hatch (round-6 review Low, mini re-review): a bogus marker on a genuinely unguarded read trips the audit, then reverts clean":
    ## The marker-count pin above (49 + 3) closes the ADDITIVE half of the
    ## escape hatch a mini re-review flagged: an audit marker with no review
    ## gate could otherwise be dropped on any line to silence the scanner --
    ## the count assertion fails the moment a NEW marker appears anywhere. It
    ## does not, by itself, DEMONSTRATE that the scanner actually catches the
    ## shape it claims to (proving the negative -- "an unmarked bare read
    ## trips it" -- is a different check from "the marked-line count is
    ## right"). Mirrors this file's own sibling audit's self-demonstration
    ## (`tests/tsymex_r6_n36_raise_class_audit.nim`'s "house scanner
    ## demonstration" test, same TOT-1 rationale) -- an IN-MEMORY injection
    ## (never a file mutation), so this test can never leave the tree dirty
    ## regardless of outcome.
    let injected = "src/nelli/smt/runtime.nim" & "\n" &
      "      let bogus = recv.seqLen\n"
    var violations: seq[Violation]
    scanForBarePlaceholderFieldReads("synthetic.nim", injected, violations)
    check violations.len == 1
    # Same injected line, now marked with the exact sanctioned marker text --
    # must revert to clean. Demonstrates the marker itself is what silences
    # the scanner (the mechanism the escape-hatch finding is about), not
    # some other property of the line.
    let markedInjected =
      "      let bogus = recv.seqLen  # [placeholder-audited]\n"
    var violations2: seq[Violation]
    scanForBarePlaceholderFieldReads("synthetic.nim", markedInjected, violations2)
    check violations2.len == 0

  test "walker version floor >= 97 (N27: lowerHofCall placeholder-receiver guard)":
    check parseInt(symexWalkerVersion) >= 97
