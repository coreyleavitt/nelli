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
## N27 site inventory (58 marked sites: 55 in runtime.nim, 3 in
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
## itself (category (d) above), simply missing the marker. Exact count is
## asserted below (a count drift in EITHER direction means a site was added,
## removed, or silently duplicated/split since this audit was written, and
## must be re-examined by a human).
import std/[unittest, strutils, os]
import nelli/smt/canonicalize

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

proc isCommentLine(trimmed: string): bool =
  trimmed.startsWith("#")

proc isIdentChar(c: char): bool = c.isAlphaNumeric or c == '_'

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

  test "the N27 site inventory carries exactly 58 marked lines (55 runtime.nim + 3 runtime_strings.nim)":
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
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    let runtimeCount = countMarkers(runtimeSrc)
    let runtimeStringsCount = countMarkers(runtimeStringsSrc)
    checkpoint("runtime.nim marker count: " & $runtimeCount &
               "; runtime_strings.nim marker count: " & $runtimeStringsCount)
    check runtimeCount == 55
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
