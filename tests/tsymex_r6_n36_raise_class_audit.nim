## N36 (round-6 fix round 4) — permanent regression audit closing the
## raw-raise-in-lower CLASS (N31's root cause, generalized), not just the one
## `iekStrSubstr` instance N31 fixed. Sibling to `tsymex_r6_n27_placeholder_
## read_audit.nim` (same TOT-1 institutionalization rationale, same house
## scan-and-marker technique) rather than an extension of it: this audits a
## DIFFERENT vocabulary — raw `raise` STATEMENTS of a classified-decline
## error carrier, not field reads.
##
## ----------------------------------------------------------------------------
## N46 (round-6 re-review) — WIDENING: bare `raise newException(` + full file
## coverage
## ----------------------------------------------------------------------------
## The re-review's own framing: "bea6921 proved the audit has a blind spot —
## two `iekSeqAdd` sites used bare `raise newException(ValueError, ...)` —
## same hazard, invisible to the audit." This slice closes TWO distinct gaps
## in the ORIGINAL N36 scanner, not one:
##
##   1. VOCABULARY gap: the original scanner only matched the literal prefix
##      `raise (ref Symex` — a bare `raise newException(<AnyExceptionType>, ...)`
##      inside the SAME hazard zone was invisible to it. `scanForBareNewException
##      Raises` (below) closes this — it matches ANY line containing the
##      substring `raise newException(` (not a comment line), which also
##      catches the common `else: raise newException(...)` single-line-if
##      idiom the prefix-only match would have missed (`trimmed.startsWith`
##      would see "else:", not "raise", as the line's leading token).
##
##   2. FILE-COVERAGE gap: the original scanner never scanned
##      `runtime_heap.nim` AT ALL, for EITHER pattern — despite it being
##      `include`d directly into `runtime.nim` (between `walkBlock` and
##      `walk`'s own body) and its top proc `walkHeapArm` being called
##      directly from `walk`'s own statement dispatch (`of isDeref, isNew,
##      isDerefWrite: walkHeapArm(...)`), making it unambiguously part of the
##      SAME hazard zone as `runtime.nim`/`runtime_strings.nim`. Widening the
##      file list surfaced 13 UNMARKED, pre-existing `raise (ref Symex...)`
##      sites in `runtime_heap.nim`'s heap-deref/ref-variant-field machinery —
##      a real, previously-invisible instance of exactly the blind-spot shape
##      bea6921 already found once. These are marked `LEDGERED-LIVE` (see the
##      marker-reason vocabulary below) — plausibly live, NOT converted this
##      slice (nested ref/variant heap machinery; a careful conversion needs
##      its own dedicated scoping), and NOT silently dropped: the count is
##      pinned below so a future round must consciously address or
##      re-adjudicate each one.
##
## N46 TRIAGED every one of the (then-)81 bare-`raise newException(` sites
## across the three files into category (a) LIVE hazard / (b) parse-time-only
## / (c) documented invariant / (d) uncertain, per the class description's own
## framework. 15 confirmed category-(a) sites were CONVERTED to the in-band
## degrade idiom this slice (`allocDegrade`/`loweringDegradeErrors`+
## `loweringDidDegrade`, matching each site's own local siblings) — see
## `canonicalize.nim`'s `symexWalkerVersion` doc (109→110→111) for the full
## per-site list. Every REMAINING bare `raise newException(` site is tagged
## `category-c: <reason>` (documented/provable invariant — no repro
## constructed, but a concrete unreachability argument given) or
## `category-d: <reason>` (uncertain — the argument was not fully closed;
## LEDGERED, not claimed safe) per line, in the SAME `# [raise-audited: ...]`
## marker convention this file already established for the `raise (ref
## Symex...)` vocabulary — one scanner, one marker syntax, two target
## patterns.
##
## ----------------------------------------------------------------------------
## Why a permanent test, not a one-time grep (same TOT-1 rationale N27 cites)
## ----------------------------------------------------------------------------
## N31's own root cause was exactly this failure mode: a raw `raise (ref
## SymexUnsupportedStringOpError)` inside `lowerStrArm`, reached from inside
## nested `walkBlock` frames, silently lost by Nim's C-backend goto-exception
## unwind (ADR-0023/SND-3) — `walk()` returns as if nothing happened,
## `w.sawUnknown` stays false, and the walker's default-to-UNSAT fallback can
## report a false `sxUnsat` for a concretely reachable target. N31 fixed ONE
## site. A round-4 spot-check found 14+ further raw raises of the SAME
## carrier shape still live. N36 converts every one of those (either at a
## chokepoint — the string family — or at its own call site — `isVariantReassign`/
## `isIndex`). A slice-close grep proves the CURRENT inventory is complete
## once; it catches no future regression — nothing stops a later edit from
## adding a new unguarded `raise (ref SymexFooError)` OR bare `raise
## newException(...)` inside a walk-reachable arm. This test makes that
## impossible to do silently: every future compile of the test suite
## re-scans `runtime.nim`/`runtime_strings.nim`/`runtime_heap.nim` for both
## shapes.
##
## ----------------------------------------------------------------------------
## Scope: what this audits and what it deliberately does NOT
## ----------------------------------------------------------------------------
## SCANNED (two independent patterns, same three files):
##   (A) `raise (ref Symex` — a line whose TRIMMED text starts with this
##       literal: a raw construction of one of the dedicated classified-
##       decline error-carrier types (`SymexUnsupportedStringOpError`, …, all
##       `object of CatchableError`). Mechanically unambiguous: a genuine
##       `raise` STATEMENT always begins its own trimmed line for this
##       pattern in this codebase's style (verified: no `else: raise (ref
##       Symex...)` inline form exists anywhere in the three scanned files as
##       of N46), so a doc-comment merely MENTIONING the same text in prose
##       can never match (comments are always `#`/`##`-prefixed).
##   (B) `raise newException(` — ANY line (not a comment line) CONTAINING
##       this substring, regardless of leading tokens. Deliberately NOT a
##       strict `startsWith` check like pattern (A): this codebase commonly
##       spells a narrow decline as `else: raise newException(ValueError,
##       "...")` on one line, which `startsWith("raise newException(")` would
##       miss entirely (the trimmed line's first token is `else:`). A
##       `contains` check risks matching prose that merely NAMES the pattern
##       in a comment — excluded by requiring the line not be a comment line
##       (mirrors N27's `isCommentLine` discipline) — verified for this
##       specific codebase state: every non-comment occurrence of the
##       substring `raise newException(` in the three files is a genuine
##       `raise` statement (either at the trimmed line's start, or
##       immediately following `else:`/`else :`), not a string-literal
##       mention.
##
## NOT SCANNED (deliberately, out of THIS audit's net):
##   - `raiseAssert`/`doAssert` sites. The class description's own framing
##     excludes these: "Defect-class invariant raises (doAssert/raiseAssert/
##     width-mismatch ValueErrors on states the walker never produces) are
##     NOT in scope." Auditing them is a DIFFERENT, larger undertaking,
##     deliberately left to a future round.
##
## ----------------------------------------------------------------------------
## What counts as "exempt" (marker discipline)
## ----------------------------------------------------------------------------
## A matched line is EXEMPT (no violation) when the SAME raw line carries the
## marker comment `# [raise-audited: <reason>]`. `git log`/`git blame` on
## these markers is the audit trail for WHY each one is safe. Reason-text
## FAMILIES in use (free-form after the `raise-audited:` prefix, not a fixed
## enum — same discipline N36 originally established):
##   - `converted-at-chokepoint` / `param-boundary` / `verified-unreachable:
##     <gate>` — pattern (A)'s pre-existing N36/N37/N40 vocabulary, unchanged
##     by N46 except `runtime_strings.nim`'s count (19→20: N46 hardened one
##     previously-bare-`ValueError` site, `lowerStrArm`'s final `else`, into
##     the SAME classified-carrier + chokepoint shape its two siblings
##     already use — see that site's own marker for the "why", a defense-in-
##     depth close of a fragility note, not a proven-live conversion).
##   - `LEDGERED-LIVE` (N46) — pattern (A), `runtime_heap.nim` only (13
##     sites): plausibly-live, genuinely unconverted this slice. An honest
##     backlog entry, never a "verified safe" claim.
##   - `category-c: <reason>` (N46) — pattern (B): a documented/provable
##     invariant (width-exhaustive, op-narrowed-by-caller, discriminator-
##     kind, bijectivity-guarded, BV-arithmetic-only, index-must-be-int,
##     literal-index-OOB, test-injection-only, post-walk-witness-extraction,
##     caught-immediately-at-sole-call-site, or an explicit in-code
##     "walker/parser bug, not SUT-reachable" doc claim already present at
##     the site) — see each marker's own reason text for the specific
##     argument.
##   - `category-d: <reason>` (N46) — pattern (B): genuinely UNCERTAIN —
##     the reachability argument was not fully closed (e.g. not every call
##     site was enumerated, or a specific code path was not traced end to
##     end). LEDGERED, not claimed safe; the marker names exactly what is
##     still open.
##
## ----------------------------------------------------------------------------
## `staticRead` vs `readFile` (toolchain note, N27 precedent)
## ----------------------------------------------------------------------------
## Same MSVC C2026 ("string too big") risk N27's header documents — this test
## reads all three scanned files at TEST RUNTIME (`readFile`) rather than
## compile time (`staticRead`); the path is still resolved at compile time
## (`currentSourcePath`, pure string arithmetic, no file content embedded).
##
## ----------------------------------------------------------------------------
## Site inventory as of N46 (round-6 re-review)
## ----------------------------------------------------------------------------
## Pattern (A) `raise (ref Symex...)`: runtime.nim 7 (unchanged from N40) +
## runtime_strings.nim 20 (19 pre-existing + 1 N46 hardening) +
## runtime_heap.nim 13 (all new N46 `LEDGERED-LIVE`, file never previously
## scanned) = 40 marked lines.
## Pattern (B) `raise newException(...)`: runtime.nim 78 (72 category-c + 6
## category-d) + runtime_strings.nim 0 (its one bare-ValueError site was
## hardened into pattern (A) instead, see above) + runtime_heap.nim 3 (all
## category-c) = 81 marked lines. 15 further pattern-(B) sites were CONVERTED
## this slice (no longer raw raises, no marker, no longer scanned/counted):
## `iteSV` (3: svUninterpRef/composite/svClosure merge arms), `cmpBV`/`eqBV`/
## `neBV` (3: non-BV-kind else arms), `refEq` (1: ordering-op mismatch),
## `lowerCmp`'s bool-ordering else (1), `svLeafEq` (1: composite closure-env
## field), `retBindEq` (2: svSeq + final composite else), `iekTableSet` (1:
## unsupported val type), `iekSeqDel`/`iekSeqInsert`/`iekSeqPop` (1 combined
## arm), `iekContains` (1: final else), `iekBorrowOp` (1: unsupported base
## operator), `seqElemAt` (1: unsupported elem kind — a genuine itRef/itPtr
## read-side asymmetry vs. `storeSeqElem`'s write-side, which DOES handle
## them). A further site, `applyClosureGround`'s unguarded `defaultZero`
## fallback call, was closed by REPLACING the call with the proven-total
## `allocateSym` (N40) rather than converting a `raise newException(` line
## directly — it does not appear in either pattern's count.
## Exact counts are asserted below (a count drift in EITHER direction means a
## site was added, removed, or silently duplicated/split since this audit was
## written, and must be re-examined by a human).
import std/[unittest, strutils, os]
import nelli/smt/canonicalize

const
  runtimeNimPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                   "smt" / "runtime.nim"
  runtimeStringsNimPath = currentSourcePath.parentDir() / ".." / "src" /
                          "nelli" / "smt" / "runtime_strings.nim"
  runtimeHeapNimPath = currentSourcePath.parentDir() / ".." / "src" /
                       "nelli" / "smt" / "runtime_heap.nim"
    ## Resolved at COMPILE time (pure path arithmetic on `currentSourcePath`
    ## -- no file content embedded), read at TEST RUNTIME (see header).

  refSymexPrefix = "raise (ref Symex"
  newExcSubstr = "raise newException("
  auditMarker = "# [raise-audited:"
  knownOpenMarker = "# [raise-audited: known-open"
    ## N37 addition: the SPECIFIC `known-open` reason prefix, distinct from
    ## `auditMarker` (which matches ANY reason). Used by the zero-known-open
    ## enforcement test below. Distinct from N46's `LEDGERED-LIVE`/
    ## `category-d` reasons -- those are honest backlog markers TOO, but
    ## under a DIFFERENT name so they do not retroactively falsify N37's own
    ## "zero known-open markers remain" certification (a different, already-
    ## closed adjudication).
  ledgeredLiveMarker = "# [raise-audited: LEDGERED-LIVE"
  categoryDMarker = "# [raise-audited: category-d:"

type
  Violation = object
    file:     string
    lineNo:   int
    lineText: string

proc isCommentLine(trimmed: string): bool = trimmed.startsWith("#")

proc scanForBareRefSymexRaises(fname, contents: string,
                                violations: var seq[Violation]) =
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if not trimmed.startsWith(refSymexPrefix):
      continue   ## not a raw classified-carrier `raise` STATEMENT at all --
                  ## a `#`/`##`-prefixed comment mentioning the same text in
                  ## prose never starts its trimmed line this way.
    if rawLine.contains(auditMarker):
      continue    ## reviewed and marked -- see the marker's own reason text.
    violations.add Violation(file: fname, lineNo: lineNo, lineText: rawLine)

proc scanForBareNewExceptionRaises(fname, contents: string,
                                    violations: var seq[Violation]) =
  ## Pattern (B), N46. Unlike pattern (A) above, this is a CONTAINS check
  ## (not `startsWith`): the common `else: raise newException(...)`
  ## single-line-if idiom means the raise is often NOT the trimmed line's
  ## first token. Comment lines are excluded by `isCommentLine` (mirrors
  ## N27's discipline) -- verified for this codebase's current state that no
  ## non-comment line contains this substring without it being a genuine
  ## `raise` statement (see this file's own header note).
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if trimmed.len == 0 or isCommentLine(trimmed):
      continue
    if not trimmed.contains(newExcSubstr):
      continue
    if rawLine.contains(auditMarker):
      continue
    violations.add Violation(file: fname, lineNo: lineNo, lineText: rawLine)

proc countMarked(contents: string, prefix: string, useContains: bool): int =
  for rawLine in contents.splitLines():
    let trimmed = rawLine.strip()
    let isMatch = if useContains: (not isCommentLine(trimmed)) and
                                   trimmed.contains(prefix)
                  else: trimmed.startsWith(prefix)
    if isMatch and rawLine.contains(auditMarker):
      inc result

proc countKnownOpenMarkers(contents: string): int =
  for rawLine in contents.splitLines():
    let trimmed = rawLine.strip()
    if trimmed.startsWith(refSymexPrefix) and rawLine.contains(knownOpenMarker):
      inc result

proc countMarkersContaining(contents: string, needle: string): int =
  for rawLine in contents.splitLines():
    if rawLine.contains(needle):
      inc result

suite "symex N36 — permanent raw-raise-in-lower CLASS regression audit":

  test "zero bare `raise (ref Symex*)` statements outside the reviewed, marked site inventory (all three files)":
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    let runtimeHeapSrc = readFile(runtimeHeapNimPath)
    var violations: seq[Violation]
    scanForBareRefSymexRaises("src/nelli/smt/runtime.nim",
                               runtimeSrc, violations)
    scanForBareRefSymexRaises("src/nelli/smt/runtime_strings.nim",
                               runtimeStringsSrc, violations)
    scanForBareRefSymexRaises("src/nelli/smt/runtime_heap.nim",
                               runtimeHeapSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " bare classified-carrier raise (ref Symex...) statement(s) outside " &
        "the reviewed, marked site inventory:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " &
          v.lineText.strip() & "\n"
      report.add "Either convert this raise to the in-band degrade idiom, " &
        "route it through an existing chokepoint, or -- if genuinely safe " &
        "or a deliberately-deferred backlog item -- tag the line with the " &
        "exact trailing comment `# [raise-audited: <reason>]` after review."
      checkpoint(report)
    check violations.len == 0

  test "zero bare `raise newException(...)` statements outside the reviewed, marked site inventory (all three files)":
    ## N46 (round-6 re-review): the widened pattern (B) scan.
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    let runtimeHeapSrc = readFile(runtimeHeapNimPath)
    var violations: seq[Violation]
    scanForBareNewExceptionRaises("src/nelli/smt/runtime.nim",
                                   runtimeSrc, violations)
    scanForBareNewExceptionRaises("src/nelli/smt/runtime_strings.nim",
                                   runtimeStringsSrc, violations)
    scanForBareNewExceptionRaises("src/nelli/smt/runtime_heap.nim",
                                   runtimeHeapSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " bare `raise newException(...)` statement(s) outside the reviewed, " &
        "marked site inventory:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " &
          v.lineText.strip() & "\n"
      report.add "Triage into category (a) LIVE hazard -- convert via " &
        "allocDegrade/loweringDegradeErrors+loweringDidDegrade, matching a " &
        "local sibling's idiom -- (b) parse-time-only, (c) documented " &
        "invariant, or (d) uncertain, then tag the line with the exact " &
        "trailing comment `# [raise-audited: category-c: <reason>]` or " &
        "`# [raise-audited: category-d: <reason>]` after review, per N46 " &
        "(round-6 re-review)."
      checkpoint(report)
    check violations.len == 0

  test "pattern (A) site inventory: 7 runtime.nim + 20 runtime_strings.nim + 13 runtime_heap.nim marked lines":
    ## A count drift means a site was added, removed, or silently
    ## duplicated/split since this audit was written -- re-examine by hand
    ## (bump this count deliberately, in the same commit as the review).
    ## runtime.nim/runtime_strings.nim counts are N40's own (7 unchanged;
    ## runtime_strings.nim 19->20, N46 hardened `lowerStrArm`'s final else
    ## from a bare ValueError into this SAME pattern + chokepoint shape).
    ## runtime_heap.nim (13) is entirely NEW as of N46 -- this file was never
    ## scanned before this slice.
    let runtimeCount = countMarked(readFile(runtimeNimPath), refSymexPrefix, false)
    let runtimeStringsCount = countMarked(readFile(runtimeStringsNimPath), refSymexPrefix, false)
    let runtimeHeapCount = countMarked(readFile(runtimeHeapNimPath), refSymexPrefix, false)
    checkpoint("runtime.nim=" & $runtimeCount & " runtime_strings.nim=" &
               $runtimeStringsCount & " runtime_heap.nim=" & $runtimeHeapCount)
    check runtimeCount == 7
    check runtimeStringsCount == 20
    # N46-followup-2 (round-6 re-review, heap-raise totality slice):
    # runtime_heap.nim's 13 LEDGERED-LIVE sites were adjudicated -- 7
    # CONVERTED to the in-band degrade idiom (no longer raw raises, no
    # longer marked/counted, per this file's own established convention for
    # a converted site) and 6 RECLASSIFIED `verified-unreachable` (still raw
    # raises, still marked -- 13 -> 6).
    check runtimeHeapCount == 6

  test "pattern (B) site inventory: 78 runtime.nim + 0 runtime_strings.nim + 3 runtime_heap.nim marked lines":
    let runtimeCount = countMarked(readFile(runtimeNimPath), newExcSubstr, true)
    let runtimeStringsCount = countMarked(readFile(runtimeStringsNimPath), newExcSubstr, true)
    let runtimeHeapCount = countMarked(readFile(runtimeHeapNimPath), newExcSubstr, true)
    checkpoint("runtime.nim=" & $runtimeCount & " runtime_strings.nim=" &
               $runtimeStringsCount & " runtime_heap.nim=" & $runtimeHeapCount)
    check runtimeCount == 78
    check runtimeStringsCount == 0
    check runtimeHeapCount == 3

  test "N46: pattern (B) category breakdown -- 72+3 category-c, 6+0 category-d (runtime.nim + runtime_heap.nim)":
    ## Sub-breakdown of the pattern-(B) inventory above, pinned separately so
    ## a future slice that resolves a `category-d` (uncertain) entry into
    ## `category-c` (proven) -- or vice versa, if a `category-c` argument
    ## turns out to be wrong -- must deliberately update this count too.
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeHeapSrc = readFile(runtimeHeapNimPath)
    let cCount = countMarkersContaining(runtimeSrc, "[raise-audited: category-c:") +
                 countMarkersContaining(runtimeHeapSrc, "[raise-audited: category-c:")
    let dCount = countMarkersContaining(runtimeSrc, categoryDMarker) +
                 countMarkersContaining(runtimeHeapSrc, categoryDMarker)
    checkpoint("category-c=" & $cCount & " category-d=" & $dCount)
    check cCount == 75
    check dCount == 6

  test "N46-followup-2: pattern (A) LEDGERED-LIVE backlog CLOSED -- zero remain (runtime_heap.nim)":
    ## The 13-site backlog N46 opened is fully adjudicated as of the
    ## heap-raise totality slice (walker v113): every site is either
    ## CONVERTED (no longer a raw raise, no longer marked) or RECLASSIFIED
    ## `verified-unreachable` (still a raw raise, still marked, but under a
    ## different reason -- see the pattern (A) site inventory test above,
    ## and `symexWalkerVersion`'s own doc comment for the full per-site
    ## writeup). Mirrors N37's own "zero known-open markers remain" closure
    ## discipline below -- a future regression that reintroduces a
    ## LEDGERED-LIVE marker (e.g. a careless revert) trips this immediately.
    let runtimeHeapSrc = readFile(runtimeHeapNimPath)
    let ledgeredCount = countMarkersContaining(runtimeHeapSrc, ledgeredLiveMarker)
    checkpoint("runtime_heap.nim LEDGERED-LIVE=" & $ledgeredCount)
    check ledgeredCount == 0

  test "N36 house scanner demonstration (pattern A): an injected bare raise trips the audit, then reverts clean":
    ## Demonstrates the scanner actually catches the shape it claims to,
    ## mirroring N27's own red/green self-demonstration -- an in-memory
    ## injection (not a file mutation) so this test never leaves the tree
    ## dirty regardless of outcome.
    let injected = "src/nelli/smt/runtime.nim" & "\n" &
      "      raise (ref SymexClassifiedDegradeError)(kind: feUnsupportedOp, msg: \"x\")\n"
    var violations: seq[Violation]
    scanForBareRefSymexRaises("synthetic.nim", injected, violations)
    check violations.len == 1
    # Same injected line, now marked -- must revert to clean.
    let markedInjected =
      "      raise (ref SymexClassifiedDegradeError)(kind: feUnsupportedOp, " &
      "msg: \"x\")  # [raise-audited: synthetic demonstration]\n"
    var violations2: seq[Violation]
    scanForBareRefSymexRaises("synthetic.nim", markedInjected, violations2)
    check violations2.len == 0

  test "N46 house scanner demonstration (pattern B): an injected bare `raise newException` -- including the `else:`-prefixed idiom -- trips the audit, then reverts clean":
    ## Two shapes: the plain trimmed-line-leading form AND the common
    ## `else: raise newException(...)` single-line-if idiom this pattern's
    ## `contains`-based (not `startsWith`-based) scan exists specifically to
    ## catch (see this file's own header note on why pattern (B) differs
    ## from pattern (A)'s stricter check).
    let injectedPlain = "src/nelli/smt/runtime.nim" & "\n" &
      "      raise newException(ValueError, \"x\")\n"
    var v1: seq[Violation]
    scanForBareNewExceptionRaises("synthetic.nim", injectedPlain, v1)
    check v1.len == 1
    let injectedElse = "src/nelli/smt/runtime.nim" & "\n" &
      "    else: raise newException(ValueError, \"x\")\n"
    var v2: seq[Violation]
    scanForBareNewExceptionRaises("synthetic.nim", injectedElse, v2)
    check v2.len == 1
    # Both marked -- must revert to clean.
    let markedPlain =
      "      raise newException(ValueError, \"x\")  # [raise-audited: category-c: synthetic demonstration]\n"
    var v3: seq[Violation]
    scanForBareNewExceptionRaises("synthetic.nim", markedPlain, v3)
    check v3.len == 0
    let markedElse =
      "    else: raise newException(ValueError, \"x\")  # [raise-audited: category-c: synthetic demonstration]\n"
    var v4: seq[Violation]
    scanForBareNewExceptionRaises("synthetic.nim", markedElse, v4)
    check v4.len == 0

  test "walker version floor >= 101 (N36: raw-raise-in-lower class closure)":
    check parseInt(symexWalkerVersion) >= 101

  test "N40: allocateSym is total -- the param boundary raises by design [raise-audited: param-boundary]":
    ## Final certification for this audit file's own tracked class (see the
    ## module doc comment's "What counts as exempt" section, `param-boundary`
    ## entry, above): `allocateSym` (`runtime.nim`) no longer raises a
    ## classified-decline carrier for ANY classifiable input, at any call
    ## site -- walk-time or otherwise.
    check parseInt(symexWalkerVersion) >= 104

  test "N37: zero `known-open` markers remain (every N36 backlog item adjudicated)":
    ## N37's own DoD: every marker N36 left as `known-open` backlog must end
    ## that slice either CONVERTED or upgraded to `verified-unreachable:
    ## <gate>` -- never left as a bare, unadjudicated `known-open`. Distinct
    ## from N46's OWN, separately-tracked `LEDGERED-LIVE`/`category-d`
    ## backlog above -- this test's zero-count is about the OLD `known-open`
    ## name specifically, an already-closed adjudication N46 does not reopen.
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    let knownOpenCount = countKnownOpenMarkers(runtimeSrc) +
                          countKnownOpenMarkers(runtimeStringsSrc)
    checkpoint("known-open marker count: " & $knownOpenCount)
    check knownOpenCount == 0

  test "N46: walker version floor >= 111 (round-6 re-review: 15 category-(a) sites converted to the in-band degrade idiom)":
    check parseInt(symexWalkerVersion) >= 111

  test "N46-followup-2: walker version floor >= 113 (heap-raise totality: runtime_heap.nim's 13-site LEDGERED-LIVE backlog closed)":
    check parseInt(symexWalkerVersion) >= 113
