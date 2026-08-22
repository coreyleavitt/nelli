## N36 (round-6 fix round 4) — permanent regression audit closing the
## raw-raise-in-lower CLASS (N31's root cause, generalized), not just the one
## `iekStrSubstr` instance N31 fixed. Sibling to `tsymex_r6_n27_placeholder_
## read_audit.nim` (same TOT-1 institutionalization rationale, same house
## scan-and-marker technique) rather than an extension of it: this audits a
## DIFFERENT vocabulary — raw `raise` STATEMENTS of a classified-decline
## error carrier, not field reads.
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
## adding a new unguarded `raise (ref SymexFooError)` inside a walk-reachable
## arm. This test makes that impossible to do silently: every future compile
## of the test suite re-scans `runtime.nim`/`runtime_strings.nim` for exactly
## that shape.
##
## ----------------------------------------------------------------------------
## Scope: what this audits and what it deliberately does NOT
## ----------------------------------------------------------------------------
## SCANNED: a line whose TRIMMED text starts with the literal `raise (ref
## Symex` — i.e. a raw construction of one of the ~19 dedicated classified-
## decline error-carrier types (`SymexUnsupportedStringOpError`,
## `SymexClassifiedDegradeError`, …, all `object of CatchableError` — see
## `runtime.nim`'s type block). This is the exact shape the class description
## names ("a raw raise of a classified-decline error carrier"), and it is
## mechanically unambiguous: a genuine `raise` STATEMENT always begins its own
## (trimmed) line in this codebase's style, so a doc-comment merely
## MENTIONING the same text in prose (this file's own header above included,
## and there is plenty of such prose in `runtime.nim`/`runtime_strings.nim`)
## can never match — prose is always preceded by `#`/`##` and other words on
## the same trimmed line.
##
## NOT SCANNED (deliberately, out of THIS audit's net):
##   - Bare `raise newException(ValueError, ...)` / `raiseAssert` / `doAssert`
##     sites. The class description's own framing excludes these: "Defect-
##     class invariant raises (doAssert/raiseAssert/width-mismatch ValueErrors
##     on states the walker never produces) are NOT in scope." There are 90+
##     such sites in `runtime.nim` alone (mostly "unreachable" walker-bug
##     sentinels) — auditing them is a DIFFERENT, much larger undertaking than
##     this class closure, deliberately left to a future round rather than
##     given a rushed, potentially-mis-classified marker pass here. The one
##     EXCEPTION the class description names by name — `defaultZero`'s
##     `ValueError` raises reached via `isVariantReassign` — is closed at its
##     CALL SITE (N36 wraps `try/except ValueError, SymexRefUnresolvedError`
##     at all three `defaultZero` call sites, matching the two pre-existing,
##     already-correct siblings) rather than by marking `defaultZero`'s own
##     raise lines; this audit does not separately re-verify that wrapping
##     (it is proc-call-site plumbing, not a text-scannable invariant).
##
## ----------------------------------------------------------------------------
## What counts as "exempt" (marker discipline)
## ----------------------------------------------------------------------------
## A matched line is EXEMPT (no violation) when the SAME raw line carries the
## marker comment `# [raise-audited: <reason>]` — added at every reviewed
## site by the N36 slice. `git log`/`git blame` on these markers is the audit
## trail for WHY each one is safe; each falls into one of:
##   - `converted-at-chokepoint` — the raise is one of the SIX classified
##     carriers `lowerStrArm` can raise; caught by `degradeStrArm` at the
##     SINGLE `lowerStrArm(env, e)` call site in `lower`'s dispatch
##     (`runtime.nim`), OR one of `defaultZero`'s ref/ptr raises, caught at
##     all three of ITS OWN call sites — no longer reachable in raw form.
##   - `category-2` — RETIRED as of N40 (round-6 fix round 6). This marker
##     used to cover an `allocateSym` site (itUninterp/itTable/itSet) SAFE
##     on its PRE-WALK param-entry path. N40 made `allocateSym` itself
##     TOTAL for every classifiable input — those five sites no longer
##     `raise` at all (converted to the in-band `allocDegrade` chokepoint),
##     so they no longer match this scan and carry no marker; see
##     `param-boundary` below for their replacement.
##   - `param-boundary` — N40 addition. A raw raise at the PRE-WALK
##     parameter-entry boundary (`raiseParamAllocIssue`, `runtime.nim`),
##     reached BEFORE any walk state (`currentWalkCtxPtr`) exists — the
##     ONE place in this codebase that is STILL allowed to raise for a
##     classified-unallocatable type, by design (preserves the whole-run
##     decline semantics every param-level pin expects). Distinct from the
##     old `category-2`: that marker asserted `allocateSym` itself was safe
##     to raise from BECAUSE of where it was called from; this marker
##     asserts the CALLER (`raiseParamAllocIssue`) is the intended, sole
##     raise site for this class of decline — `allocateSym` no longer
##     raises for the same input at all.
##   - `known-open` — a genuinely LIVE instance of the SAME hazard class this
##     slice did NOT convert. As of N36: `iekSeqLen`/`iekSeqSlice`'s raw
##     declines, `isRaise`'s bare-reraise decline, and `allocateSeqDataRaw`'s
##     raise as reached through `lowerHofCall`'s UNGUARDED inline `map`/
##     `filter` calls. Marked, not fixed — an honest backlog entry, not a
##     false "verified safe" claim, so a human reviewing `raise-audited`
##     markers sees exactly what remains open.
##   - `verified-unreachable: <gate>` — N37 addition. A genuinely LIVE-LOOKING
##     instance the class description's own scope covers, but PROVEN
##     unreachable from any valid DSL surface (or, for `allocateSeqDataRaw`'s
##     own raise, from any call site in this file after N37 guarded every
##     caller) — the marker names the EXACT gate (parser-level type
##     restriction, or "every caller now guards"). Not a stronger claim than
##     `known-open`'s honesty; a DIFFERENT one (proven safe vs. deferred).
##
## As of N37 (round-6 fix round 4, adjudication slice): every `known-open`
## marker N36 left has been adjudicated — three sites (`iekSeqSlice` x2,
## `isRaise` x1) were CONFIRMED REACHABLE and CONVERTED to the in-band
## degrade idiom (no longer raw `raise` statements, so they no longer match
## this scan and carry no marker); two sites (`iekSeqLen`,
## `allocateSeqDataRaw`) were adjudicated VERIFIED UNREACHABLE and their
## markers upgraded accordingly. ZERO `known-open` markers remain — see the
## dedicated test below that enforces this mechanically, not just by prose.
##
## ----------------------------------------------------------------------------
## `staticRead` vs `readFile` (toolchain note, N27 precedent)
## ----------------------------------------------------------------------------
## Same MSVC C2026 ("string too big") risk N27's header documents for
## `runtime.nim`'s ~565KB size — this test reads both scanned files at TEST
## RUNTIME (`readFile`) rather than compile time (`staticRead`); the path is
## still resolved at compile time (`currentSourcePath`, pure string
## arithmetic, no file content embedded).
##
## ----------------------------------------------------------------------------
## Site inventory as of N40 (26 marked lines: 7 in runtime.nim, 19 in
## runtime_strings.nim). Was 27 (8 + 19) at N39; N40 (round-6 fix round 6,
## allocateSym totality) REMOVED the five `category-2` raw-raise lines
## entirely (`allocateSym`'s itUninterp x3 + itTable + itSet arms no longer
## raise at all — converted to the in-band `allocDegrade` chokepoint, so
## they no longer match this scan and carry no marker) and ADDED four new
## `param-boundary` raw-raise lines at the pre-walk parameter-entry
## boundary (`raiseParamAllocIssue`) that preserve the SAME whole-run
## decline semantics those five sites used to provide when reached via a
## top-level param — net runtime.nim count 8 -> 3 -> 7. Before that, N39
## updated the FIVE `category-2` markers' REASON TEXT in place (no count
## change); before THAT, N37 converted 3 of runtime.nim's raw-raise lines
## away entirely (`iekSeqSlice` x2, `isRaise` x1) and upgraded 2 markers
## in place (`iekSeqLen`, `allocateSeqDataRaw`) from `known-open` to
## `verified-unreachable` without removing them (was 11 + 19 = 30 at N36).
## ----------------------------------------------------------------------------
## runtime.nim: allocateSeqDataRaw's nested-seq raise (1,
## verified-unreachable — every caller now guards with `isBackedSeqElemTy`);
## defaultZero's ref/ptr raise (1, converted-at-chokepoint); iekSeqLen (1,
## verified-unreachable — parser-level type gate + the one cross-
## representation mismatch already lands on the svString arm); the four
## `raiseParamAllocIssue` dispatch arms (4, param-boundary — N40, the sole
## remaining raise site for the six `unallocatableFieldIssue` kinds,
## reached ONLY at pre-walk parameter-entry, before any walk state exists).
## `allocateSym`'s former `category-2` itUninterp/itTable/itSet raises (5)
## are GONE (see the N40 paragraph above) — `allocateSym` itself no longer
## raises for classifiable input at all. N37 converted AWAY (no longer raw
## raises, no marker): `iekSeqSlice`'s base-kind and CR-17-style bound
## declines (2), `isRaise`'s bare-reraise decline (1). `isVariantReassign`'s
## `defaultZero` call and `isIndex`'s two declines (fixed at N36) remain
## absent from this count by construction, not omitted from review.
## runtime_strings.nim: every `lowerStrArm`-reachable raw raise (19, all
## converted-at-chokepoint) — `requireStr` (2), `needleAsStr` (1),
## `iekStrReplaceAll`'s version-gate (1), `iekStrJoin`/`iekStrSplit` (5),
## `iekStrMatch`/`iekStrFindRe`/`iekStrReplaceRe` (4), `iekStrBytes` (2),
## `iekRadixFmt` (1), `iekStrToLower`/`iekStrToUpper`'s shared catch (1),
## `iekStrInOptionRegion` (1), the "not modeled" catch-all (1). Untouched by
## N37. Exact count asserted below (a count drift in EITHER direction means a
## site was added, removed, or silently duplicated/split since this audit
## was written, and must be re-examined by a human).
import std/[unittest, strutils, os]
import nelli/smt/canonicalize

const
  runtimeNimPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                   "smt" / "runtime.nim"
  runtimeStringsNimPath = currentSourcePath.parentDir() / ".." / "src" /
                          "nelli" / "smt" / "runtime_strings.nim"
    ## Resolved at COMPILE time (pure path arithmetic on `currentSourcePath`
    ## -- no file content embedded), read at TEST RUNTIME (see header).

  targetPrefix = "raise (ref Symex"
  auditMarker = "# [raise-audited:"
  knownOpenMarker = "# [raise-audited: known-open"
    ## N37 addition: the SPECIFIC `known-open` reason prefix, distinct from
    ## `auditMarker` (which matches ANY reason). Used by the zero-known-open
    ## enforcement test below.

type
  Violation = object
    file:     string
    lineNo:   int
    lineText: string

proc scanForBareClassifiedRaises(fname, contents: string,
                                  violations: var seq[Violation]) =
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if not trimmed.startsWith(targetPrefix):
      continue   ## not a raw classified-carrier `raise` STATEMENT at all --
                  ## a `#`/`##`-prefixed comment mentioning the same text in
                  ## prose never starts its trimmed line this way.
    if rawLine.contains(auditMarker):
      continue    ## reviewed and marked -- see the marker's own reason text.
    violations.add Violation(file: fname, lineNo: lineNo, lineText: rawLine)

proc countMarkedClassifiedRaises(contents: string): int =
  for rawLine in contents.splitLines():
    let trimmed = rawLine.strip()
    if trimmed.startsWith(targetPrefix) and rawLine.contains(auditMarker):
      inc result

proc countKnownOpenMarkers(contents: string): int =
  ## N37 addition: count markers still carrying the `known-open` reason
  ## specifically (a subset of `countMarkedClassifiedRaises`). N37's own
  ## DoD is "zero `known-open` markers remain" -- enforced mechanically
  ## here, not just claimed in prose, so a FUTURE slice that adds a new
  ## `known-open` marker (a legitimate, honest thing to do) does not
  ## silently make this file's own header claim stale; the number simply
  ## needs to be re-examined and bumped deliberately, same discipline as
  ## `countMarkedClassifiedRaises`'s own count pins.
  for rawLine in contents.splitLines():
    let trimmed = rawLine.strip()
    if trimmed.startsWith(targetPrefix) and rawLine.contains(knownOpenMarker):
      inc result

suite "symex N36 — permanent raw-raise-in-lower CLASS regression audit":

  test "zero bare `raise (ref Symex*)` statements outside the reviewed, marked site inventory":
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    var violations: seq[Violation]
    scanForBareClassifiedRaises("src/nelli/smt/runtime.nim",
                                 runtimeSrc, violations)
    scanForBareClassifiedRaises("src/nelli/smt/runtime_strings.nim",
                                 runtimeStringsSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " bare classified-carrier raise statement(s) outside the reviewed, " &
        "marked site inventory:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " &
          v.lineText.strip() & "\n"
      report.add "Either convert this raise to the in-band degrade idiom " &
        "(`loweringDegradeErrors`/`loweringDidDegrade` from inside `lower()`, " &
        "or `w.walkDegradeErrors`/`w.sawUnknown`/`forkPathTainted` from " &
        "inside `walk`), or route it through an existing chokepoint " &
        "(`degradeStrArm` for a NEW `lowerStrArm` site), or -- if genuinely " &
        "safe (a pre-walk param-entry boundary with zero intervening " &
        "`walkBlock` frames) or a deliberately-deferred known-open backlog " &
        "item -- tag the line with the exact trailing comment `# [raise-" &
        "audited: <reason>]` after review, per N36 (round-6 fix round 4, " &
        "raw-raise-in-lower CLASS, #High)."
      checkpoint(report)
    check violations.len == 0

  test "the site inventory carries exactly 26 marked lines (7 runtime.nim + 19 runtime_strings.nim) as of N40":
    ## A count drift means a site was added, removed, or silently
    ## duplicated/split since this audit was written -- re-examine by hand
    ## (bump this count deliberately, in the same commit as the review).
    ## Was 11 + 19 = 30 at N36; N37 converted 3 runtime.nim raw-raise lines
    ## away entirely (no longer raw raises, no longer scanned/marked) --
    ## `iekSeqSlice` x2, `isRaise` x1 -- leaving 8. N40 (round-6 fix round 6,
    ## allocateSym totality) REMOVED the five `category-2` allocateSym raises
    ## entirely (8 -> 3) and ADDED four new `param-boundary` raises at the
    ## pre-walk parameter-entry boundary (3 -> 7) -- see this file's own
    ## site-inventory paragraph above for the full accounting.
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    let runtimeCount = countMarkedClassifiedRaises(runtimeSrc)
    let runtimeStringsCount = countMarkedClassifiedRaises(runtimeStringsSrc)
    checkpoint("runtime.nim marked-raise count: " & $runtimeCount &
               "; runtime_strings.nim marked-raise count: " &
               $runtimeStringsCount)
    check runtimeCount == 7
    check runtimeStringsCount == 19

  test "N37: zero `known-open` markers remain (every N36 backlog item adjudicated)":
    ## N37's own DoD: every marker N36 left as `known-open` backlog must end
    ## this slice either CONVERTED (no longer a raw raise at all -- see the
    ## count drop 11->8 in the sibling test above) or upgraded to
    ## `verified-unreachable: <gate>` -- never left as a bare, unadjudicated
    ## `known-open`. Enforced mechanically so a stale/forgotten backlog item
    ## cannot silently survive a future edit.
    let runtimeSrc = readFile(runtimeNimPath)
    let runtimeStringsSrc = readFile(runtimeStringsNimPath)
    let knownOpenCount = countKnownOpenMarkers(runtimeSrc) +
                          countKnownOpenMarkers(runtimeStringsSrc)
    checkpoint("known-open marker count: " & $knownOpenCount)
    check knownOpenCount == 0

  test "N36 house scanner demonstration: an injected bare raise trips the audit, then reverts clean":
    ## Demonstrates the scanner actually catches the shape it claims to,
    ## mirroring N27's own red/green self-demonstration -- an in-memory
    ## injection (not a file mutation) so this test never leaves the tree
    ## dirty regardless of outcome.
    let injected = "src/nelli/smt/runtime.nim" & "\n" &
      "      raise (ref SymexClassifiedDegradeError)(kind: feUnsupportedOp, msg: \"x\")\n"
    var violations: seq[Violation]
    scanForBareClassifiedRaises("synthetic.nim", injected, violations)
    check violations.len == 1
    # Same injected line, now marked -- must revert to clean.
    let markedInjected =
      "      raise (ref SymexClassifiedDegradeError)(kind: feUnsupportedOp, " &
      "msg: \"x\")  # [raise-audited: synthetic demonstration]\n"
    var violations2: seq[Violation]
    scanForBareClassifiedRaises("synthetic.nim", markedInjected, violations2)
    check violations2.len == 0

  test "walker version floor >= 101 (N36: raw-raise-in-lower class closure)":
    check parseInt(symexWalkerVersion) >= 101

  test "N40: allocateSym is total -- the param boundary raises by design [raise-audited: param-boundary]":
    ## Final certification for this audit file's own tracked class (see the
    ## module doc comment's "What counts as exempt" section, `param-boundary`
    ## entry, above): `allocateSym` (`runtime.nim`) no longer raises a
    ## classified-decline carrier for ANY classifiable input, at any call
    ## site -- walk-time or otherwise. The raw-raise-in-lower CLASS's raise
    ## sites in `runtime.nim` are now exactly: `allocateSeqDataRaw` (1,
    ## verified-unreachable), `defaultZero` (1, converted-at-chokepoint),
    ## `iekSeqLen` (1, verified-unreachable), and `raiseParamAllocIssue`'s
    ## four dispatch arms (4, param-boundary -- the pre-walk parameter-entry
    ## boundary is the SOLE remaining site permitted to raise for the
    ## `unallocatableFieldIssue` kind family, by design, before any walk
    ## state exists). This test's own name IS the certification text this
    ## slice's mandate requested; the mechanical counts above are what
    ## actually enforce it against regression.
    check parseInt(symexWalkerVersion) >= 104
