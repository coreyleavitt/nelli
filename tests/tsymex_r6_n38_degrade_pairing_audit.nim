## N38 (fix-slice item 9, round-6 re-review) — permanent regression audit
## enforcing the `allocDegrade`+`freshDegradeName` PAIRING discipline.
##
## ----------------------------------------------------------------------------
## THE FINDING
## ----------------------------------------------------------------------------
## The CR-1c table (`runtime.nim`, above `allocDegrade`'s own definition)
## documents `allocDegrade` as the chokepoint carrier for allocation/sort-
## derivation failures; its reconstruction column says the paired site
## "almost always" does `allocateSym(ty, freshDegradeName(tag), pcOut)`
## immediately after. Nothing enforced that pairing mechanically — the two
## calls were two SEPARATE lines at every site, free to drift apart. This
## slice found the drift had already happened TWICE (items 3/4 of this same
## re-review): `storeSeqElem`'s val-kind-mismatch site and `seqElemAt`'s
## unsupported-elem-kind site both degraded to a BARE fixed Z3 const name
## (`"__storeSeqElemKindMismatch"` / `"__seqElemAtUnsupported"`), silently
## dropping `freshDegradeName`'s per-run uniquification and reopening the
## exact `(name, sort)` collision hazard `freshDegradeName` exists to close.
##
## `degradeAlloc(ty, kind, msg, tag)` (runtime.nim, defined immediately after
## `freshDegradeName`) now fuses the two calls into one, and this file is the
## permanent backstop: it scans `runtime.nim` for the RAW two-call idiom
## re-emerging at any site outside `degradeAlloc`'s own body, and pins how
## many of the file's `allocDegrade` sites have been migrated onto the new
## helper.
##
## ----------------------------------------------------------------------------
## Scope: what this audits and what it deliberately does NOT
## ----------------------------------------------------------------------------
## SCANNED: `runtime.nim` only. `runtime_heap.nim`'s `allocDegrade` sites
## "handle their own" pairing — heap degrades follow `allocDegrade` + a fresh
## `allocateSym` with an env-rebind + `forkPathTainted`/
## `drainPendingLowerEffects` (`Path`-scoped fork/drain machinery), a
## DIFFERENT taint sink than the bare `freshDegradeName` counter `degradeAlloc`
## wraps — forcing heap sites onto `degradeAlloc`'s signature would be a
## carrier-choice regression, not a fix. Out of scope for this audit, same as
## N36's own file-scoping decisions.
##
## NOT SCANNED / deliberately exempt, by DESIGN rather than marker:
##   - `degradeAlloc`'s own body (the ONE site meant to contain exactly the
##     two-call shape) — tagged `# [pairing-audited: ...]` so the scanner's
##     own violation-detection logic does not have to special-case it.
##   - The other two CR-1c carriers (R1 placeholder funnel —
##     `placeholderBoolDecline`; `degradeStrArm`'s own chokepoint) — neither
##     pairs `freshDegradeName` with `allocDegrade` at all (R1 pairs it with
##     `declinePlaceholderInLower`; `degradeStrArm` pairs it with a single
##     `loweringDegradeErrors.add`/`loweringDidDegrade` write at the TOP of
##     the proc, shared across many `freshDegradeName` calls in the `case`
##     dispatch below it) — this audit's pattern requires BOTH `allocateSym(`
##     AND `freshDegradeName(` to appear textually within the lookahead
##     window of an `allocDegrade(` call, so neither sibling carrier's shape
##     can match it (verified empirically below — see the "sibling carriers
##     never trip this scanner" test).
##
## ----------------------------------------------------------------------------
## `staticRead` vs `readFile` (toolchain note, N27/N36 precedent)
## ----------------------------------------------------------------------------
## Reads `runtime.nim` at TEST RUNTIME (`readFile`), path resolved at compile
## time (`currentSourcePath`) — same MSVC C2026 avoidance N27/N36 document.
import std/[unittest, strutils, os]
import nelli/smt/canonicalize
import audit_scan_utils

const
  runtimeNimPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                   "smt" / "runtime.nim"

  pairingAuditMarker = "# [pairing-audited:"
  lookaheadWindow = 20
    ## Generous enough to span the longest real doc-comment gap between an
    ## `allocDegrade(...)` call and its paired `allocateSym(...)` call in this
    ## file today (the widest observed gap, `iekField`'s unsupported-kind
    ## site, is ~12 lines of explanatory comment) without crossing into an
    ## unrelated LATER proc's own unrelated pairing.

type
  Violation = object
    lineNo:   int
    lineText: string

proc looksLikeTopLevelDef(trimmed: string): bool =
  ## A new top-level `proc`/`template`/`macro`/`type` definition (column-0 in
  ## the original, `strip()`ped here) ends the lookahead window early — an
  ## `allocDegrade` call's paired `allocateSym` (if any) is always in the SAME
  ## routine body, never spilled into the next definition.
  trimmed.startsWith("proc ") or trimmed.startsWith("template ") or
    trimmed.startsWith("macro ") or trimmed.startsWith("type ") or
    trimmed.startsWith("include ")

proc scanForUnpairedAllocDegrade(contents: string): seq[Violation] =
  ## A VIOLATION is an `allocDegrade(` call whose line does NOT carry the
  ## `[pairing-audited: ...]` exemption, followed — within `lookaheadWindow`
  ## lines, and before the next top-level definition — by a line containing
  ## BOTH `allocateSym(` AND `freshDegradeName(`. That combination is exactly
  ## the split two-call idiom `degradeAlloc` exists to replace; finding it
  ## means a new (or reintroduced) site bypassed the pairing helper.
  let lines = contents.splitLines()
  var i = 0
  while i < lines.len:
    let trimmed = lines[i].strip()
    if trimmed.contains("allocDegrade(") and not isCommentLine(trimmed) and
       not lines[i].contains(pairingAuditMarker):
      var j = i + 1
      var foundPair = false
      while j < lines.len and j < i + 1 + lookaheadWindow:
        let lj = lines[j].strip()
        if looksLikeTopLevelDef(lj):
          break
        if lj.contains("allocateSym(") and lj.contains("freshDegradeName("):
          foundPair = true
          break
        inc j
      if foundPair:
        result.add Violation(lineNo: i + 1, lineText: lines[i])
    inc i

proc countDegradeAllocCallSites(contents: string): int =
  ## Counts CALL sites only (excludes the `proc degradeAlloc(...)`
  ## definition line itself, which contains `degradeAlloc(` as its own
  ## signature, not a call).
  for rawLine in contents.splitLines():
    let trimmed = rawLine.strip()
    if trimmed.contains("degradeAlloc(") and
       not trimmed.startsWith("proc degradeAlloc"):
      inc result

suite "symex N38 — allocDegrade + freshDegradeName pairing audit":

  test "zero unpaired allocDegrade+allocateSym(...freshDegradeName...) sites outside degradeAlloc's own body":
    let src = readFile(runtimeNimPath)
    let violations = scanForUnpairedAllocDegrade(src)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " allocDegrade(...) call(s) immediately paired with a raw " &
        "allocateSym(...freshDegradeName(...)...) rather than routed " &
        "through degradeAlloc:\n"
      for v in violations:
        report.add "  runtime.nim:" & $v.lineNo & ":  " & v.lineText.strip() & "\n"
      report.add "Route through degradeAlloc(ty, kind, msg, tag) instead, " &
        "or -- if genuinely a different carrier -- mark the allocDegrade " &
        "line `# [pairing-audited: <reason>]` after review."
      checkpoint(report)
    check violations.len == 0

  test "degradeAlloc has been adopted at >= 13 call sites (fix-slice item 9 migration floor)":
    ## Floor, not exact-equality (mirrors N36's tolerant version-floor idiom
    ## elsewhere in this file's own family): a FUTURE slice migrating MORE
    ## sites onto `degradeAlloc` should never have to touch this pin, only a
    ## regression (sites reverting to the raw two-call form) would drop the
    ## count below the floor -- which the scanner test above would ALSO catch
    ## directly, so this is a redundant, cheap second signal.
    let count = countDegradeAllocCallSites(readFile(runtimeNimPath))
    checkpoint("degradeAlloc call sites: " & $count)
    check count >= 13

  test "sibling carriers never trip this scanner (R1 placeholder funnel, degradeStrArm)":
    ## Direct proof the scanner's "requires BOTH allocateSym( AND
    ## freshDegradeName( in the lookahead" rule does not false-positive on
    ## the OTHER two CR-1c carriers, which also call `freshDegradeName` but
    ## never pair it with `allocDegrade`.
    let r1Shape = "template placeholderBoolDecline(recv: SymVal, opDesc, tag: string): SymVal =\n" &
      "  declinePlaceholderInLower(recv, \"\", opDesc)\n" &
      "  var freshPCD: seq[Z3Bool]\n" &
      "  allocateSym(tBool(), freshDegradeName(tag), freshPCD)\n"
    check scanForUnpairedAllocDegrade(r1Shape).len == 0
    let strArmShape = "proc degradeStrArm(e: IRExpr, kind: SymexErrorKind, msg: string): SymVal =\n" &
      "  loweringDegradeErrors.add SymexErrorInfo(kind: kind, severity: sevError, msg: msg)\n" &
      "  loweringDidDegrade = true\n" &
      "  var fresh: seq[Z3Bool]\n" &
      "  case e.kind\n" &
      "  of iekStrAt:\n" &
      "    allocateSym(tInt(8, signed = false), freshDegradeName(\"__strArmDegrade\"), fresh)\n"
    check scanForUnpairedAllocDegrade(strArmShape).len == 0

  test "house scanner demonstration: an injected split allocDegrade/allocateSym(freshDegradeName) pair trips the audit, then reverts clean via degradeAlloc":
    ## Mirrors N36's own red/green self-demonstration (in-memory injection,
    ## never a file mutation, so this test never leaves the tree dirty).
    let injected =
      "    allocDegrade(feUnsupportedOp, \"synthetic split-idiom demo\")\n" &
      "    var fresh: seq[Z3Bool]\n" &
      "    allocateSym(tBool(), freshDegradeName(\"__syntheticDemo\"), fresh)\n"
    check scanForUnpairedAllocDegrade(injected).len == 1
    let migrated =
      "    degradeAlloc(tBool(), feUnsupportedOp, \"synthetic split-idiom demo\",\n" &
      "                 \"__syntheticDemo\")\n"
    check scanForUnpairedAllocDegrade(migrated).len == 0
    let markedExempt =
      "    allocDegrade(feUnsupportedOp, \"synthetic split-idiom demo\")  # [pairing-audited: synthetic demonstration]\n" &
      "    var fresh: seq[Z3Bool]\n" &
      "    allocateSym(tBool(), freshDegradeName(\"__syntheticDemo\"), fresh)\n"
    check scanForUnpairedAllocDegrade(markedExempt).len == 0

  test "walker version floor >= 119 (fix-slice items 1/2/5/7a landed alongside this audit)":
    check parseInt(symexWalkerVersion) >= 119
