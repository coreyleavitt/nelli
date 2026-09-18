## Issue #163 review R11 -- permanent regression audit for the range-invariant
## TWO-OBLIGATION contract every `range[lo..hi]`-typed value carries wherever
## it is materialized from a backing store:
##   (a) CONSTRAINT -- assert the symbol lies in `[lo,hi]` on the solver path
##       (`rangeCondsIfNeeded`/`bvRangeConds`, `runtime.nim`). Missing => the
##       solver can pick an illegal value => a false `sxSat`.
##   (b) WITNESS CLAMP -- clamp the reconstructed CONCRETE value read back out
##       of an already-solved model (`clampWitnessField`/`clampToDeclaredRange`,
##       `clampWitnessFieldsDeep`, `runtime.nim`). Missing => a `RangeDefect`
##       raised inside the CALLER's OWN process when the witness materializes.
##
## Same TOT-1 institutionalization rationale as `tsymex_r6_n36_raise_class_
## audit.nim` (read that file first -- this one matches its structure, marker
## style, and self-test discipline deliberately): a slice-close grep proves
## the CURRENT inventory is complete once; it catches no future regression on
## its own. This test makes forgetting the obligation at an EIGHTH
## backing-store shape impossible to do silently.
##
## ----------------------------------------------------------------------------
## Why this exists -- six prior instances, one root cause, found separately
## ----------------------------------------------------------------------------
## This exact obligation has been forgotten at a NEW backing-store shape SIX
## times, each found independently and each shipped green in between:
##   W2  -- `seq[range[lo..hi]]` elements never clamped at extraction.
##   W4  -- `ref object` fields sharing another instance's field-split heap
##          array reconstructed unclamped.
##   R3  -- a ref-to-VARIANT arm field reached neither the solver-path
##          constraint nor the witness clamp.
##   R4  -- `Table[string, range[lo..hi]]` values: `extractTableEntries` never
##          checked `hasRange`, unlike its sibling extractors.
##   R17 -- R3's own fix was incomplete: a ranged arm field that was WRITTEN
##          (not just read) still reached the caller unclamped, because the
##          active-arm override unconditionally overwrote the clamp with a
##          fresh, unclamped `heapSelect`.
##   W8  -- `allocateSym`'s `isIntOffset` arms allocate a Z3-Int-sorted
##          `svInt` directly rather than the type-driven BV default, and the
##          then-existing helper silently no-op'd for anything that wasn't a
##          BV kind -- the exact case it existed to cover.
## R11 (commit a663589) finally centralized the logic into two helpers in
## `src/nelli/smt/runtime.nim`: `rangeCondsIfNeeded` (beside `bvRangeConds`,
## the CONSTRAINT half) and `clampWitnessField` (beside `clampToDeclaredRange`,
## the WITNESS-CLAMP half), plus `clampWitnessFieldsDeep` (R8, recursive
## nested-field clamp) and `forkAssignRangeCheck` (R22, the plain-local
## assignment RangeDefect fork). R11's own author flagged the remaining hole
## honestly: the helpers make the right thing cheap and obvious, but nothing
## MECHANICALLY forces a new materialization site to call them. A seventh
## backing-store shape could still skip both and compile fine. This file
## closes that gap for the two RAW primitives the helpers wrap.
##
## ----------------------------------------------------------------------------
## Scan vocabulary chosen, and why (honesty: scope this audit CAN cover)
## ----------------------------------------------------------------------------
## CHOSEN: scan for direct, non-definition calls to the two RAW primitives
## the helpers wrap -- `bvRangeConds(` and `clampToDeclaredRange(` -- across
## every file that is part of `runtime.nim`'s own compiled unit (itself plus
## every file it `include`s: `runtime_strings.nim`, `runtime_floats.nim`,
## `runtime_exceptions.nim`, `runtime_closures.nim`, `runtime_heap.nim`).
## Both primitives are module-private (no `*`), so this file list is
## EXHAUSTIVE for who could possibly call them -- not a heuristic guess.
##
## Rationale for narrowing to exactly this: a direct call to a raw primitive,
## found OUTSIDE the two helpers' own bodies, means one of exactly two
## things -- either (1) it is the helpers' own internal implementation
## (`rangeCondsIfNeeded` calling `bvRangeConds`; `clampWitnessField` calling
## `clampToDeclaredRange`) -- structurally always safe, no adjudication ever
## needed -- or (2) it is a call site that BYPASSED the helper. Every (2)
## site is either a previously-reviewed, legitimate exception (the
## `extractSeqElements`/`extractTableEntries` "bare-int64-preinsert" case --
## see below) or a genuine miss. This is a MECHANICALLY exact scan: no
## judgment call about what "looks like" a materialization site, just "did
## this line call the primitive, and is the calling proc on the reviewed
## list."
##
## REJECTED (considered, scoped out): widening the scan to the
## MATERIALIZATION VERBS themselves (`liftBV`, `heapSelect`, `allocateSym`'s
## arms, `extractLeaf`, `select(`) to try to catch a site that never calls
## either raw primitive OR either helper at all -- the true "eighth
## instance" shape R11's author actually worried about. This was rejected as
## NOT precisely checkable by a text scan: proving "this materialization
## site's caller ALSO calls `rangeCondsIfNeeded`/`clampWitnessField`
## somewhere on its path" requires control-flow analysis this scanner does
## not have. A text scan for `select(`/`heapSelect`/`liftBV` alone produces
## dozens of matches with no reliable way to tell which ones need the
## obligation and which don't (most `select(` calls are for NON-range types
## entirely) -- exactly the "marker-spammed and dies" failure mode this
## audit must avoid. A narrower gate that genuinely works beats a broad one
## that misfires.
##
## NOT SCANNED, deliberately:
##   - `dsl_typebridge.nim`/`dsl_parser.nim`: these run at MACRO/parse time,
##     computing `hasRange`/`rangeLo`/`rangeHi` on the `IRType` itself. They
##     never hold a `SymVal`, a `Z3Model`, or a `RawWitness`, and cannot call
##     either raw primitive (both are private to `runtime.nim`'s own compiled
##     unit) -- confirmed empirically, not assumed (see the accompanying
##     investigation: neither identifier appears in either file). The
##     obligation these two files owe is a DIFFERENT one (getting `hasRange`
##     itself right), already covered by `tsymex_163rev_range_bounds`,
##     `tsymex_163rev_enum_domain`, `tsymex_163rev_enum_positions`, etc.
##   - The CONCOLIC interval-domain `hasRange` consumers (`runtime.nim`
##     ~12971-13163, `interval(p.rangeLo, p.rangeHi)`): a parallel,
##     non-Z3 representation for the SAME declared bound, used by concolic
##     execution rather than solver-path/witness reconstruction. It never
##     calls either raw primitive (confirmed by the same full-file grep) and
##     has its own dedicated coverage (`tsymex_163rev_concolic_modes`,
##     R6). Out of scope for a Z3-constraint/witness-clamp audit specifically.
##
## ----------------------------------------------------------------------------
## Marker discipline -- and why it differs from N36's inline-comment style
## ----------------------------------------------------------------------------
## N36's audit exempts a matched line by requiring a literal, IN-SOURCE
## trailing comment (`# [raise-audited: <reason>]`). This audit was written
## under a HARD constraint that N36's was not: `src/nelli/smt/runtime.nim`,
## `runtime_heap.nim`, and `dsl_parser.nim` are concurrently owned by sibling
## work this same round, and this task is explicitly TEST-ONLY -- adding even
## a pure comment to those files is a source edit and out of scope here.
##
## The investigation below found exactly 8 direct call sites, all inside
## `runtime.nim`, all already legitimate (see inventory), and NONE currently
## carry an inline marker (none existed before this audit). Rather than ship
## a permanently-RED gate demanding a source edit this task cannot make, the
## exemption ledger for the CURRENT inventory lives HERE, in the test, keyed
## by (primitive, enclosing top-level proc name) -- functionally identical
## to a marker (a human reviewed this exact site and recorded why it's safe;
## a drift in either direction re-trips the gate) without touching the
## sibling-owned files. This is a deliberate adaptation, not a shortcut: it
## is exactly as precise as an inline marker for a call site that already
## exists, and is recorded as pinned per-proc COUNTS below, so an unexpected
## additional call inside an already-allowed proc still trips the gate.
##
## Going forward, a NEW call site can be exempted EITHER way: (1) add an
## inline `# [range-invariant: <reason>]` marker directly on the call
## line (this scanner recognizes it exactly like N36 recognizes
## `# [raise-audited: ...]`), or (2) get the enclosing proc added to the
## allowlist below after review, in the same commit that bumps the pinned
## counts. Whichever path is used, the count assertions below force a human
## to touch this file deliberately -- silence is never an option.
##
## Reason vocabulary (free-form after the prefix, two families seen so far):
##   - `helper-internal` -- the raw primitive's OWN wrapping helper calling
##     it (`rangeCondsIfNeeded` -> `bvRangeConds`; `clampWitnessField` ->
##     `clampToDeclaredRange`). Structurally always safe.
##   - `bare-int64-preinsert` -- `extractSeqElements`/`extractTableEntries`
##     clamp a bare `int64` pulled straight off the Z3 model BEFORE any
##     witness key exists to hand `clampWitnessField` (there is no
##     already-keyed `RawWitness` entry yet -- the map write happens on the
##     very next line, using the just-clamped value). Calling the flat
##     `clampToDeclaredRange` directly, then assigning, is the only order
##     that works here; routing through `clampWitnessField` would require
##     writing an unclamped value first and immediately re-patching it,
##     which is possible but strictly less clear than the current form.
##
## ----------------------------------------------------------------------------
## Site inventory as of this writing (walker v138)
## ----------------------------------------------------------------------------
## `bvRangeConds(`: 1 direct call site, all in `runtime.nim`:
##   - `rangeCondsIfNeeded` (1) -- helper-internal.
## `clampToDeclaredRange(`: 7 direct call sites, all in `runtime.nim`:
##   - `clampWitnessField`   (2) -- helper-internal.
##   - `extractTableEntries` (1) -- bare-int64-preinsert.
##   - `extractSeqElements`  (4, one per BV width 8/16/32/64) --
##     bare-int64-preinsert.
## Total: 8 direct call sites, ZERO unadjudicated (the audit is CLEAN on the
## current tree without any source edit -- see the marker-discipline note
## above for why). `runtime_strings.nim`/`runtime_floats.nim`/
## `runtime_exceptions.nim`/`runtime_closures.nim`/`runtime_heap.nim` all
## call the WRAPPING HELPERS (`rangeCondsIfNeeded`/`clampWitnessField`/
## `clampWitnessFieldsDeep`), never a raw primitive directly -- confirmed
## empirically (grep for the two exact identifiers across all six files
## returns exactly these 8 lines, all in `runtime.nim`).
## A count drift in EITHER direction means a site was added, removed, or
## silently duplicated/split since this audit was written, and must be
## re-examined by a human.
import std/[unittest, strutils, os]
import nelli/smt/canonicalize
import audit_scan_utils

const
  runtimeNimPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                   "smt" / "runtime.nim"
  runtimeStringsNimPath = currentSourcePath.parentDir() / ".." / "src" /
                          "nelli" / "smt" / "runtime_strings.nim"
  runtimeFloatsNimPath = currentSourcePath.parentDir() / ".." / "src" /
                         "nelli" / "smt" / "runtime_floats.nim"
  runtimeExceptionsNimPath = currentSourcePath.parentDir() / ".." / "src" /
                             "nelli" / "smt" / "runtime_exceptions.nim"
  runtimeClosuresNimPath = currentSourcePath.parentDir() / ".." / "src" /
                           "nelli" / "smt" / "runtime_closures.nim"
  runtimeHeapNimPath = currentSourcePath.parentDir() / ".." / "src" /
                       "nelli" / "smt" / "runtime_heap.nim"
    ## Resolved at COMPILE time (pure path arithmetic on `currentSourcePath`
    ## -- no file content embedded), read at TEST RUNTIME (same
    ## `readFile`-not-`staticRead` MSVC C2026 avoidance N27/N36 already
    ## document).

  bvCallSubstr = "bvRangeConds("
  bvDefPrefix = "proc bvRangeConds("
  clampCallSubstr = "clampToDeclaredRange("
  clampDefPrefix = "proc clampToDeclaredRange("
  auditMarker = "# [range-invariant:"

type
  AllowedSite = tuple[primitive: string, procName: string, reason: string]

const
  ## The current-inventory exemption ledger -- see the marker-discipline
  ## section above for why this lives here instead of as inline comments.
  allowedSites: array[4, AllowedSite] = [
    ("bvRangeConds", "rangeCondsIfNeeded", "helper-internal"),
    ("clampToDeclaredRange", "clampWitnessField", "helper-internal"),
    ("clampToDeclaredRange", "extractTableEntries", "bare-int64-preinsert"),
    ("clampToDeclaredRange", "extractSeqElements", "bare-int64-preinsert"),
  ]

proc isAllowed(primitive, procName: string): bool =
  for site in allowedSites:
    if site.primitive == primitive and site.procName == procName:
      return true
  false

type
  CallSite = object
    file:     string
    procName: string
    lineNo:   int
    lineText: string

proc isTopLevelRoutineLine(rawLine: string): bool =
  ## A genuine top-level (column-0) `proc`/`func` declaration line -- the
  ## codebase has zero NESTED proc definitions inside the scanned region
  ## (verified), so tracking only column-0 declarations is exact here: a
  ## call's enclosing top-level proc is always the most recent such line
  ## above it.
  rawLine.startsWith("proc ") or rawLine.startsWith("func ")

proc extractProcName(rawLine: string): string =
  ## `rawLine` satisfies `isTopLevelRoutineLine`. Take the identifier
  ## immediately after the keyword, stopping at the first non-identifier
  ## character (`*`, `(`, `:`, space, backtick, ...).
  let spaceIdx = rawLine.find(' ')
  var i = spaceIdx + 1
  let start = i
  while i < rawLine.len and isIdentChar(rawLine[i]): inc i
  rawLine[start ..< i]

proc scanCallSites(fname, contents, callSubstr, defPrefix: string):
    seq[CallSite] =
  var currentProc = "<top-level, before any proc>"
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    if isTopLevelRoutineLine(rawLine):
      currentProc = extractProcName(rawLine)
    let trimmed = rawLine.strip()
    if trimmed.len == 0 or isCommentLine(trimmed):
      continue
    if trimmed.startsWith(defPrefix):
      continue    ## the primitive's own definition line, not a call.
    let idx = trimmed.find(callSubstr)
    if idx < 0:
      continue
    if idx > 0 and isIdentChar(trimmed[idx - 1]):
      continue    ## part of a longer identifier (word-boundary guard).
    result.add CallSite(file: fname, procName: currentProc, lineNo: lineNo,
                         lineText: rawLine)

proc violatingSites(sites: seq[CallSite], primitive: string): seq[CallSite] =
  for s in sites:
    if s.lineText.contains(auditMarker):
      continue    ## inline marker path (for a FUTURE site -- see header).
    if isAllowed(primitive, s.procName):
      continue    ## reviewed-proc allowlist path (current inventory).
    result.add s

let allFiles = [
  ("src/nelli/smt/runtime.nim", runtimeNimPath),
  ("src/nelli/smt/runtime_strings.nim", runtimeStringsNimPath),
  ("src/nelli/smt/runtime_floats.nim", runtimeFloatsNimPath),
  ("src/nelli/smt/runtime_exceptions.nim", runtimeExceptionsNimPath),
  ("src/nelli/smt/runtime_closures.nim", runtimeClosuresNimPath),
  ("src/nelli/smt/runtime_heap.nim", runtimeHeapNimPath),
]

suite "symex R11 — permanent range-invariant regression audit":

  test "zero unadjudicated direct `bvRangeConds(` calls outside the reviewed allowlist (all six files)":
    var allSites: seq[CallSite]
    for (label, path) in allFiles:
      allSites.add scanCallSites(label, readFile(path), bvCallSubstr, bvDefPrefix)
    let violations = violatingSites(allSites, "bvRangeConds")
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " unadjudicated direct call(s) to `bvRangeConds` (the raw " &
        "solver-path CONSTRAINT primitive `rangeCondsIfNeeded` wraps):\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & "  (in " & v.procName &
          "):  " & v.lineText.strip() & "\n"
      report.add "This bypasses the centralized helper -- either route " &
        "through `rangeCondsIfNeeded` instead, or if this is a genuinely " &
        "new legitimate direct use, tag the line `# [range-invariant: " &
        "<reason>]` and record it in this file's inventory/allowlist."
      checkpoint(report)
    check violations.len == 0

  test "zero unadjudicated direct `clampToDeclaredRange(` calls outside the reviewed allowlist (all six files)":
    var allSites: seq[CallSite]
    for (label, path) in allFiles:
      allSites.add scanCallSites(label, readFile(path), clampCallSubstr, clampDefPrefix)
    let violations = violatingSites(allSites, "clampToDeclaredRange")
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " unadjudicated direct call(s) to `clampToDeclaredRange` (the raw " &
        "witness-CLAMP primitive `clampWitnessField` wraps):\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & "  (in " & v.procName &
          "):  " & v.lineText.strip() & "\n"
      report.add "This bypasses the centralized helper -- either route " &
        "through `clampWitnessField`/`clampWitnessFieldsDeep` instead, or " &
        "if this is a genuinely new legitimate direct use (e.g. another " &
        "bare-int64-preinsert shape), tag the line `# [range-invariant: " &
        "<reason>]` and record it in this file's inventory/allowlist."
      checkpoint(report)
    check violations.len == 0

  test "pinned inventory: bvRangeConds 1 call (rangeCondsIfNeeded, helper-internal), all in runtime.nim":
    ## A count drift means a site was added, removed, or silently
    ## duplicated/split since this audit was written -- re-examine by hand
    ## (bump this count deliberately, in the same commit as the review).
    var byFile: seq[(string, int)]
    var byProc: seq[(string, int)]
    for (label, path) in allFiles:
      let sites = scanCallSites(label, readFile(path), bvCallSubstr, bvDefPrefix)
      byFile.add (label, sites.len)
      for s in sites:
        var found = false
        for i in 0 ..< byProc.len:
          if byProc[i][0] == s.procName:
            byProc[i][1] += 1
            found = true
        if not found: byProc.add (s.procName, 1)
    checkpoint("bvRangeConds by file: " & $byFile & "  by proc: " & $byProc)
    check byFile[0][1] == 1               ## runtime.nim
    for i in 1 ..< byFile.len:
      check byFile[i][1] == 0             ## the five `include`d siblings
    check byProc.len == 1
    check byProc[0][0] == "rangeCondsIfNeeded"
    check byProc[0][1] == 1

  test "pinned inventory: clampToDeclaredRange 7 calls (clampWitnessField 2, extractTableEntries 1, extractSeqElements 4), all in runtime.nim":
    var byFile: seq[(string, int)]
    var byProc: seq[(string, int)]
    for (label, path) in allFiles:
      let sites = scanCallSites(label, readFile(path), clampCallSubstr, clampDefPrefix)
      byFile.add (label, sites.len)
      for s in sites:
        var found = false
        for i in 0 ..< byProc.len:
          if byProc[i][0] == s.procName:
            byProc[i][1] += 1
            found = true
        if not found: byProc.add (s.procName, 1)
    checkpoint("clampToDeclaredRange by file: " & $byFile & "  by proc: " & $byProc)
    check byFile[0][1] == 7                ## runtime.nim
    for i in 1 ..< byFile.len:
      check byFile[i][1] == 0              ## the five `include`d siblings
    var perProc: seq[(string, int)]
    for p in byProc: perProc.add p
    var clampWitnessFieldCount, extractTableEntriesCount, extractSeqElementsCount: int
    for (name, count) in perProc:
      case name
      of "clampWitnessField": clampWitnessFieldCount = count
      of "extractTableEntries": extractTableEntriesCount = count
      of "extractSeqElements": extractSeqElementsCount = count
      else: discard
    check clampWitnessFieldCount == 2
    check extractTableEntriesCount == 1
    check extractSeqElementsCount == 4
    check clampWitnessFieldCount + extractTableEntriesCount +
          extractSeqElementsCount == byFile[0][1]   ## no fifth proc appeared

  test "R11 house scanner demonstration: an injected unmarked call in an unreviewed proc trips the audit; a marker OR allowlisting reverts it clean":
    ## Mirrors N36's own red/green self-demonstration -- in-memory injection
    ## only (never a file mutation), so this test cannot leave the tree
    ## dirty regardless of outcome, and cannot rot into a no-op scanner.
    let injectedUnmarked =
      "proc bogusNewMaterializationSite(x: int64, ty: IRType): int64 =\n" &
      "  result = clampToDeclaredRange(x, ty)\n"
    let sitesUnmarked = scanCallSites("synthetic.nim", injectedUnmarked,
                                       clampCallSubstr, clampDefPrefix)
    check sitesUnmarked.len == 1
    check violatingSites(sitesUnmarked, "clampToDeclaredRange").len == 1

    # Fix path 1: an inline marker on the call line.
    let injectedMarked =
      "proc bogusNewMaterializationSite(x: int64, ty: IRType): int64 =\n" &
      "  result = clampToDeclaredRange(x, ty)  # [range-invariant: synthetic demonstration]\n"
    let sitesMarked = scanCallSites("synthetic.nim", injectedMarked,
                                     clampCallSubstr, clampDefPrefix)
    check sitesMarked.len == 1
    check violatingSites(sitesMarked, "clampToDeclaredRange").len == 0

    # Fix path 2: the SAME unmarked call, now inside an already-reviewed
    # (allowlisted) proc name instead -- demonstrates the current-inventory
    # exemption path this file's own 8 real sites rely on.
    let injectedAllowlistedProc =
      "proc extractTableEntries(x: int64, ty: IRType): int64 =\n" &
      "  result = clampToDeclaredRange(x, ty)\n"
    let sitesAllowlisted = scanCallSites("synthetic.nim", injectedAllowlistedProc,
                                          clampCallSubstr, clampDefPrefix)
    check sitesAllowlisted.len == 1
    check violatingSites(sitesAllowlisted, "clampToDeclaredRange").len == 0

  test "R11 house scanner demonstration: the primitive's own definition line is never counted as a call":
    let defOnly = "proc clampToDeclaredRange(v: int64, ty: IRType): int64 =\n" &
                  "  if v < ty.rangeLo: ty.rangeLo\n" &
                  "  elif v > ty.rangeHi: ty.rangeHi\n" &
                  "  else: v\n"
    let sites = scanCallSites("synthetic.nim", defOnly, clampCallSubstr, clampDefPrefix)
    check sites.len == 0

  test "walker version floor >= 138 (#162 slice 5: range bounds live on the type, not just the param)":
    check parseInt(symexWalkerVersion) >= 138
