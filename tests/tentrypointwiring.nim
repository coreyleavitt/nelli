## RFC-0010 (stage-4 review) — permanent regression audit for the
## `parseEntryImpl` / `parseEntryImplWarned` wiring split in
## `src/nelli/symex.nim`.
##
## ----------------------------------------------------------------------------
## Background: the bug this test exists to prevent from recurring
## ----------------------------------------------------------------------------
## The round found `warnIncoherentSettings` (the macro-time check that warns
## when a `SymexSettings` is incoherent -- notably `arithChecks == {}`, which
## silently disables every arithmetic-defect fork) wired into only 2 of the 6
## symex entry macros. The fix introduced a chokepoint, `parseEntryImplWarned`
## (~symex.nim:1123), which wraps `warnIncoherentSettings` +
## `dsl_parser.parseEntryImpl`. The five WALKER-RUNNING entry macros
## (`symexFind`, `assertCoveredBy`, `concolicCollect`, `concolicFlip`,
## `symexFindAllWitnesses`; `symexForAll` transitively, via its call to
## `symexFindAllWitnesses`) now route through it. Five CACHE/DB HELPER macros
## (`symexCacheKeyForFn`, `saveSymexWitness`, `loadSymexWitnesses`,
## `saveSymexVerdict`, `loadSymexVerdict`) deliberately still call
## `parseEntryImpl` directly -- they never run the walker (they only build a
## cache key, or persist/load an already-computed result), so warning there
## would point at the wrong call site.
##
## That two-tier split was enforced by nothing but a doc comment. A future
## macro author who copy-pastes one of the five cache/DB macros -- which
## visibly call `parseEntryImpl` directly -- reproduces the original bug with
## zero compiler feedback: a new walker-running macro that bypasses
## `warnIncoherentSettings` compiles cleanly and silently ships. This test
## catches that mechanically: every run re-scans `symex.nim` for the bare
## identifier `parseEntryImpl` on a word boundary and fails if an occurrence
## turns up outside an approved declaration -- no compiler feedback is
## involved, and this guard only fires when the test itself actually runs
## (see the CI-leg note below for where that is and is not true today).
##
## ----------------------------------------------------------------------------
## Mechanism (same house scan-and-marker technique as the `*_audit.nim`
## siblings -- `tsymex_phase15_A2a_chokepoint_audit.nim`,
## `tsymex_r6_n27_placeholder_read_audit.nim`, et al.)
## ----------------------------------------------------------------------------
## The file is read once (`readFile`, NOT `staticRead` -- see the `symexSrc`
## comment below) and scanned line by line. Each line is attributed to the
## most recently seen top-level (column-0) `macro <name>` or `proc <name>`
## declaration; a whole-word occurrence of `parseEntryImpl` on that line is a
## call site (or a reference to one) belonging to that declaration. Comment
## lines (`#`/`##`, which is where every prose mention of the bare name
## lives) are skipped. The match is on the identifier itself, neither
## preceded nor followed by an identifier character -- NOT on a trailing
## `(` -- so it (a) can never match `parseEntryImplWarned`, whose next
## character after the shared prefix is `W`, not a non-identifier boundary,
## and (b) still catches a call split across lines, e.g.
## `parseEntryImpl\n    (fn, apiName, ...)`, where no single line contains the
## substring `parseEntryImpl(`. Known accepted gap: a string literal
## containing the bare word (e.g. a hypothetical log message) would also
## match and could false-positive; reliably excluding string/raw/triple-quoted
## literals needs a real Nim lexer, and no such literal exists in
## `symex.nim` today, so that complexity was judged not worth it here. If one
## is ever added, either reword it to avoid the bare identifier or extend
## this scanner then.
##
## Two independent assertions, deliberately not one:
##   1. every found call site's enclosing declaration is on `approvedCallers`
##      (catches a NEW unapproved site -- the regression this test exists for);
##   2. the found call sites are EXACTLY one per approved name, no more, no
##      fewer (catches an approved site silently disappearing or duplicating,
##      which would mean this audit's own inventory has drifted and needs a
##      deliberate update, not a silent pass).

import std/[unittest, strutils, os]
import audit_scan_utils

const
  symexPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "symex.nim"

let symexSrc = readFile(symexPath)
  ## Runtime `readFile`, not `staticRead`: `staticRead` embeds the file as a
  ## single C string literal, and symex.nim is ~97KB -- comfortably over
  ## MSVC's ~64KB string-literal limit (C2026) that already forced
  ## `tsymex_phase15_A2a_chokepoint_audit.nim` off `staticRead` for a bigger
  ## file (dsl_parser.nim, 486KB; see that file's N46 comment). This suite is
  ## Z3-free (no `import nelli/symex`) so it is not disqualified from any CI
  ## leg on that basis, and it dodges the same MSVC string-literal trap in
  ## case that ever becomes relevant. But being Z3-free was necessary, not
  ## sufficient: for most of this test's life no CI leg's test-discovery
  ## pattern named it, so it ran nowhere in CI despite compiling cleanly.
  ## Current state: `fuzzer-msvc.yaml` and `fuzzer-mingw.yaml` both discover
  ## it by explicit name (`tentrypointwiring` in their `Where-Object` match
  ## list, alongside `tlearnedstate`/`tcoverage`/etc.) -- that is the whole
  ## reason those two legs run it. `symex-mingw.yaml` does NOT run it: that
  ## leg derives its corpus purely from `tsymex_*`-named suites in
  ## `nelli.nimble`'s `test` task, and this file matches neither prefix.
  ## Registering this suite in `nelli.nimble` buys nothing on its own --
  ## no CI leg in this repo runs the `test` task at all (see
  ## `symex-mingw.yaml`'s own header); nimble registration only makes `nim
  ## exec` or a local `test` task invocation find it. The path is resolved at
  ## compile time via `currentSourcePath`; only the content read is deferred
  ## to when the test body runs.

const
  approvedCallers = [
    "parseEntryImplWarned",  # the chokepoint itself
    "symexCacheKeyForFn", "saveSymexWitness", "loadSymexWitnesses",
    "saveSymexVerdict", "loadSymexVerdict",
    "replayWitness",         # RFC-0005 S2: runs `fn`, never the walker
  ]
    ## The five cache/DB helper macros that legitimately call
    ## `parseEntryImpl` directly (they build a cache key or persist/load an
    ## already-computed result -- they never run the walker), plus the one
    ## call inside `parseEntryImplWarned` itself -- the wrapper every
    ## walker-running entry macro must route through instead.
    ##
    ## RFC-0005 S2 added `replayWitness`, deliberately: it parses `fn` only
    ## for its parameter `IRType`s (to classify witness fidelity against the
    ## same types `emitTyAndReader` rendered), then executes the REAL `fn` --
    ## it takes no `SymexSettings` and never runs the walker, so there is
    ## nothing for `parseEntryImplWarned` to warn about.

proc declNameAt(rawLine: string): string =
  ## If `rawLine` is a top-level (column-0) `macro <name>` or `proc <name>`
  ## declaration, returns `<name>`; otherwise "".
  ##
  ## Rounds 4-5 gap: this used to require the keyword be followed by a
  ## literal space (`"macro "`/`"proc "`), so `proc\tsneakyDecl(...)` (a tab
  ## after the keyword) was not recognised as a declaration at all -- a call
  ## inside it stayed attributed to whichever declaration came textually
  ## before it. Fixed by matching the bare keyword, then any RUN of
  ## whitespace (space or tab) before the name, rather than one hardcoded
  ## space character.
  for kw in ["macro", "proc"]:
    if rawLine.startsWith(kw) and rawLine.len > kw.len and
       rawLine[kw.len] in {' ', '\t'}:
      var i = kw.len
      while i < rawLine.len and rawLine[i] in {' ', '\t'}:
        inc i
      let start = i
      while i < rawLine.len and isIdentChar(rawLine[i]):
        inc i
      return rawLine[start ..< i]
  ""

proc hasBareCall(line: string, name: string): bool =
  ## True if `line` contains the bare identifier `name` on a word boundary --
  ## neither preceded nor followed by an identifier character. Deliberately
  ## does NOT require a trailing `(`: matching the identifier itself (rather
  ## than "identifier immediately followed by open-paren") is what catches a
  ## call split across lines, e.g.
  ##   parseEntryImpl
  ##       (fn, apiName, ...)
  ## where the call token and its `(` are on different lines and no single
  ## line contains the substring `name & "("`. The boundary check on BOTH
  ## sides still rejects `name` as a substring of a longer identifier, so a
  ## scan for `parseEntryImpl` can never match `parseEntryImplWarned`
  ## (immediately followed by `W`, an identifier character) or a hypothetical
  ## `xParseEntryImpl` (immediately preceded by an identifier character).
  var searchFrom = 0
  while true:
    let idx = line.find(name, searchFrom)
    if idx < 0: return false
    let precededOk = idx == 0 or not isIdentChar(line[idx - 1])
    let followIdx = idx + name.len
    let followedOk = followIdx >= line.len or not isIdentChar(line[followIdx])
    if precededOk and followedOk:
      return true
    searchFrom = idx + 1

type
  CallSite = object
    lineNo: int
    decl: string
    text: string

proc stripTrailingComment(line: string): string =
  ## Rounds 4-5 gap: `isCommentLine` (audit_scan_utils.nim, shared with other
  ## audit suites -- not edited here) only recognises a WHOLE-line comment,
  ## so a line like `foo()  # see parseEntryImpl` was not filtered by it and
  ## registered as a false-positive call site. Truncating at the first `#`
  ## before matching fixes that for this file's actual content.
  ##
  ## Tradeoff accepted, matching the gap `isCommentLine` already documents
  ## for whole-line comments: this is not a real Nim lexer, so a `#` that
  ## appears inside a string literal (e.g. a hypothetical log message
  ## containing `#`) would truncate the line too early and could hide a
  ## genuine call site after it. `symex.nim` has no such literal today; if
  ## one is ever added, either reword it or extend this to a real lexer.
  let idx = line.find('#')
  if idx < 0: line else: line[0 ..< idx]

proc scanCallSites(src: string): seq[CallSite] =
  var currentDecl = ""
  var lineNo = 0
  for rawLine in src.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if isCommentLine(trimmed):
      continue
    let decl = declNameAt(rawLine)
    if decl.len > 0:
      currentDecl = decl
    if hasBareCall(stripTrailingComment(rawLine), "parseEntryImpl"):
      result.add CallSite(lineNo: lineNo, decl: currentDecl, text: trimmed)

const wiringRule =
  "Rule: walker-running entry macros must call `parseEntryImplWarned`; " &
  "only the cache/DB helpers may call `parseEntryImpl` directly, because " &
  "they don't run the walker."

suite "entry-macro wiring — parseEntryImpl allow-list audit (RFC-0010)":

  test "every bare parseEntryImpl( call site in symex.nim is inside an approved macro/proc":
    let sites = scanCallSites(symexSrc)
    var violations: seq[string]
    var violatingDecls: seq[string]
      ## The actual declaration(s) that violated the rule -- NOT `sites[0]`,
      ## which is simply the first call site in file order (in practice
      ## always the approved chokepoint's own internal call) and names the
      ## wrong declaration in the closing advice below if used directly.
    for site in sites:
      if site.decl notin approvedCallers:
        violations.add "  line " & $site.lineNo & ": bare parseEntryImpl( call " &
          "inside `" & site.decl & "` is not on the approved allow-list\n    " &
          site.text
        if site.decl notin violatingDecls:
          violatingDecls.add site.decl
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " unapproved parseEntryImpl( call site(s) in src/nelli/symex.nim:\n"
      for v in violations: report.add v & "\n"
      let advice =
        if violatingDecls.len == 1:
          "If `" & violatingDecls[0] &
            "` is a genuinely new cache/DB helper that never runs the walker, " &
            "add it to `approvedCallers` in tests/tentrypointwiring.nim " &
            "deliberately; if it runs the walker, route it through " &
            "`parseEntryImplWarned` instead, per RFC-0010."
        else:
          "For each of `" & violatingDecls.join("`, `") &
            "`: if it is a genuinely new cache/DB helper that never runs the " &
            "walker, add it to `approvedCallers` in tests/tentrypointwiring.nim " &
            "deliberately; if it runs the walker, route it through " &
            "`parseEntryImplWarned` instead, per RFC-0010."
      report.add wiringRule & " " & advice
      checkpoint(report)
    check violations.len == 0

  test "the approved allow-list is exactly what's found — one call site per name, no drift":
    let sites = scanCallSites(symexSrc)
    var counts: seq[tuple[name: string, count: int]]
    for name in approvedCallers:
      var n = 0
      for site in sites:
        if site.decl == name: inc n
      counts.add (name, n)
    var violations: seq[string]
    for (name, n) in counts:
      if n != 1:
        violations.add "  expected exactly 1 parseEntryImpl( call site inside `" &
          name & "`, found " & $n
    # Also flag any site attributed to a name outside the allow-list, so this
    # test fails the same way test 1 does if run in isolation.
    for site in sites:
      if site.decl notin approvedCallers:
        violations.add "  line " & $site.lineNo & ": unexpected call site inside `" &
          site.decl & "`"
    if violations.len > 0:
      var report = "\nFound " & $violations.len & " allow-list drift violation(s):\n"
      for v in violations: report.add v & "\n"
      report.add wiringRule & " Update the `approvedCallers` allow-list in " &
        "tests/tentrypointwiring.nim only if this drift is deliberate " &
        "(e.g. a helper was renamed or removed) -- otherwise treat it as the " &
        "regression this audit exists to catch."
      checkpoint(report)
    check violations.len == 0
