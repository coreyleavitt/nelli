## RFC-parser-normalization (#146), Cluster N, slice N2 — full `dsl_parser.nim`
## migration onto the N1 nil-core, plus a PERMANENT regression audit.
##
## ----------------------------------------------------------------------------
## Why a permanent test, not a one-time grep (TOT-1 rationale, cited verbatim
## per the RFC's round-2 institutionalization decision)
## ----------------------------------------------------------------------------
## A slice-close grep audit proves the inventory was complete ONCE, at the
## moment it was run. It catches no future regression: nothing stops a later
## edit from reintroducing a bare `impl.kind == nnkProcDef` check, a narrow
## `{nnkProcDef, nnkFuncDef}` set literal, or an `nskProc`/`nskFunc` symbol-
## kind gate at some new or existing call site. Round 1 of this RFC found
## exactly that pattern already: `799b0bc` widened 19 sites and was believed
## complete, but a LATER grep (this RFC, round 1) found three more that had
## been added or missed since. The fix institutionalized here: the audit
## becomes a committed, compile-time-enforced test (`staticRead` + pure-Nim
## string scanning) that runs on every future compile of the test suite, not
## a discipline that has to be remembered and re-run by hand.
##
## ----------------------------------------------------------------------------
## What this test scans, and what it deliberately does not
## ----------------------------------------------------------------------------
## `staticRead`s the source files whose grep-based site inventory (this slice)
## found real resolution/membership sites over routine-kind vocabulary:
##   - src/nelli/smt/dsl_parser.nim  (the migration target — 11 sites fixed)
##   - src/nelli/symex.nim           (N1 migrated its 9 entry macros; the
##     scan is regression insurance, not a fix — N1 already left it clean)
##   - src/nelli/smt/canonicalize.nim (grep matched this file, but only in
##     PROSE — the N0 slice-changelog doc comment quotes the old bare gates
##     as history; there is no live code site here. Scanned anyway: cheap,
##     and it means a future *code* addition here is covered too.)
##
## Standing, DELIBERATELY UNSCANNED exclusions (RFC §Non-goals — a different
## subsystem's own routine-kind vocabulary, out of this RFC's scope):
##   - src/nelli/coverage.nim:292 — `expectKind procDef, {nnkProcDef,
##     nnkFuncDef, nnkLambda}`. Coverage instrumentation's own three-kind
##     set; unrelated to the symex parser boundary this RFC hardens.
##   - src/nelli/mutation.nim:123 — `expectKind originalLambda, {nnkLambda,
##     nnkProcDef, nnkDo}`. Mutation testing's own three-kind set; same
##     rationale. Also: neither set is the narrow `{nnkProcDef, nnkFuncDef}`
##     two-element literal this audit's pattern (a) matches, so even an
##     incidental future scan of these files would not flag them today —
##     they are excluded by file, not merely by accident of pattern shape.
##
## ----------------------------------------------------------------------------
## The three banned patterns (source-line, not AST-level — pure string scan,
## deliberately simple: this test must stay readable by inspection)
## ----------------------------------------------------------------------------
##   (a) an inline two-element set literal `{nnkProcDef, nnkFuncDef}` (either
##       member order) OUTSIDE the `walkableRoutineKinds` const definition
##       line itself. Matches bare `==`/`!=`/`in`/`notin` membership tests
##       AND `expectKind` calls that spell the set out inline instead of
##       naming `walkableRoutineKinds`. Deliberately does NOT match the
##       wider N3-scoped "routine-shaped node" sets (the 7-elem closure-call
##       family and the 6-elem scanner-scope-boundary family) — those carry
##       more than two members, so the exact two-element substring never
##       matches them. N3 (a later, separate slice) owns reconciling those;
##       flagging them here would be scope creep this test must not do.
##   (b) a bare single-kind comparison `== nnkProcDef` / `!= nnkProcDef`
##       (with or without a space before the kind name) that excludes `func`
##       by construction — the exact #147/N0 defect shape.
##   (c) an `nskProc`/`nskFunc` symbol-kind gate in live code. N2 eliminated
##       the repo's only such gate (dsl_parser.nim's former C3 proc-as-value
##       pre-filter at `symKind(n) in {nskProc, nskFunc}`): a compile-time
##       probe (`scratchpad/probe_n2_getimpl_symkinds.nim`, run against this
##       toolchain) confirmed `NimNode.getImpl` neither raises nor ever
##       returns a `walkableRoutineKinds` member for `nskParam`/`nskLet`/
##       `nskVar`/`nskForVar`/`nskResult` symbols, so `resolveRoutineImpl`
##       alone (no symKind pre-check) is behavior-identical at that site.
##       There is consequently no "documented site" carve-out needed for
##       class (c) — the ban is unconditional, repo-wide, within the
##       scanned files.
## A line is exempted from all three checks when it is a comment (trimmed
## text starts with `#`) — this file's own header, and every doc comment in
## the scanned sources that narrates history using these tokens in PROSE
## (there are many — e.g. "an `nnkProcDef` NODE"), is not code and must not
## trip the scanner. Allowlisting is done by matching robust markers (the
## const-definition's own exact text; "starts with #"), never by hardcoded
## line numbers — line numbers rot the moment the file is edited above them.
##
## ----------------------------------------------------------------------------
## N2 site inventory (11 code sites fixed in `dsl_parser.nim`; symex.nim had
## zero remaining — N1 already migrated all nine entry macros)
## ----------------------------------------------------------------------------
## Resolution sites (getImpl + kind-check as one step) routed through
## `resolveRoutineImpl`, each keeping its EXISTING failure policy verbatim
## (Invariant-3 — a policy consolidation, never a behavior merge):
##   - `hasSymexOpaquePragma`   — boolean-false predicate
##   - `borrowInfoFor`          — boolean-false predicate (N0-completed site)
##   - `isStdMathProc`          — boolean-false predicate
##   - C3 proc-as-value         — classified-degrade-on-fallthrough (N0-
##     completed site; BOTH the symKind AND impl.kind gates collapse onto
##     one `resolveRoutineImpl` call — see pattern (c) above)
##   - G8 string-op disambiguation — classified-degrade-on-fallthrough
##     (N0-completed site)
##   - rune-compare intercept   — `break`-to-fallthrough (same shape as
##     `borrowInfoFor`, a distinct call site the RFC's known-list did not
##     name; found by this slice's own grep, per the house "grep, never
##     list" rule)
##   - `ensureProcRegistered`   — classified degrade to `sxUnknown`
##     (`feUnsupportedOp`, v67 mechanism)
## Membership-only checks on an ALREADY-obtained impl node (the resolution
## already happened upstream) routed onto `walkableRoutineKinds` directly,
## per the RFC's N2 instruction — no wrapper needed, since there is no
## resolution left to do at these sites:
##   - `hasBorrowPragma`        — receives `impl` as a parameter
##   - `gatherTypeSubst`        — receives `impl` as a parameter, already
##     validated by its one caller (`ensureProcRegistered`)
##   - `parseCalleeImpl`        — `expectKind`, receives `impl` already
##     validated by its one caller
##   - `parseProc*`             — `expectKind`, receives `procDef` already
##     validated by `resolveEntryImpl` (its callers) or a prior
##     `resolveRoutineImpl` result
## Deliberately UNTOUCHED (N3-scoped "routine-shaped node" wider sets — these
## answer "is this AST fragment routine-shaped", not "resolve this symbol",
## and are a separate reconciliation left for N3): the 7-elem family at the
## `earlyClosureCallDetect`/`closureCallDetect` blocks and the statement-
## position closure-call detector, and the 6-elem family behind
## `hasYieldShallow`/`hasReturnShallow`/`hasKindShallow`/
## `substIteratorParams`. Also untouched: the `parseExpr` case-of dispatch
## arm `of nnkProcDef, nnkFuncDef:` — comma-separated case LABELS classifying
## the CURRENT node's own kind (the parser's ordinary per-shape dispatch),
## not a `{}` membership test resolving some OTHER symbol; it was never in
## scope.
##
## Behavior-identical migration (Invariant-3 preserved at every site) ⇒ NO
## `symexWalkerVersion` bump. The floor pin below asserts the version this
## slice landed against, matching house convention (N0/N1 carry the same
## pin style).

import std/[unittest, strutils]
import nelli/smt/canonicalize

const
  dslParserSrc  = staticRead("../src/nelli/smt/dsl_parser.nim")
  symexSrc      = staticRead("../src/nelli/symex.nim")
  canonicalizeSrc = staticRead("../src/nelli/smt/canonicalize.nim")

type
  Violation = object
    file:     string
    lineNo:   int
    lineText: string

proc isCommentLine(trimmed: string): bool =
  ## Nim `#`/`##` doc and ordinary comments both start with `#` once
  ## leading whitespace is stripped. Prose narrating these tokens (this
  ## file's own header included) must never trip the scanner.
  trimmed.startsWith("#")

proc isConstDefLine(trimmed: string): bool =
  ## The ONE allowlisted definition site: `walkableRoutineKinds`'s own
  ## declaration. Matched by its exact, distinctive text — not a line
  ## number, which would rot the moment the file grows or shrinks above it.
  trimmed.contains("walkableRoutineKinds* = {nnkProcDef, nnkFuncDef}")

proc scanForBareKindGates(fname, contents: string, violations: var seq[Violation]) =
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if trimmed.len == 0 or isCommentLine(trimmed) or isConstDefLine(trimmed):
      continue
    let isNarrowSetLiteral =
      trimmed.contains("{nnkProcDef, nnkFuncDef}") or
      trimmed.contains("{nnkFuncDef, nnkProcDef}")
    let isBareSingleKindCompare =
      trimmed.contains("== nnkProcDef") or trimmed.contains("!= nnkProcDef") or
      trimmed.contains("==nnkProcDef") or trimmed.contains("!=nnkProcDef") or
      trimmed.contains("== nnkFuncDef") or trimmed.contains("!= nnkFuncDef") or
      trimmed.contains("==nnkFuncDef") or trimmed.contains("!=nnkFuncDef")
    let isSymKindGate =
      trimmed.contains("nskProc") or trimmed.contains("nskFunc")
    if isNarrowSetLiteral or isBareSingleKindCompare or isSymKindGate:
      violations.add Violation(file: fname, lineNo: lineNo, lineText: rawLine)

suite "symex N2 — permanent routine-kind bare-gate regression audit":

  test "zero bare {nnkProcDef, nnkFuncDef} / nskProc / nskFunc gates outside the nil-core":
    var violations: seq[Violation]
    scanForBareKindGates("src/nelli/smt/dsl_parser.nim", dslParserSrc, violations)
    scanForBareKindGates("src/nelli/symex.nim", symexSrc, violations)
    scanForBareKindGates("src/nelli/smt/canonicalize.nim", canonicalizeSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " bare routine-kind gate(s) outside the walkableRoutineKinds/" &
        "resolveRoutineImpl nil-core:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " & v.lineText.strip() & "\n"
      report.add "Route this site through resolveRoutineImpl (resolution) " &
        "or walkableRoutineKinds (membership on an already-obtained impl), " &
        "per RFC-parser-normalization Cluster N (#146/#148)."
      checkpoint(report)
    check violations.len == 0

  test "walker version floor: symexWalkerVersion >= 71 (N2 is behavior-identical, no bump)":
    check parseInt(symexWalkerVersion) >= 71
