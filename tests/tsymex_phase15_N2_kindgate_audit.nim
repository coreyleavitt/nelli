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
## The four banned patterns (source-line, not AST-level — pure string scan,
## deliberately simple: this test must stay readable by inspection)
## ----------------------------------------------------------------------------
##   (a) an inline two-element set literal `{nnkProcDef, nnkFuncDef}` (either
##       member order) OUTSIDE the `walkableRoutineKinds` const definition
##       line itself. Matches bare `==`/`!=`/`in`/`notin` membership tests
##       AND `expectKind` calls that spell the set out inline instead of
##       naming `walkableRoutineKinds`. Deliberately does NOT match the
##       wider N3-scoped "routine-shaped node" sets (the `routineShapedFor-
##       ClosureDetect`/`nestedRoutineScanBoundary` families) — those carry
##       more than two members, so the exact two-element substring never
##       matches them; pattern (d) below is their dedicated ban.
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
##   (d) — added by N3 — a WIDE inline routine-shaped-node list: more than
##       two `std/macros.RoutineNodes`-vocabulary tokens (`nnkProcDef`,
##       `nnkFuncDef`, `nnkIteratorDef`, `nnkMethodDef`, `nnkConverterDef`,
##       `nnkTemplateDef`, `nnkMacroDef`, `nnkLambda`, `nnkDo`) chained by
##       nothing but commas/braces/whitespace — the shape of an inline SET
##       LITERAL (`{A, B, C, ...}`) or CASE-LABEL LIST (`of A, B, C, ...:`).
##       This is the N3 reconciliation target: the pre-N3 7-element
##       closure-call-detect family and 6-element scanner-scope-boundary
##       family, both copy-pasted at their call sites instead of naming a
##       shared const. Unlike (a)–(c), this scan is MULTI-LINE-AWARE (see
##       `scanForWideRoutineKindLists` below) — the house 79-column style
##       wraps these lists across 2–3 source lines, which a per-line
##       substring match (patterns a–c) cannot see across. A reference to
##       the named consts (`routineShapedForClosureDetect`/
##       `nestedRoutineScanBoundary`) is a single identifier, never a
##       vocabulary-token run, so it never trips this scan — including
##       their OWN definitions (`RoutineNodes - {nnkDo, ...}` names at most
##       two vocabulary tokens inline, under the >2 threshold, by
##       construction; no line-based allowlist is needed for them the way
##       pattern (a) needs one for `walkableRoutineKinds`).
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
## ----------------------------------------------------------------------------
## N3 site inventory (7 sites reconciled onto two named consts, both defined
## against `std/macros.RoutineNodes` by explicit exclusion in dsl_parser.nim)
## ----------------------------------------------------------------------------
## `routineShapedForClosureDetect` (closure-call detection — "does
## `calleeSym.getImpl` report an actual routine DEFINITION, as opposed to a
## proc-valued variable"): `earlyClosureCallDetect`, `closureCallDetect`, and
## the statement-position closure-call detector guarding
## `ensureProcRegistered`'s call fall-through — the former 7-element inline
## literal (no `nnkLambda`/`nnkDo`; membership UNCHANGED, only the spelling
## moved onto the named const).
##
## `nestedRoutineScanBoundary` (A3/ADR-0014 scanner scope boundary — "does
## this node start a nested scope the scan must not descend into"):
## `hasYieldShallow`, `hasReturnShallow`, `hasKindShallow` (shared by
## `hasBreakContinueShallow`), and `substIteratorParams` — the former
## 6-element literal PLUS `nnkMethodDef`/`nnkConverterDef` (closing the
## RFC's named latent gap; both probe-verified top-level-only in Nim 2.2.10,
## so the gap was never reachable — adding them is behavior-identical
## hardening, not a verdict change).
##
## Still deliberately UNTOUCHED, and out of pattern (d)'s reach by
## construction (only 2 elements, well under the >2 threshold): the
## `parseExpr` case-of dispatch arm `of nnkProcDef, nnkFuncDef:` —
## comma-separated case LABELS classifying the CURRENT node's own kind (the
## parser's ordinary per-shape dispatch), not a membership test resolving
## some OTHER symbol; it was never in scope for either N2 or N3.
##
## Both probe findings that DECIDED the N3 design (2026-08-13,
## `scratchpad/probe_n3_*.nim`, not committed — gitignored `scratchpad/`,
## same convention as the N2/RFC-146 probes): nested `method`/`converter`
## definitions are illegal Nim ("only allowed at top level"), and `do:`
## notation is rewritten to `nnkLambda` by the parser before any symbol's
## typed `getImpl` can report it — so `nnkDo` is unreachable at every one of
## these sites regardless of which family. Neither family's reconciliation
## changes any verdict.
##
## Behavior-identical migration (Invariant-3 preserved at every site, N2 AND
## N3) ⇒ NO `symexWalkerVersion` bump. The floor pin below asserts the
## version this slice landed against, matching house convention (N0/N1
## carry the same pin style).

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

const routineNodeVocab = [
  "nnkProcDef", "nnkFuncDef", "nnkIteratorDef", "nnkMethodDef",
  "nnkConverterDef", "nnkTemplateDef", "nnkMacroDef", "nnkLambda", "nnkDo"]
  ## Exactly `std/macros.RoutineNodes`, spelled as strings (N3). This is the
  ## vocabulary pattern (d) hunts for — see the header comment for why a
  ## generic ">2 comma-joined `nnk*` identifiers" rule would be useless here
  ## (this parser's ordinary per-shape `case` dispatch has plenty of
  ## unrelated wide `nnk*` label lists; restricting to exactly these nine
  ## names is what keeps the scan precise).

proc isIdentChar(c: char): bool = c.isAlphaNumeric or c == '_'

proc routineVocabWordLenAt(s: string, i: int): int =
  ## Length of the `routineNodeVocab` word starting EXACTLY at `s[i]`,
  ## matched at whole-word boundaries only (so `nnkDo` does not falsely
  ## match inside `nnkDotExpr`, and a vocabulary word inside a longer
  ## identifier is never counted). Returns 0 when no word matches.
  if i > 0 and isIdentChar(s[i - 1]): return 0
  for w in routineNodeVocab:
    let e = i + w.len
    if e <= s.len and s[i ..< e] == w and (e == s.len or not isIdentChar(s[e])):
      return w.len
  0

proc scanForWideRoutineKindLists(fname, contents: string, violations: var seq[Violation]) =
  ## Multi-line-aware companion to `scanForBareKindGates`'s single-line
  ## patterns (a)-(c): finds every maximal run of `routineNodeVocab` tokens
  ## joined by nothing but whitespace/newlines/commas/braces (the shape of
  ## an inline `{A, B, C, ...}` set literal or `of A, B, C, ...:` case-label
  ## list, however many source lines the house 79-column style wraps it
  ## across) and flags any run of MORE than two members. A reference to a
  ## named const (`walkableRoutineKinds`, `routineShapedForClosureDetect`,
  ## `nestedRoutineScanBoundary`, or any future one) is a single identifier
  ## — never a vocabulary-token run — so naming a const is always the way
  ## to satisfy this scan, never a special-cased exemption.
  var
    lineNo = 1
    chainCount = 0
    chainStartLine = 0
    i = 0
  template flushChain() =
    if chainCount > 2:
      violations.add Violation(file: fname, lineNo: chainStartLine,
        lineText: "wide inline routine-shaped-node list (" & $chainCount &
                  " members chained here)")
    chainCount = 0
  while i < contents.len:
    if contents[i] == '\n':
      inc lineNo
    let wlen = routineVocabWordLenAt(contents, i)
    if wlen > 0:
      if chainCount == 0:
        chainStartLine = lineNo
      inc chainCount
      i += wlen
    elif chainCount > 0 and contents[i] in {' ', '\t', '\r', '\n', ',', '{', '}'}:
      inc i   ## neutral separator: keep the chain open across the wrap
    else:
      flushChain()
      inc i
  flushChain()

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

  test "zero wide inline routine-shaped-node lists outside the N3 consts (RFC N3)":
    ## Multi-line-aware: pattern (d). Pre-N3 this flags exactly 7 sites (the
    ## 3-site `routineShapedForClosureDetect` family + the 4-site
    ## `nestedRoutineScanBoundary` family); post-N3 migration it is zero.
    var violations: seq[Violation]
    scanForWideRoutineKindLists("src/nelli/smt/dsl_parser.nim", dslParserSrc, violations)
    scanForWideRoutineKindLists("src/nelli/symex.nim", symexSrc, violations)
    scanForWideRoutineKindLists("src/nelli/smt/canonicalize.nim", canonicalizeSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " wide inline routine-shaped-node list(s) outside " &
        "routineShapedForClosureDetect/nestedRoutineScanBoundary:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " & v.lineText & "\n"
      report.add "Name (or route through) routineShapedForClosureDetect / " &
        "nestedRoutineScanBoundary, per RFC-parser-normalization Cluster N, " &
        "slice N3 (#146/#148/#150)."
      checkpoint(report)
    check violations.len == 0

  test "walker version floor: symexWalkerVersion >= 71 (N2/N3 are behavior-identical, no bump)":
    check parseInt(symexWalkerVersion) >= 71
