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
##       member order, ANY spacing, and wrapped across any number of source
##       lines — M2 hardening, below) OUTSIDE the `walkableRoutineKinds`
##       const definition line itself. Matches bare `==`/`!=`/`in`/`notin`
##       membership tests AND `expectKind` calls that spell the set out
##       inline instead of naming `walkableRoutineKinds`. Deliberately does
##       NOT match the wider N3-scoped "routine-shaped node" sets (the
##       `routineShapedForClosureDetect`/`nestedRoutineScanBoundary`
##       families) — those carry more than two members, so a run of exactly
##       two vocabulary tokens never matches them; pattern (d) below is
##       their dedicated ban.
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
## Out of pattern (d)'s reach by construction (only 2 elements, well under
## the >2 threshold): the `parseExpr` case-of dispatch arm `of nnkProcDef,
## nnkFuncDef:` — comma-separated case LABELS classifying the CURRENT
## node's own kind (the parser's ordinary per-shape dispatch), not a
## membership test resolving some OTHER symbol; it was never in scope for
## either N2 or N3. It IS, however, in scope for the M2-hardened pattern
## (f) below (added specifically to close the "a new 2-element case arm
## evades every pattern" gap M2 found) — that pattern scans for exactly
## this arm shape and carries a site-specific exemption for this one
## legitimate occurrence; see the M2 section for why the exemption can't be
## satisfied by simply reusing this arm's text.
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
##
## ----------------------------------------------------------------------------
## C2 addition (2026-08-14): generic-param descriptor threading
## ----------------------------------------------------------------------------
## RFC-parser-normalization Cluster C, slice C2 threads N1's fully-parsed
## `GenericDescriptor` through the remaining consumers that used to re-derive
## the `impl[2]`-vs-`impl[5][1]` generic-params dual-location lookup on their
## own: `gatherTypeSubst` (generic-param NAMES) and `parseCalleeImpl`'s
## concept-constraint capture (per-param CONSTRAINT nodes). Post-C2 the ONLY
## place that lookup may live is `genericParamsNode` (the private helper
## `resolveGenericDescriptor` calls) — every other consumer reads
## `resolveGenericDescriptor(impl).params` instead. `staticParamNames` and
## `instKeyFor` were audited too (per the RFC's explicit C2 action item):
## `staticParamNames` had its own independent `nnkIdentDefs` walk (duplicate
## `isStatic` derivation, though it already delegated the location lookup to
## `genericParamsNode`) and is migrated to filter `resolveGenericDescriptor`'s
## `params` by `.isStatic`; `instKeyFor` never re-derived anything directly —
## it only consumes `staticParamNames`, so it is descriptor-backed
## transitively once `staticParamNames` migrates.
##
## `scanForGenericParamLocationProbes` below is the permanent regression
## audit for the dual-location half: zero `nnkGenericParams` kind-comparisons
## outside `genericParamsNode`'s own body. It is intentionally narrower than
## a full "detect any re-walk of generic-param identDefs" scanner — the RFC's
## own C2 acceptance text names this exact pattern ("impl[2]/impl[5][1]-style
## generic-param location probes"), and a scanner broad enough to also catch
## an independent identDefs walk that DOESN'T re-derive the location (e.g.
## `staticParamNames`'s pre-C2 shape) would need to distinguish generic-param
## identDefs walks from the many unrelated FORMAL-param identDefs walks
## elsewhere in this file (iterator inlining, `parseCalleeImpl`'s own param
## loop, `parseProc`'s SUT param loop, …) by more than a string match — not a
## simple, inspectable scan. That half of the acceptance criterion (the
## identDefs walk existing in exactly one place) is enforced by code review
## and the RFC's own record of the migration, not a standing string scanner.
##
## ----------------------------------------------------------------------------
## M2 hardening (2026-08-14): whitespace/wrap-robust (a), plus new pattern (f)
## ----------------------------------------------------------------------------
## A code review of this file (RFC-parser-normalization #146, round 1)
## converged two findings onto the same root cause: pattern (a) and the
## exemption list in the header above were both HONEST about what they
## covered, but what they covered was less than the header's framing implied.
## Concretely:
##   - pattern (a), as originally written, was a single-line, single-spelling
##     substring match (`trimmed.contains("{nnkProcDef, nnkFuncDef}")`, one
##     space after the comma, one physical line). A respaced
##     `{nnkFuncDef,nnkProcDef}` or a line-wrapped `{nnkProcDef,\n
##     nnkFuncDef}` (the house style wraps long lines exactly this way, and
##     pattern (d) already had to become multi-line-aware for the same
##     reason) evaded it silently.
##   - the "Still deliberately UNTOUCHED" `parseExpr` case arm carve-out
##     documented above was true only because no pattern scanned for
##     2-element `case` arms AT ALL. A brand-new `of nnkProcDef, nnkFuncDef:`
##     arm added at some unrelated call site — not the parser's own per-shape
##     dispatch, an actual resolution-site evasion wearing case-arm syntax
##     instead of a set literal or a bare compare — evaded every one of
##     patterns (a)-(e): (d)'s scanner only fires above the 2-member
##     threshold (deliberately, to exempt `walkableRoutineKinds` and the N3
##     consts' own definitions), and no other pattern looks at `of` arms.
##
## Both gaps are closed by `scanForTwoElemProcFuncGates` below, which
## replaces pattern (a)'s old per-line check and adds pattern (f):
##   (a, hardened) unchanged in what it bans (an inline 2-element
##       `{nnkProcDef, nnkFuncDef}` set literal), but now detected by the
##       SAME char-by-char, separator-skipping walk `scanForWideRoutineKind-
##       Lists` already uses for pattern (d) (`routineVocabWordLenAt`) —
##       whitespace and line-wraps are structurally invisible to it, so
##       every spelling/order/wrap of the pair is caught, not just the one
##       the original author happened to write. The `walkableRoutineKinds`
##       const-definition exemption still works, checked against a
##       whitespace-normalized copy of its own line (`normalizeWs`) rather
##       than a fixed-spacing substring — so respacing the DEFINITION itself
##       doesn't accidentally un-exempt it.
##   (f, new) a 2-element `case`-arm `of nnkProcDef, nnkFuncDef:` (any
##       order/spacing/wrap) — the shape the M2 review demonstrated evades
##       everything else. The repo's one legitimate instance (`parseExpr`'s
##       own per-shape dispatch, dsl_parser.nim) is exempted, but NOT by
##       matching the arm's text alone: that text is exactly what a new
##       evasion would also write, so a text-only exemption would exempt the
##       evasion too and defeat the point of adding this pattern. The
##       exemption instead requires a two-part, site-specific fingerprint —
##       the arm text AND its immediate next line of (non-comment) code
##       being the exact `parseLambda(n, ctx)` call the real site makes — so
##       a future 2-element case arm anywhere else, even one that copies the
##       exact arm text, still trips the audit unless it also happens to be
##       followed by that exact call, which is the real site's fingerprint,
##       not a shape a new evasion would incidentally reproduce.
## Both shapes skip comment lines entirely (a whole-line check, same
## `isCommentLine` predicate the rest of the file uses) — needed here
## specifically because this scan fires at exactly two vocabulary tokens,
## and canonicalize.nim:165's doc comment narrates this exact pair in prose
## (`` `{nnkProcDef, nnkFuncDef}` ``); pattern (d)'s >2-token threshold never
## had to worry about this, but a 2-token pattern does.

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
  ## Patterns (b) and (c) only — single-line, per-line substring checks.
  ## Pattern (a) (the narrow 2-element set literal) moved to the
  ## whitespace/line-wrap-robust `scanForTwoElemProcFuncGates` below (M2
  ## hardening): a per-line substring check cannot see a respaced or
  ## line-wrapped spelling of the same construct.
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if trimmed.len == 0 or isCommentLine(trimmed) or isConstDefLine(trimmed):
      continue
    let isBareSingleKindCompare =
      trimmed.contains("== nnkProcDef") or trimmed.contains("!= nnkProcDef") or
      trimmed.contains("==nnkProcDef") or trimmed.contains("!=nnkProcDef") or
      trimmed.contains("== nnkFuncDef") or trimmed.contains("!= nnkFuncDef") or
      trimmed.contains("==nnkFuncDef") or trimmed.contains("!=nnkFuncDef")
    let isSymKindGate =
      trimmed.contains("nskProc") or trimmed.contains("nskFunc")
    if isBareSingleKindCompare or isSymKindGate:
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
  ## patterns (b)-(c): finds every maximal run of `routineNodeVocab` tokens
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

proc normalizeWs(s: string): string =
  ## Collapse every run of whitespace (space/tab/CR/LF) into a single space
  ## and drop leading/trailing whitespace. Used so a candidate line (or the
  ## fixed marker text it is compared against) matches regardless of how it
  ## is spaced — the M2 hardening's whole point.
  result = ""
  var pendingSpace = false
  for c in s:
    if c in {' ', '\t', '\r', '\n'}:
      pendingSpace = result.len > 0
    else:
      if pendingSpace:
        result.add ' '
      pendingSpace = false
      result.add c

proc nearestNonWsBefore(contents: string, idx: int): char =
  ## Nearest non-whitespace byte strictly before byte offset `idx`, skipping
  ## only whitespace (never commas/braces) — so a comma-separated NEIGHBOR
  ## token is still visible here, distinguishing a true 2-element construct
  ## from an incidental 2-element run embedded inside a larger list. `'\0'`
  ## at the start of the file.
  var j = idx - 1
  while j >= 0 and contents[j] in {' ', '\t', '\r', '\n'}:
    dec j
  if j >= 0: contents[j] else: '\0'

proc nearestNonWsAtOrAfter(contents: string, idx: int): char =
  ## Nearest non-whitespace byte at-or-after byte offset `idx`, same
  ## whitespace-only-skip rule as `nearestNonWsBefore`. `'\0'` at EOF.
  var j = idx
  while j < contents.len and contents[j] in {' ', '\t', '\r', '\n'}:
    inc j
  if j < contents.len: contents[j] else: '\0'

proc precededByOfKeyword(contents: string, idx: int): bool =
  ## True when the token immediately before byte offset `idx` (skipping only
  ## whitespace) is the two-letter `case`-arm keyword `of`, at a word
  ## boundary — e.g. the `of` in `of nnkProcDef, nnkFuncDef:`.
  var j = idx - 1
  while j >= 0 and contents[j] in {' ', '\t', '\r', '\n'}:
    dec j
  if j < 1: return false
  if contents[j] != 'f' or contents[j - 1] != 'o': return false
  let beforeO = j - 2
  beforeO < 0 or not isIdentChar(contents[beforeO])

proc isProcFuncPair(words: seq[string]): bool =
  ## True when `words` is exactly the two-element run `nnkProcDef`,
  ## `nnkFuncDef` in either order — never fewer, never more, and never any
  ## other `routineNodeVocab` pairing.
  words.len == 2 and
    ((words[0] == "nnkProcDef" and words[1] == "nnkFuncDef") or
     (words[0] == "nnkFuncDef" and words[1] == "nnkProcDef"))

proc firstCodeLineFrom(lines: seq[string], startIdx: int): string =
  ## Normalized text of the first line at 0-based index `startIdx` or later
  ## that is neither blank nor a comment. Empty string past EOF.
  for idx in startIdx ..< lines.len:
    let t = lines[idx].strip()
    if t.len > 0 and not isCommentLine(t):
      return normalizeWs(t)
  ""

proc scanForTwoElemProcFuncGates(fname, contents: string, violations: var seq[Violation]) =
  ## M2 hardening (RFC-parser-normalization #146, round 1). Whitespace- and
  ## line-wrap-robust replacement for pattern (a)'s old per-line check, plus
  ## new pattern (f). Reuses the same char-by-char, separator-skipping walk
  ## as `scanForWideRoutineKindLists` (`routineVocabWordLenAt`) so respacing
  ## (`{nnkFuncDef,nnkProcDef}`), reordering, and line-wrapping
  ## (`{nnkProcDef,\n  nnkFuncDef}`) are all caught identically — a fixed,
  ## single-spelling substring cannot see any of these.
  ##
  ## Every maximal 2-element run of `routineNodeVocab` tokens that is EXACTLY
  ## `nnkProcDef`/`nnkFuncDef` (either order) is classified by its immediate
  ## (whitespace-only-skipped) surroundings:
  ##   (a, hardened) immediately brace-enclosed        -> inline set literal,
  ##       exempt only on the `walkableRoutineKinds` const-definition line
  ##       (matched against a whitespace-normalized copy of that line, so
  ##       respacing the DEFINITION doesn't accidentally un-exempt it).
  ##   (f, new)      `of`-prefixed and `:`-terminated  -> a 2-element `case`
  ##       arm, exempt only at the one legitimate site (`parseExpr`'s own
  ##       per-shape dispatch in dsl_parser.nim). The exemption is
  ##       deliberately NOT just "arm text matches" — that text is exactly
  ##       what a new evasion would also write. It additionally requires the
  ##       arm's immediate next line of (non-comment) code to be the exact
  ##       `parseLambda(n, ctx)` call the real site makes; a new 2-element
  ##       arm anywhere else — even one that copies the arm text verbatim —
  ##       still trips this scan unless it also reproduces that call.
  ## Any other 2-element run of this pair (neither brace-enclosed nor an
  ## `of`/`:` arm — e.g. incidental prose-adjacent text) is not flagged;
  ## comment lines are skipped entirely first (see below), which is what
  ## makes that safe.
  ##
  ## Comment lines never contribute to a chain (checked whole-line, same
  ## `isCommentLine` predicate as the rest of the file) — needed here
  ## specifically because this scan fires at exactly two tokens, and
  ## canonicalize.nim:165's doc comment narrates this exact pair in prose.
  let lines = contents.splitLines()
  var commentLine = newSeq[bool](lines.len)
  for idx, ln in lines:
    commentLine[idx] = isCommentLine(ln.strip())
  var
    lineNo = 1
    chainStart = -1
    chainStartLine = 0
    chainLastEnd = -1
    chainWords: seq[string]
    i = 0
  template resetChain() =
    chainStart = -1
    chainLastEnd = -1
    chainWords.setLen(0)
  template flushChain() =
    if isProcFuncPair(chainWords):
      let beforeCh = nearestNonWsBefore(contents, chainStart)
      let afterCh = nearestNonWsAtOrAfter(contents, chainLastEnd)
      if beforeCh == '{' and afterCh == '}':
        let siteLine =
          if chainStartLine >= 1 and chainStartLine <= lines.len:
            lines[chainStartLine - 1]
          else: ""
        if not normalizeWs(siteLine).contains("walkableRoutineKinds* = {"):
          violations.add Violation(file: fname, lineNo: chainStartLine,
            lineText: "two-element {nnkProcDef, nnkFuncDef} set literal " &
                      "(any order/spacing/line-wrap)")
      elif afterCh == ':' and precededByOfKeyword(contents, chainStart):
        if firstCodeLineFrom(lines, chainStartLine) != "parseLambda(n, ctx)":
          violations.add Violation(file: fname, lineNo: chainStartLine,
            lineText: "two-element `of nnkProcDef, nnkFuncDef:` case arm " &
                      "(any order/spacing/line-wrap)")
    resetChain()
  while i < contents.len:
    if contents[i] == '\n':
      inc lineNo
    let inComment = lineNo >= 1 and lineNo <= commentLine.len and
                     commentLine[lineNo - 1]
    if inComment:
      if chainStart >= 0: flushChain()
      inc i
      continue
    let wlen = routineVocabWordLenAt(contents, i)
    if wlen > 0:
      if chainStart < 0:
        chainStart = i
        chainStartLine = lineNo
      chainWords.add contents[i ..< i + wlen]
      i += wlen
      chainLastEnd = i
    elif chainStart >= 0 and contents[i] in {' ', '\t', '\r', '\n', ',', '{', '}'}:
      inc i   ## neutral separator: keep the chain open across the wrap
    else:
      flushChain()
      inc i
  flushChain()

proc isGenericParamsNodeBodyLine(trimmed: string): bool =
  ## The two ALLOWLISTED lines — inside `genericParamsNode`'s own body — that
  ## perform the ONE dual-location `impl[2]`-vs-`impl[5][1]` generic-params
  ## probe (RFC-parser-normalization C2). Matched by exact trimmed text, the
  ## same robust-marker convention `isConstDefLine` uses above (never a line
  ## number). Every other site must route through `resolveGenericDescriptor`
  ## instead of re-deriving this lookup.
  trimmed == "if impl[2].kind == nnkGenericParams: return impl[2]" or
  trimmed == "impl[5][1].kind == nnkGenericParams: return impl[5][1]"

proc scanForGenericParamLocationProbes(fname, contents: string,
                                        violations: var seq[Violation]) =
  ## RFC-parser-normalization C2 (pattern (e)): zero `nnkGenericParams`
  ## kind-comparisons outside `genericParamsNode`'s own body. Pre-C2 this
  ## flags exactly two sites — `gatherTypeSubst` and `parseCalleeImpl`, each
  ## re-deriving the dual-location trick independently instead of reading
  ## `resolveGenericDescriptor(impl).params`; post-C2 it is zero.
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if trimmed.len == 0 or isCommentLine(trimmed) or
       isGenericParamsNodeBodyLine(trimmed):
      continue
    if trimmed.contains("nnkGenericParams"):
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

  test "zero {nnkProcDef, nnkFuncDef}-pair set literals / case arms of any spacing/order/wrap (M2)":
    ## Whitespace/line-wrap-robust patterns (a, hardened) and (f, new).
    ## Baseline: two exempt sites (the `walkableRoutineKinds` const
    ## definition, and `parseExpr`'s own `of nnkProcDef, nnkFuncDef:`
    ## per-shape dispatch arm) and zero violations — any respacing,
    ## reordering, line-wrapping, or brand-new 2-element case arm of this
    ## exact pair anywhere else in the scanned files must trip this test.
    var violations: seq[Violation]
    scanForTwoElemProcFuncGates("src/nelli/smt/dsl_parser.nim", dslParserSrc, violations)
    scanForTwoElemProcFuncGates("src/nelli/symex.nim", symexSrc, violations)
    scanForTwoElemProcFuncGates("src/nelli/smt/canonicalize.nim", canonicalizeSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " {nnkProcDef, nnkFuncDef}-pair set literal(s)/case arm(s) outside " &
        "walkableRoutineKinds / parseExpr's own per-shape dispatch:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " & v.lineText & "\n"
      report.add "Route this site through resolveRoutineImpl/" &
        "walkableRoutineKinds instead of an inline pair, per " &
        "RFC-parser-normalization Cluster N (#146, round 1, M2)."
      checkpoint(report)
    check violations.len == 0

  test "zero impl[2]/impl[5][1]-style generic-param location probes outside genericParamsNode (RFC C2)":
    ## Pre-C2 baseline: flags `gatherTypeSubst` and `parseCalleeImpl`, the two
    ## consumers that re-derived the `impl[2]`-vs-`impl[5][1]` dual-location
    ## trick independently instead of reading
    ## `resolveGenericDescriptor(impl).params`. Post-C2: zero — the lookup
    ## lives exactly once, inside `genericParamsNode`.
    var violations: seq[Violation]
    scanForGenericParamLocationProbes("src/nelli/smt/dsl_parser.nim",
                                       dslParserSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " generic-param dual-location probe(s) outside genericParamsNode:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " & v.lineText.strip() & "\n"
      report.add "Route this site through resolveGenericDescriptor(impl).params " &
        "instead of re-deriving the impl[2]/impl[5][1] lookup, per " &
        "RFC-parser-normalization Cluster C, slice C2 (#146/#150)."
      checkpoint(report)
    check violations.len == 0

  test "walker version floor: symexWalkerVersion >= 71 (N2/N3 are behavior-identical, no bump)":
    check parseInt(symexWalkerVersion) >= 71
