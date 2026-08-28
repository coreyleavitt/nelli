## RFC-parser-normalization (#146), Cluster A, slice A2a — the
## `parseAtomicOperand` chokepoint acceptance, a PERMANENT regression audit.
## Sibling to `tsymex_phase15_N2_kindgate_audit.nim` (same round-2
## institutionalization decision, same `staticRead` + pure-Nim string-scan
## mechanism) rather than an extension of it: N2 audits routine-KIND
## resolution; this audits operand-ANF construction — a different
## vocabulary and a different acceptance shape, sharing only the technique.
##
## ----------------------------------------------------------------------------
## Why a permanent test, not a one-time grep (same TOT-1 rationale N2 cites)
## ----------------------------------------------------------------------------
## A slice-close grep audit proves the atomization was complete ONCE. It
## catches no future regression: nothing stops a later edit from reverting
## one of the eight atomized call sites back to a bare `parseExpr` (e.g. "just
## this once, to fix a bug") without anyone noticing the boundary guarantee
## quietly regressed. The fix: a committed test that runs on every future
## compile.
##
## ----------------------------------------------------------------------------
## What this test scans, and how (pragmatic, marker-comment convention)
## ----------------------------------------------------------------------------
## The RFC's Mechanism names the acceptance target as "any IR-constructing
## consumption of a `parseExpr` operand result" (`mkBinop`/`mkUnop`/
## `mkStrOp`/`mkBorrowOp`) at the atomized families. A pure AST-level check
## of that claim would need to re-implement a Nim parser; this test instead
## uses the same house convention N2 established — a marker-comment tag at
## every atomized call site (`## A2a chokepoint (<family>)`, added in the
## same commit as the atomization itself) plus a scan that:
##   1. every expected marker is present, with the expected per-family
##      COUNT (not just "at least one") — an unexpected count means a site
##      was added, removed, or silently duplicated since this audit was
##      written, and must be re-examined by a human, not waved through;
##   2. every marker-tagged LINE also contains a `parseAtomicOperand(` call
##      on the SAME line — catches a reformatting or revert that strips the
##      chokepoint call but accidentally leaves the marker comment behind
##      (a stale, misleading marker is worse than a missing one);
##   3. the two documented EXCLUSIONS (Mechanism constraint 1: the boolean
##      `bAnd`/`bOr` block, and the `not`-over-boolean-infix sub-case;
##      constraint 4: the guard-cond no-op) carry their own markers, and the
##      `not`-exclusion line genuinely calls plain `parseExpr` (proving the
##      exclusion is real, not merely commented).
## This is deliberately line-based and marker-driven, not a generic "ban
## bare parseExpr near mkBinop" scan: `dsl_parser.nim` has dozens of
## legitimate `parseExpr` call sites entirely unrelated to Cluster A (call
## arguments, array literals, statement bodies, …), so a context-free ban
## would be both unable to distinguish them and unreadable by inspection —
## the same design trade-off N2's own header discusses for its patterns.
##
## ----------------------------------------------------------------------------
## A2a site inventory (13 chokepoint call sites across 8 atomized families,
## dsl_parser.nim)
## ----------------------------------------------------------------------------
##   - string-concat (`&`, the S8 intercept)         — 2 (lhs, rhs)
##   - borrow intercept (`{.borrow.}` operators)      — 2 (l, r)
##   - nil-compare (the non-nil ref side only)        — 1 (refIR; the nil
##     side is a synthesised `mkNil`, never a `parseExpr` result, so it is
##     not itself a chokepoint site)
##   - general infix `else` (comparisons/arithmetic/shl/shr/xor — the
##     non-bAnd/bOr path; constraint 1 holds STRUCTURALLY here because
##     bAnd/bOr are handled entirely in the sibling `if` branch above and
##     never fall through to this `else`) — 2 (l, r)
##   - `not` (unary prefix, non-boolean-infix operand only) — 1
##   - unary minus (non-float-literal operand)        — 1
##   - `pred`/`succ` arithmetic                        — 2 (base, step)
##   - rune-compare intercept (the `nnkCall`-form borrow comparison)  — 2
##     (lhs, rhs)
## Total: 13. At A2a-close, the WHOLE bAnd/bOr block and the guard-cond parse
## inside `mkShortCircuitWhile` were the two DOCUMENTED EXCLUSIONS (Mechanism
## constraints 1 and 4) — deliberately NOT chokepoint sites.
##
## ----------------------------------------------------------------------------
## A2b addendum (RFC-parser-normalization #146/#149, D2) — bAnd/bOr
## classify-first restructure
## ----------------------------------------------------------------------------
## A2b restructures the bAnd/bOr block itself: the boolean-vs-bitwise
## decision (`classifyType(n).ty.kind != itBool`, with an untyped-node
## carve-out) now precedes both operand parses, splitting what was one
## excluded block into two genuinely separate parse paths —
##   - BITWISE and/or (no short-circuit semantics in Nim) — 2 NEW chokepoint
##     sites (l, r), both depositing into the OUTER preamble unconditionally.
##   - BOOLEAN and/or (itBool, or untyped) — D1c's fast/guarded machinery,
##     VERBATIM; still a documented EXCLUSION, now scoped to this one branch
##     rather than the whole block. Branch exclusivity with the bitwise arm
##     makes constraint 1 structural (a bitwise operand can never reach D1c's
##     guard code; a boolean operand can never reach `parseAtomicOperand`)
##     rather than relying on the block never being entered.
## New total: 15 chokepoint call sites across 9 families. The guard-cond
## parse inside `mkShortCircuitWhile` (constraint 4) remains the other
## documented exclusion, unaffected by A2b.
##
## Behavior: hoisted and inline forms produce identical verdicts/witnesses
## (A1 corpus, unchanged); the canonical form changes for any program with a
## previously-compound atomized-family operand (A2a) or a previously-compound
## BITWISE and/or operand (A2b), so the cache key rotates — **Ver: SW**
## (`symexWalkerVersion` 71→72 at A2a, 72→73 at A2b; see `canonicalize.nim`'s
## own doc comment and `tsymex_phase15_CR2_cachekey.nim`).

import std/[unittest, strutils, os]
import nelli/smt/canonicalize
import audit_scan_utils

const
  dslParserPath = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                  "smt" / "dsl_parser.nim"
    ## N46 (round-6 re-review): was `staticRead` -- dsl_parser.nim is ~486KB,
    ## large enough that MSVC's C2026 rejects the emitted C string literal;
    ## this suite has never compiled in this container as a result. Every
    ## consumer below reads the content only inside `test` bodies -- switch
    ## to a TEST-RUNTIME `readFile` (path still resolved at compile time),
    ## matching the precedent `tsymex_r6_n27_placeholder_read_audit.nim`/
    ## `tsymex_r6_n36_raise_class_audit.nim` already established.

let dslParserSrc = readFile(dslParserPath)

type
  Violation = object
    lineNo:   int
    lineText: string
    reason:   string

const
  chokepointFamilies = [
    ("A2a chokepoint (string-concat)", 2),
    ("A2a chokepoint (borrow intercept)", 2),
    ("A2a chokepoint (nil-compare, non-nil side)", 1),
    ("A2a chokepoint (general infix)", 2),
    ("A2a chokepoint (unary not)", 1),
    ("A2a chokepoint (unary minus)", 1),
    ("A2a chokepoint (pred/succ)", 2),
    ("A2a chokepoint (rune-compare)", 2),
    ("A2b chokepoint (bitwise and/or)", 2),
  ]
    ## The 9 atomized families and their exact expected per-family call-site
    ## count (15 total) — see the header's site inventory. A count drift in
    ## EITHER direction (a site silently removed, or a family silently
    ## duplicated/split) fails loudly rather than passing on ">= 1".

  exclusionMarkers = [
    "A2b EXCLUSION",                        ## boolean and/or (constraint 1; A2b-scoped)
    "A2a exclusion (not-over-bAnd/bOr",     ## not-over-boolean-infix (constraint 1)
    "A2a guard-cond carve-out",             ## guard-cond no-op (constraint 4)
  ]

suite "symex A2a — permanent parseAtomicOperand chokepoint audit":

  test "every atomized family carries its exact expected marker count, each on a parseAtomicOperand( line":
    var violations: seq[Violation]
    for (marker, expected) in chokepointFamilies:
      var found = 0
      var lineNo = 0
      for rawLine in dslParserSrc.splitLines():
        inc lineNo
        if rawLine.contains(marker):
          inc found
          if not rawLine.contains("parseAtomicOperand("):
            violations.add Violation(lineNo: lineNo, lineText: rawLine,
              reason: "marker '" & marker & "' present but line does not " &
                      "call parseAtomicOperand( — stale/misleading marker")
      if found != expected:
        violations.add Violation(lineNo: 0, lineText: "",
          reason: "family '" & marker & "': expected " & $expected &
                  " site(s), found " & $found)
    if violations.len > 0:
      var report = "\nFound " & $violations.len & " A2a chokepoint audit violation(s):\n"
      for v in violations:
        if v.lineNo > 0:
          report.add "  line " & $v.lineNo & ": " & v.reason & "\n    " & v.lineText.strip() & "\n"
        else:
          report.add "  " & v.reason & "\n"
      report.add "Route this site through parseAtomicOperand and tag it with " &
        "its family's `## A2a chokepoint (<family>)` marker, or update this " &
        "audit's site inventory deliberately, per RFC-parser-normalization " &
        "Cluster A, slice A2a (#146/#149)."
      checkpoint(report)
    check violations.len == 0

  test "the two documented exclusions (boolean bAnd/bOr; guard-cond no-op) carry their markers":
    var violations: seq[Violation]
    for marker in exclusionMarkers:
      if not dslParserSrc.contains(marker):
        violations.add Violation(lineNo: 0, lineText: "",
          reason: "missing exclusion marker: '" & marker & "'")
    # The not-exclusion line must itself call plain parseExpr (proving the
    # exclusion is a real un-atomized parse, not merely a comment):
    var sawNotExclusionCall = false
    for rawLine in dslParserSrc.splitLines():
      if rawLine.contains("A2a exclusion (not-over-bAnd/bOr") and
         rawLine.contains("parseExpr(") and not rawLine.contains("parseAtomicOperand("):
        sawNotExclusionCall = true
    if not sawNotExclusionCall:
      violations.add Violation(lineNo: 0, lineText: "",
        reason: "the not-over-bAnd/bOr exclusion marker is present but no " &
                "line tagged with it calls plain parseExpr( without also " &
                "calling parseAtomicOperand( — the exclusion may have been lost")
    # A2b's boolean and/or branch (LHS + RHS) must itself carry the
    # "A2b EXCLUSION" marker on the SAME line as a bare parseExpr( call — the
    # post-restructure analog of the not-exclusion check above, catching a
    # future revert that swaps parseAtomicOperand into the boolean path
    # without updating (or removing) the marker.
    var booleanExclusionCallCount = 0
    for rawLine in dslParserSrc.splitLines():
      if rawLine.contains("A2b EXCLUSION (boolean and/or") and
         rawLine.contains("parseExpr(") and not rawLine.contains("parseAtomicOperand("):
        inc booleanExclusionCallCount
    if booleanExclusionCallCount != 2:
      violations.add Violation(lineNo: 0, lineText: "",
        reason: "expected exactly 2 lines tagged 'A2b EXCLUSION (boolean " &
                "and/or' calling bare parseExpr( (LHS + RHS), found " &
                $booleanExclusionCallCount)
    # The guard-cond carve-out must set ctx.inGuardCond exactly once (the
    # single shared mkShortCircuitWhile implementation both nnkWhileStmt
    # arms feed into — see ParseCtx.inGuardCond's own doc comment).
    var guardSetCount = 0
    for rawLine in dslParserSrc.splitLines():
      let trimmed = rawLine.strip()
      if isCommentLine(trimmed): continue
      if trimmed == "ctx.inGuardCond = true":
        inc guardSetCount
    if guardSetCount != 1:
      violations.add Violation(lineNo: 0, lineText: "",
        reason: "expected exactly 1 'ctx.inGuardCond = true' site (the " &
                "shared mkShortCircuitWhile), found " & $guardSetCount)
    if violations.len > 0:
      var report = "\nFound " & $violations.len & " A2a exclusion audit violation(s):\n"
      for v in violations:
        report.add "  " & v.reason & "\n"
      checkpoint(report)
    check violations.len == 0

  test "walker version floor: symexWalkerVersion >= 73 (A2a bumped 71->72, A2b 72->73)":
    check parseInt(symexWalkerVersion) >= 73
