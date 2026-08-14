## RFC-parser-normalization (#146), round 1, code-review finding H1 —
## `isAtomicIR`'s shape-coupling boundary (`dsl_parser.nim` ~:1200-1253).
##
## H1 (verified, High): `isAtomicIR` is the predicate deciding which operand
## IR shapes the A2a `parseAtomicOperand` chokepoint must NOT hoist. Its
## membership grew twice, empirically, in response to two separate
## incidents — `iekStrAt` (CR-17(a)'s `s[i]`-ordering shape guard) and
## `iekStrLen`/`iekSeqLen` (D1c's `rhsPreamble.len == 0` fast-path
## pollution) — with no completeness audit either time, unlike every other
## completeness claim this RFC makes (N2's kind-gate audit, A2a's own
## chokepoint-site audit). The predicate's own doc comment (dsl_parser.nim
## ~:1245-1251) names a residual, narrower version of the SAME hazard for
## "other zero-fault compound-shaped kinds" as an unswept candidate finding.
##
## A verifier made the residual concrete: `rhsHasInlineDefectFork`
## (dsl_parser.nim ~:731-823) ALSO unconditionally clears `iekField` (:753),
## `iekIndex` (:755), and `iekContains` (:769) for bare-var/literal
## receivers — the exact same "zero-fault compound shape" property that
## earned `iekStrLen`/`iekSeqLen` their spot in `isAtomicIR`'s allowlist —
## yet none of the three is admitted. As a comparison operand under a
## boolean `and`/`or` RHS, each is hoisted by `parseAtomicOperand` today,
## manufacturing a `rhsPreamble` entry that flips D1c's own fast-path
## predicate (`rhsPreamble.len == 0 and not rhsHasInlineDefectFork(rhsIR)`,
## ~:1495) exactly as `s.len` did pre-A2a-triage — whether that flip could
## ever defeat a downstream `svKind`-based decline (e.g. the slice-bound
## `loSV.kind != svInt` checks at `runtime_strings.nim`:207 /
## `runtime.nim`:3068) was UNPROVEN by any test.
##
## This file has two parts, per the finding's own remediation shape:
##   PART 1 (CHARACTERIZATION) — SUT twin-pairs for all three kinds, proving
##     the hazard is latent-but-benign AT HEAD (every twin agrees). These
##     cells become permanent pins: any future divergence between the
##     natural (unhoisted) and hand-hoisted forms fails loudly.
##   PART 2 (AUDIT) — a `tsymex_phase15_N2_kindgate_audit.nim`-style
##     `staticRead` + pure-Nim string scan (read that file's header for the
##     TOT-1 "permanent test, not a one-time grep" rationale, shared
##     verbatim here) that inventories every SUBFIELD IR-kind shape-peek in
##     `runtime.nim`/`runtime_strings.nim` and requires each to be in
##     exactly one of: `isAtomicIR`'s allowlist, the always-atomic
##     literal/var set, or a documented exemption with a one-line rationale.
##     A future shape-peek on a hoistable kind — the exact class of bug this
##     finding is about — now fails the build, not just a future code review.
##
## Both walker-version-neutral: this slice changes no parser behavior, only
## tests and documentation (isAtomicIR's own doc comment, ADR-0030 D2).

import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize

# ============================================================================
# PART 1 — CHARACTERIZATION
# ============================================================================
## Twin technique per `tsymex_phase15_A1_boolean.nim` /
## `tsymex_phase15_A2b_bitwise.nim` (read their headers for the convention):
## an "inline" SUT where the compound operand sits directly under the and/or
## RHS's comparison, paired with a "hoisted" twin that hand-lifts ONLY that
## operand into a `let` before the `if` — the exact transformation
## `parseAtomicOperand` performs automatically today. Twin verdict
## (and, for `sxSat`, witness) equality is the oracle: if the manufactured
## `rhsPreamble` entry silently changed anything observable, the twins would
## disagree.

proc checkTwins[T](rInline, rHoisted: SymexResult[T]) =
  check rInline.status == rHoisted.status
  if rInline.status == sxSat and rHoisted.status == sxSat:
    check rInline.witness == rHoisted.witness
  if rInline.status == sxRaised and rHoisted.status == sxRaised:
    check rInline.raisedTypeId == rHoisted.raisedTypeId
    check rInline.raisedWitness == rHoisted.raisedWitness

# ---------------------------------------------------------------------------
# Cell F — iekField: `box.x` as a comparison operand under a boolean AND's
# RHS. Field reads are unconditionally side-effect-free (no bounds, no
# division), so the hoisted twin lifts it unconditionally — no guard needed.
# ---------------------------------------------------------------------------
type H1FieldBox = object
  x: int

proc fieldRhsAnd(flag: bool, box: H1FieldBox) =
  if flag and box.x > 0:
    symexTarget("hit")

proc fieldRhsAndHoisted(flag: bool, box: H1FieldBox) =
  let tmp = box.x
  if flag and tmp > 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell I — iekIndex: `arr[j]` as a comparison operand under a boolean AND's
# RHS. `symexAssume` bounds `j` for the WHOLE proc (not just inside the
# and-chain), so the hoisted twin's unconditional `let tmp = arr[j]` is
# itself fault-free — the same "hoist only what's actually safe" discipline
# `tsymex_phase15_A1_boolean.nim`'s twins use, applied via a precondition
# instead of chain position since `rhsHasInlineDefectFork`'s `iekIndex` arm
# (dsl_parser.nim :755) treats a bare-var receiver/index as zero-fault
# regardless of chain position (array OOB is a separate, Nim-inserted
# raise-statement concern, not an inline defect-fork the index EXPRESSION
# itself carries).
# ---------------------------------------------------------------------------
proc indexRhsAnd(flag: bool, arr: array[5, int], j: int) =
  symexAssume(j >= 0 and j < 5)
  if flag and arr[j] > 0:
    symexTarget("hit")

proc indexRhsAndHoisted(flag: bool, arr: array[5, int], j: int) =
  symexAssume(j >= 0 and j < 5)
  let tmp = arr[j]
  if flag and tmp > 0:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# Cell C — iekContains: `x in mySet` as a comparison operand under a boolean
# AND's RHS. `in`/`contains`/`hasKey` on a `HashSet`/`Table` lowers to
# `iekContains` (dsl_parser.nim :2571-2577); wrapped in `== true` so the
# compound node sits in COMPARISON-OPERAND position (parseAtomicOperand's
# own chokepoint shape, dsl_parser.nim :1751-1752) rather than riding
# directly as the and/or's RHS, which never touches parseAtomicOperand at
# all (Mechanism constraint 1) — `rhsHasInlineDefectFork`'s `iekContains` arm
# (dsl_parser.nim :769) is zero-fault here: both `mySet` and `x` are bare
# vars.
# ---------------------------------------------------------------------------
proc containsRhsAnd(flag: bool, x: int, mySet: HashSet[int]) =
  if flag and (x in mySet) == true:
    symexTarget("hit")

proc containsRhsAndHoisted(flag: bool, x: int, mySet: HashSet[int]) =
  let tmp = x in mySet
  if flag and tmp == true:
    symexTarget("hit")

suite "symex H1 — isAtomicIR shape-coupling characterization corpus":

  test "walker version floor: symexWalkerVersion >= 73 (no behavior change; audit/tests only)":
    check parseInt(symexWalkerVersion) >= 73

  test "cell F (obj.field comparison operand under AND RHS): twin-identical, sxSat":
    let rInline  = symexFind(fieldRhsAnd, tLabel("hit"))
    let rHoisted = symexFind(fieldRhsAndHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell I (arr[j] comparison operand under AND RHS, in-bounds): twin-identical, sxSat":
    let rInline  = symexFind(indexRhsAnd, tLabel("hit"))
    let rHoisted = symexFind(indexRhsAndHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

  test "cell C (x in mySet comparison operand under AND RHS): twin-identical, sxSat":
    let rInline  = symexFind(containsRhsAnd, tLabel("hit"))
    let rHoisted = symexFind(containsRhsAndHoisted, tLabel("hit"))
    check rInline.status == sxSat
    checkTwins(rInline, rHoisted)

# ============================================================================
# PART 2 — AUDIT (permanent regression net)
# ============================================================================
## Sibling to `tsymex_phase15_N2_kindgate_audit.nim` — same `staticRead` +
## pure-Nim string-scan mechanism, same TOT-1 rationale (a slice-close grep
## audit proves completeness ONCE; nothing stops a later edit from
## reintroducing an un-audited shape-peek — the fix is a committed test that
## runs on every future compile, not a discipline that has to be
## remembered).
##
## What this scans, and what it deliberately does not
## ----------------------------------------------------------------------------
## RFC-parser-normalization round 2 finding R2-2 widened the scope below from
## the original two files (H1's one-time manual inventory) to a PRINCIPLED
## boundary: every module that consumes `IRExpr` DOWNSTREAM of
## `parseAtomicOperand`.
##
## Round 3 findings R3-2/R3-3 corrected two gaps in that boundary:
##
## R3-2 (fragment blind spot): `runtime.nim` textually `include`s FIVE
## fragment files — `runtime_strings.nim`, `runtime_floats.nim`,
## `runtime_exceptions.nim`, `runtime_closures.nim`, `runtime_heap.nim` (see
## `runtimeIncludedFragments` below for the exact list, kept in lockstep with
## reality by the include-graph guard). `staticRead("runtime.nim")` reads the
## raw file text and sees only the `include "..."` DIRECTIVE lines, never the
## fragment bodies Nim's compiler splices in at compile time — so a fragment
## not ALSO staticRead and scanned on its own is invisible to this audit no
## matter what its header claims. Before this fix, `runtime_floats.nim`,
## `runtime_exceptions.nim`, and `runtime_closures.nim` were exactly that:
## unscanned despite being downstream IR-lowering arms, same as
## `runtime_strings.nim`/`runtime_heap.nim`. All three were verified by hand
## to have ZERO subfield `iek*`-kind peeks as of this fix, so widening the
## scan to cover them required NO new `isExemptedLine` entries — but nothing
## structural PREVENTED that from being false; the previous "every module
## that consumes IRExpr downstream" header claim was aspirational, not
## actually enforced for three of the five fragments.
##
## R3-3 (no drift guard): the scanned-file set — the five `staticRead` consts
## and five `scanForSubfieldIekShapePeeks` calls below — is a hand-maintained
## list with no structural tie to what `runtime.nim` actually `include`s.
## Nothing stopped a future SIXTH fragment from shipping the same way the
## first three did: silently unscanned. The fix is the include-graph guard
## test below (`extractIncludedFragmentNames` + `runtimeIncludedFragments`):
## it parses the ALREADY-staticRead `runtime.nim` content for `include
## "<name>.nim"` lines and asserts every name it finds is a member of
## `runtimeIncludedFragments`, so a future `include` directive in
## `runtime.nim` that isn't ALSO added there (and given its own `staticRead`
## + scan call) turns this audit RED at compile time — closing the gap
## structurally instead of relying on the same manual discipline that missed
## the first three fragments.
##
## Scanned vs. excluded, and why (the honest disposition list this header
## used to paper over with a single "every module" claim)
## ----------------------------------------------------------------------------
## SCANNED (staticRead + `scanForSubfieldIekShapePeeks`, below):
##   * `runtime.nim` — the walker's own body (outside its five `include`d
##     fragments).
##   * `runtime_strings.nim`, `runtime_floats.nim`, `runtime_exceptions.nim`,
##     `runtime_closures.nim`, `runtime_heap.nim` — the five fragments
##     `runtime.nim` `include`s; each is a distinct file on disk, so each
##     needs its OWN `staticRead` (Nim's `include` is invisible to
##     `staticRead`, per R3-2 above) and its own scan call.
##   * `abstraction.nim` — the promotion/proof-obligation layer, a direct
##     downstream `IRExpr` consumer.
##   * `canonicalize.nim` — direct downstream `IRExpr` consumer; zero
##     subfield IR-kind shape-peeks as of this writing.
##
## EXCLUDED, with each module's actual relationship to `IRExpr` stated
## honestly rather than folded into a blanket completeness claim:
##   * `dsl_parser.nim` — the PRODUCER, not a consumer: its subfield peeks
##     (`isAtomicIR`, `rhsHasInlineDefectFork`, …) ARE the atomization logic
##     this audit polices, not code subject to it.
##   * `dsl.nim` — front-end re-export façade only (Layer 3 of the predicate
##     DSL); zero `IRExpr`/`iek*` references, nothing to scan.
##   * `dsl_typebridge.nim` — type layer (Layer 2): `typedesc` → `IRType`
##     classification, upstream of `IRExpr` entirely; zero `IRExpr`/`iek*`
##     references.
##   * `types.nim` — defines the `IRExprKind` enum (`iek*`) and `IRExpr`
##     itself; every `iek*` occurrence there is a type/enum DEFINITION, not a
##     subfield shape-peek on an already-constructed `IRExpr` value.
##   * `scan.nim` — walks `IRStmt` (macro-time target/assert/index discovery)
##     via `case s.kind` self-dispatch only; never peeks an `IRExpr`
##     sub-node's kind through a receiver chain, so it is structurally outside
##     this audit's scan shape (see the "deliberately EXCLUDES" note below),
##     not merely unscanned by omission.
##   * `stdlib_models.nim` — a name/receiver-kind registry for stdlib proc
##     interception; its `iek*` occurrences are all in comments, no code-level
##     shape-peeks.
##   * `exn_hierarchy.nim` — static exception-type ancestry table; no
##     `IRExpr`/`iek*` involvement at all.
##   * `regex_parser.nim` — self-contained Nim-regex → Z3-regex string
##     parser; its own header states NO walker/`IRExpr` dependency.
##
## NEW standalone modules require a MANUAL update to this scanned-file list
## (const block + scan calls, and this disposition comment) — the
## include-graph guard only covers the fragment class (`runtime.nim`'s
## `include`s), which is where downstream lowering arms actually live. This
## limitation is stated here rather than silently claimed away.
##
## Scans for SUBFIELD IR-kind shape-peeks: a pattern of the form
## `.<identifier>.kind ==` / `!=` / `in {...}` / `notin {...}` whose
## right-hand side names one or more `iek*` kinds — i.e. a check on the kind
## of some SUB-EXPRESSION reached through a field access (`e.lhs.kind`,
## `e.container.kind`, `stmt.cargs[i].kind`, …), not on the CURRENT node's
## own kind.
##
## This deliberately EXCLUDES two shapes:
##   - the walker's own `case e.kind` / `of iekX:` dispatch arms — ordinary
##     recursion over the current node, not a peek at ANOTHER node's shape.
##     (Structurally excluded: `of`-arm case labels never use `==`/`!=`/
##     `in {`, so this scan's operator-based match never reaches them.)
##   - a BARE single-level self-check, `e.kind == iekX` / `e.kind in {…}`,
##     on the immediate parameter itself (no receiver chain) — the same
##     "ordinary recursion" shape as a case dispatch, just spelled with an
##     explicit comparison instead of `of`. `lowerLeafInExpr`'s container
##     assert (`runtime.nim` — `doAssert e.kind in {iekVar, iekField,
##     iekStrBytes}`, one of H1's two verified non-A2a-reachable sites) is
##     exactly this shape: `e.kind` has only ONE dot, so
##     `receiverHasPrecedingDot` below reports false and the scan never
##     matches it — no runtime exemption is needed for it (documented here
##     for completeness, matching the finding's own site inventory, since
##     it legitimately admits the compound `iekField` kind that this scan
##     would otherwise flag as a violation if it were ever restructured
##     into a genuine subfield chain).
## `svKind` comparisons (`recv.kind == svArray`, `sv.kind in {svBool, …}`)
## are filtered by requiring at least one `iek`-prefixed identifier on the
## right-hand side — `SymVal`'s runtime-value kind is a different
## vocabulary entirely, out of this audit's scope (H1's finding explicitly
## calls out `runtime_strings.nim`:575/578/586 as irrelevant for exactly
## this reason).
##
## Every `iek*` kind this scan finds must be in exactly one of:
##   (a) `isAtomicIRAllowlist` — mirrors `isAtomicIR`'s own set verbatim
##       (dsl_parser.nim ~:1252-1253).
##   (b) `bareAtomicSet` — the literal/var kinds atomic BY CONSTRUCTION
##       (single leaf, no sub-expressions): `iekIntLit`, `iekStrLit`,
##       `iekVar`. A strict subset of (a); kept separate per H1's own
##       three-way category split.
##   (c) a documented, line-fingerprinted exemption (mirrors
##       `isGenericParamsNodeBodyLine`'s convention in the N2 audit) —
##       seeded with `runtime.nim`'s var-param write-back check
##       (`stmt.cargs[i].kind == iekVar`, `#140`'s call-site aliasing
##       detection): a genuine two-level subfield chain this scan WOULD
##       flag, except the kind it checks (`iekVar`) is already atomic by
##       construction, and the check itself never influences operand
##       hoisting — it identifies which formal params alias a var-argument
##       for post-call write-back, entirely outside `parseAtomicOperand`'s
##       reach (call arguments are built via plain `parseExpr`,
##       dsl_parser.nim ~:2712, never through the chokepoint). Documented
##       as an exemption anyway, per H1's own verified-site inventory, so
##       a future reader sees the rationale rather than re-deriving it.
## A future shape-peek on a kind outside (a)/(b)/(c) — e.g. a new site
## checking `e.lhs.kind == iekBinop`, the exact class of bug this finding
## is about — turns this audit RED.

const
  runtimeSrc            = staticRead("../src/nelli/smt/runtime.nim")
  runtimeStringsSrc     = staticRead("../src/nelli/smt/runtime_strings.nim")
  runtimeFloatsSrc      = staticRead("../src/nelli/smt/runtime_floats.nim")
  runtimeExceptionsSrc  = staticRead("../src/nelli/smt/runtime_exceptions.nim")
  runtimeClosuresSrc    = staticRead("../src/nelli/smt/runtime_closures.nim")
  runtimeHeapSrc        = staticRead("../src/nelli/smt/runtime_heap.nim")
  abstractionSrc        = staticRead("../src/nelli/smt/abstraction.nim")
  canonicalizeSrc       = staticRead("../src/nelli/smt/canonicalize.nim")

  runtimeIncludedFragments = ["runtime_strings.nim", "runtime_floats.nim",
                               "runtime_exceptions.nim", "runtime_closures.nim",
                               "runtime_heap.nim"]
    ## Every fragment `runtime.nim` `include`s (R3-2), kept in lockstep with
    ## the `staticRead` consts and `scanForSubfieldIekShapePeeks` calls above
    ## by the include-graph guard test below. Adding a new `include "..."`
    ## line to `runtime.nim` without adding its name here (plus its own
    ## `staticRead` const and scan call) turns that guard test RED.

type
  KindViolation = object
    file:     string
    lineNo:   int
    lineText: string
    kindName: string

proc isCommentLine(trimmed: string): bool =
  ## Nim `#`/`##` doc and ordinary comments both start with `#` once leading
  ## whitespace is stripped. Prose narrating `iek*` tokens (this file's own
  ## header included) must never trip the scanner.
  trimmed.startsWith("#")

proc isIdentChar(c: char): bool = c.isAlphaNumeric or c == '_'

proc matchesAt(s: string, i: int, lit: string): bool =
  i >= 0 and i + lit.len <= s.len and s[i ..< i + lit.len] == lit

const
  isAtomicIRAllowlist = ["iekIntLit", "iekBoolLit", "iekFloatLit", "iekStrLit",
                          "iekVar", "iekStrAt", "iekStrLen", "iekSeqLen"]
    ## MUST mirror `isAtomicIR`'s own set verbatim (dsl_parser.nim
    ## ~:1252-1253). A future `isAtomicIR` widening that forgets to update
    ## this const does not silently pass: the newly-admitted kind's
    ## existing shape-peeks (if any) keep whatever classification they had
    ## before, and any NEW shape-peek against it still needs a real
    ## audit-category home — this const drifting stale is a maintenance
    ## hazard flagged by code review, the same way N2's `routineNodeVocab`
    ## is maintained.
  bareAtomicSet = ["iekIntLit", "iekStrLit", "iekVar"]
    ## The literal/var kinds atomic BY CONSTRUCTION, independent of
    ## `isAtomicIR`'s own membership — a strict subset of
    ## `isAtomicIRAllowlist`, kept separate per H1's category (b).

proc receiverHasPrecedingDot(s: string, dotBeforeKind: int): bool =
  ## `s[dotBeforeKind] == '.'`, the dot immediately introducing `.kind`.
  ## Walks BACKWARD over the receiver segment — identifier characters, plus
  ## one optional trailing balanced `[...]` index suffix (e.g.
  ## `cargs[i]`) — and reports whether that segment is itself immediately
  ## preceded by ANOTHER `.` (a true `X.receiver.kind` SUBFIELD chain), as
  ## opposed to a bare `receiver.kind` where `receiver` is a plain
  ## local/param name (the walker's own self-kind-check shape — see the
  ## header's exclusion discussion).
  var j = dotBeforeKind - 1
  if j >= 0 and s[j] == ']':
    var depth = 1
    dec j
    while j >= 0 and depth > 0:
      if s[j] == ']': inc depth
      elif s[j] == '[': dec depth
      dec j
  while j >= 0 and isIdentChar(s[j]):
    dec j
  j >= 0 and s[j] == '.'

proc extractIekIdentsAfterOperator(s: string, opStart: int): seq[string] =
  ## `s[opStart..]` starts immediately after the matched `.kind` (whitespace
  ## not yet skipped). Recognises the three comparison forms `isAtomicIR`'s
  ## own shape-peek sites use — `==`, `!=`, `in {...}` / `notin {...}` — and
  ## returns only the `iek`-prefixed identifiers on the right-hand side (an
  ## `svKind` comparison yields none, which the caller treats as "not a
  ## match").
  var i = opStart
  while i < s.len and s[i] in {' ', '\t'}: inc i
  var isEqNe = false
  var isIn = false
  if matchesAt(s, i, "=="):
    isEqNe = true; i += 2
  elif matchesAt(s, i, "!="):
    isEqNe = true; i += 2
  elif matchesAt(s, i, "notin") and (i + 5 >= s.len or not isIdentChar(s[i + 5])):
    isIn = true; i += 5
  elif matchesAt(s, i, "in") and (i + 2 >= s.len or not isIdentChar(s[i + 2])):
    isIn = true; i += 2
  else:
    return @[]
  while i < s.len and s[i] in {' ', '\t'}: inc i
  if isEqNe:
    var j = i
    while j < s.len and isIdentChar(s[j]): inc j
    let tok = s[i ..< j]
    if tok.startsWith("iek"): result.add tok
  elif isIn:
    if i >= s.len or s[i] != '{': return @[]
    var j = i + 1
    var cur = ""
    while j < s.len and s[j] != '}':
      if isIdentChar(s[j]):
        cur.add s[j]
      else:
        if cur.startsWith("iek"): result.add cur
        cur = ""
      inc j
    if cur.startsWith("iek"): result.add cur

proc extractIncludedFragmentNames(s: string): seq[string] =
  ## R3-3 include-graph guard. Pure string scan (same style as this file's
  ## other scanners) over the already-`staticRead` `runtime.nim` content for
  ## `include "<name>.nim"` directive lines, returning each quoted fragment
  ## name. The caller asserts every name found here is a member of
  ## `runtimeIncludedFragments` — so a future `include` added to
  ## `runtime.nim` that isn't ALSO staticRead and scanned above turns that
  ## assertion RED, closing the "hand-maintained list with no structural
  ## drift guard" gap (R3-3) rather than relying on a reviewer noticing.
  for rawLine in s.splitLines():
    let trimmed = rawLine.strip()
    if trimmed.startsWith("include \""):
      let afterQuote = trimmed["include \"".len .. ^1]
      let endQuote = afterQuote.find('"')
      if endQuote > 0:
        result.add afterQuote[0 ..< endQuote]

proc isExemptedLine(fname, trimmed: string): bool =
  ## H1's one CODE-level exemption (category (c) above): `runtime.nim`'s
  ## var-param write-back check. Matched by exact trimmed text — the same
  ## robust-marker convention `isGenericParamsNodeBodyLine` uses in the N2
  ## audit (never a line number, which rots the moment the file is edited
  ## above it).
  fname == "src/nelli/smt/runtime.nim" and
    trimmed == "if formal.isVar and stmt.cargs[i].kind == iekVar:"

proc scanForSubfieldIekShapePeeks(fname, contents: string,
                                   violations: var seq[KindViolation]) =
  var lineNo = 0
  for rawLine in contents.splitLines():
    inc lineNo
    let trimmed = rawLine.strip()
    if trimmed.len == 0 or isCommentLine(trimmed) or isExemptedLine(fname, trimmed):
      continue
    var i = 0
    while i < rawLine.len:
      if matchesAt(rawLine, i, "kind") and i > 0 and rawLine[i - 1] == '.' and
         (i + 4 >= rawLine.len or not isIdentChar(rawLine[i + 4])):
        if receiverHasPrecedingDot(rawLine, i - 1):
          for kindName in extractIekIdentsAfterOperator(rawLine, i + 4):
            if kindName notin isAtomicIRAllowlist and kindName notin bareAtomicSet:
              violations.add KindViolation(file: fname, lineNo: lineNo,
                lineText: rawLine, kindName: kindName)
        i += 4
      else:
        inc i

suite "symex H1 — isAtomicIR shape-coupling permanent audit":

  test "zero subfield IR-kind shape-peeks against a kind outside isAtomicIR / the atomic literal-var set / the documented exemptions":
    var violations: seq[KindViolation]
    scanForSubfieldIekShapePeeks("src/nelli/smt/runtime.nim", runtimeSrc, violations)
    scanForSubfieldIekShapePeeks("src/nelli/smt/runtime_strings.nim",
                                  runtimeStringsSrc, violations)
    scanForSubfieldIekShapePeeks("src/nelli/smt/runtime_floats.nim",
                                  runtimeFloatsSrc, violations)
    scanForSubfieldIekShapePeeks("src/nelli/smt/runtime_exceptions.nim",
                                  runtimeExceptionsSrc, violations)
    scanForSubfieldIekShapePeeks("src/nelli/smt/runtime_closures.nim",
                                  runtimeClosuresSrc, violations)
    scanForSubfieldIekShapePeeks("src/nelli/smt/runtime_heap.nim",
                                  runtimeHeapSrc, violations)
    scanForSubfieldIekShapePeeks("src/nelli/smt/abstraction.nim",
                                  abstractionSrc, violations)
    scanForSubfieldIekShapePeeks("src/nelli/smt/canonicalize.nim",
                                  canonicalizeSrc, violations)
    if violations.len > 0:
      var report = "\nFound " & $violations.len &
        " subfield IR-kind shape-peek(s) against a kind outside " &
        "isAtomicIR's allowlist / the always-atomic literal-var set / the " &
        "documented exemption list:\n"
      for v in violations:
        report.add "  " & v.file & ":" & $v.lineNo & ":  " & v.lineText.strip() &
          "  (kind: " & v.kindName & ")\n"
      report.add "Either widen isAtomicIR's allowlist (dsl_parser.nim), with " &
        "a completeness audit of the D1c fast-path-pollution hazard its own " &
        "doc comment describes, or add this site to isExemptedLine with a " &
        "one-line rationale, per RFC-parser-normalization round 1 finding H1 " &
        "(#146)."
      checkpoint(report)
    check violations.len == 0

  test "include-graph guard (R3-3): every runtime.nim `include \"...\"` fragment is in the scanned-file list":
    ## R3-2/R3-3 (RFC-parser-normalization #146 round 3). Structurally ties
    ## the scanned-file set to what `runtime.nim` actually `include`s, so a
    ## future sixth fragment fails THIS assertion the moment it's added,
    ## rather than silently riding along unscanned the way
    ## `runtime_floats.nim`/`runtime_exceptions.nim`/`runtime_closures.nim`
    ## did before this fix.
    let included = extractIncludedFragmentNames(runtimeSrc)
    check included.len > 0  ## sanity: the scan itself must find runtime.nim's
                             ## known includes, or this guard is vacuous.
    for name in included:
      checkpoint("runtime.nim includes: " & name)
      check name in runtimeIncludedFragments

  test "walker version floor: symexWalkerVersion >= 73 (H1 is tests+docs only, no walker bump)":
    check parseInt(symexWalkerVersion) >= 73
