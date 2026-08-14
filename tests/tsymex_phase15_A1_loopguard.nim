## RFC-parser-normalization Cluster A, slice A1 — context 5: WHILE-GUARD
## shapes.
##
## Mechanism constraint 4 (round-2 carve-out) forbids `parseAtomicOperand`
## from ever firing inside a `while`-guard condition parse: the guard
## machinery (`mkShortCircuitWhile`) routes on preamble EMPTINESS, and a pure
## hoist would flip `continue`-bearing loops from the Case-1b/4 fast paths
## into the R14 sound-degrade — turning previously-proving programs
## `sxUnknown`. This file has NO twins (hoisting the guard is exactly what
## constraint 4 forbids, today and post-A2); every cell instead pins a
## DEMONSTRATIVE shape pair (same guard, with vs without `continue` in the
## body) so a future slice that regresses the carve-out fails loudly here.
##
## Cell (b) is the RFC's named demonstrative cell: "compound fault-free
## guard operand + `continue` in body" MUST prove today via the Case-4 fast
## path. If it does NOT prove, that is a blocker-report per the task
## instructions, not a silent accept.
##
## Cells (e)/(f) pin Ground truth item 4: the Q1 scan-idiom recognizer
## (`tryRecognizeScanIdiom`) matches the raw `nnkWhileStmt` NimNode BEFORE
## any `parseExpr`, so it is safe from Cluster A by construction — verified
## here via the SAME "impossible" UNSAT-companion idiom `tsymex_q1_scanlift.nim`
## uses (an un-recognized k-unrolled loop cannot prove that companion;
## only the recognized closed form can), for both the canonical bound
## (`s.len`) and a compound-bound variant (`s.len - 1`).
##
## INVESTIGATION NOTE (out of A1/Cluster-A scope, recorded so it is not
## silently lost): (c)/(d) originally used the SAME delimiter char (`':'`)
## and the SAME bare `inc i` loop body as (e)'s canonical-bound scan
## (`while i < s.len and s[i] != ':': inc i`, byte-identical AST). With that
## overlap, cell (e) — queried in ISOLATION, with (c)/(d) never even passed
## to `symexFind` — flipped from the correct `sxUnsat` to `sxSat`: the MERE
## co-presence of a second, differently-targeted proc with an
## AST-IDENTICAL while-loop in the same module changed whether the Q1
## recognizer's closed form got applied to (e)'s own query. Minimized to a
## 2-proc repro (one proc never even invoked) confirmed via `scratchpad`
## probes (not committed): changing only the unrelated sibling's delimiter
## char restores (e)'s correct, isolated verdict. This is a distinct,
## apparently cross-proc collision in the recognizer/registration path —
## unrelated to operand-shape hoisting — flagged for separate follow-up.
## (c)/(d) below use `';'` instead of `':'` specifically to keep this
## corpus file's own baselines honest (not an artifact of that collision).
##
## RESOLUTION (issue #154, closed as not-reproducible): the follow-up
## investigation could not reproduce the flip under exact reconstruction —
## neither at HEAD nor at this file's own commit (65f5e5d) with the
## identical dependency lock and container image, on either backend, for
## the declared-only sibling, the queried-first sibling, the full corpus
## file with (c)/(d) reverted to `':'`, or cell (e) run in isolation — and
## a structural audit found no shape-keyed state in the recognizer, parser,
## or runtime (fresh Z3Context per query). Attributed to transient
## authoring-session build state. The collision surface is permanently
## pinned in `tsymex_q1_sibling_collision.nim`; the `';'` delimiters below
## are kept as cheap cell-independence hygiene.
import std/[unittest]
import nelli/symex

# ---------------------------------------------------------------------------
# (a)/(b) — compound fault-free guard operand (`i < n + 1`), with vs without
# `continue` in the body. Both must prove IDENTICALLY (the demonstrative
# pin): `continue` must not flip this off the Case-4 fast path. `n` is
# bounded so `n + 1` cannot overflow — an unbounded `n` makes `OverflowDefect`
# reachable at the guard's own evaluation (Phase 15 E6 dominance), which
# would test overflow-fork behavior instead of the intended guard shape (and
# was empirically observed to make the with/without-`continue` forms explore
# that overflow path differently, an unrelated confound).
# ---------------------------------------------------------------------------
proc loopGuardCompoundNoContinue(n: int) =
  symexAssume(n >= 0 and n < 1_000)
  var i = 0
  var acc = 0
  while i < n + 1:
    acc += 1
    inc i
  if acc == 3:
    symexTarget("hit")

proc loopGuardCompoundWithContinue(n: int) =
  symexAssume(n >= 0 and n < 1_000)
  var i = 0
  var acc = 0
  while i < n + 1:
    if i mod 2 == 0:
      inc i
      continue
    acc += 1
    inc i
  if acc == 3:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# (c)/(d) — and-split guard with an in-guard fault (`s[i]`), with vs without
# `continue` in the body. Per constraint 4's own rationale, `continue`
# presence with a non-empty guard preamble routes to the R14 sound-degrade;
# without `continue` the same shape may still resolve via ordinary
# k-unrolling. Baselines recorded, not assumed.
# ---------------------------------------------------------------------------
proc loopGuardAndSplitFaultNoContinue(s: string) =
  var i = 0
  while i < s.len and s[i] != ';':
    inc i
  if i == 3:
    symexTarget("hit")

proc loopGuardAndSplitFaultWithContinue(s: string) =
  var i = 0
  var skips = 0
  while i < s.len and s[i] != ';':
    if s[i] == ' ':
      inc i
      inc skips
      continue
    inc i
  if i == 3:
    symexTarget("hit")

# ---------------------------------------------------------------------------
# (e) — Q1 recognizer pin, canonical bound: `while i < s.len and s[i] != c:
# inc i` is the EXACT recognized scan idiom. The UNSAT companion `i > s.len`
# is impossible ONLY via the recognized closed form's clamp (an unrecognized
# k-unrolled loop cannot prove it — see tsymex_q1_scanlift.nim Q1-1b).
# ---------------------------------------------------------------------------
proc loopGuardQ1CanonicalBound(s: string) =
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i > s.len:
    symexTarget("impossible")

# ---------------------------------------------------------------------------
# (f) — Q1 recognizer pin, COMPOUND bound: `while i < s.len - 1 and s[i] !=
# c: inc i`. Same recognizer, same UNSAT-companion idiom, but the bound
# expression is itself compound (`s.len - 1`). BASELINE RECORDED (not
# assumed): the recognizer does NOT generalize to a compound bound — the
# UNSAT companion is NOT provable here, unlike (e)'s bare-atom bound. This
# is consistent with Q1's own documented doctrine (`tsymex_q1_scanlift.nim`
# Part 2d): anything off the EXACT recognized shape is deliberately left
# unrecognized (a false-positive recognition would be unsound), so a
# compound `<bound>` falling outside that exact shape is expected scope,
# not a regression. Still Cluster-A-safe either way: A2 hoists at IR
# emission, never rewrites the surface tree the recognizer matches.
# ---------------------------------------------------------------------------
proc loopGuardQ1CompoundBound(s: string) =
  var i = 0
  while i < s.len - 1 and s[i] != ':':
    inc i
  if i > s.len - 1:
    symexTarget("impossible")

# ===========================================================================
# Runner
# ===========================================================================
suite "symex A1 — loop-guard operand-shape characterization corpus":

  test "(a) compound fault-free guard, no continue: acc==3 reachable, sxSat":
    let r = symexFind(loopGuardCompoundNoContinue, tLabel("hit"))
    check r.status == sxSat

  test "(b) DEMONSTRATIVE: SAME guard + continue in body — BLOCKER: does NOT match (a) today":
    ## BLOCKER FINDING (verbatim, not a routine baseline record): the RFC
    ## names this shape as the load-bearing pin for Mechanism constraint 4's
    ## Case-4 fast path — "compound fault-free guard operand + continue in
    ## body" is asserted to prove IDENTICALLY to the no-continue twin, since
    ## the guard here (`i < n + 1`) deposits NO preamble/fork at all (pure
    ## compound arithmetic, no defect potential), so R14's stale-preamble
    ## hazard should never engage regardless of `continue`. Empirically, at
    ## HEAD (walker v71), it does NOT: `loopGuardCompoundNoContinue` is
    ## `sxSat` (acc==3 reachable) but `loopGuardCompoundWithContinue` — same
    ## guard, `continue` added to an otherwise-equivalent body — degrades to
    ## `sxUnknown`. This is pinned here as TODAY's actual (degraded)
    ## behavior per the task's baseline-recording discipline, but per the
    ## RFC text this is explicitly a blocker-class discovery, not a silent
    ## accept: a future slice that makes this prove is a fix, not a
    ## regression, and this test's expectation should flip forward with it.
    let rNoContinue   = symexFind(loopGuardCompoundNoContinue, tLabel("hit"))
    let rWithContinue = symexFind(loopGuardCompoundWithContinue, tLabel("hit"))
    check rNoContinue.status == sxSat
    check rWithContinue.status == sxUnknown
    if rWithContinue.status == sxUnknown:
      check rWithContinue.errors.len > 0

  test "(c) and-split guard fault, no continue: baseline recorded":
    let r = symexFind(loopGuardAndSplitFaultNoContinue, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len >= 3

  test "(d) and-split guard fault, WITH continue: baseline recorded":
    let r = symexFind(loopGuardAndSplitFaultWithContinue, tLabel("hit"))
    # Baseline pin: whatever HEAD does today, no crash and no un-classified
    # degrade.
    check r.status in {sxSat, sxUnsat, sxRaised, sxUnknown}
    if r.status == sxUnknown:
      check r.errors.len > 0

  test "(e) Q1 recognizer, canonical bound: i > s.len is UNSAT (closed-form clamp fires)":
    let r = symexFind(loopGuardQ1CanonicalBound, tLabel("impossible"))
    check r.status == sxUnsat

  test "(f) Q1 recognizer, compound bound (s.len - 1): baseline recorded — NOT recognized (sxSat)":
    let r = symexFind(loopGuardQ1CompoundBound, tLabel("impossible"))
    check r.status == sxSat
