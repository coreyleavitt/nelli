## Round-6 N21 fix slice (walker v95) -- CONFIRMED Critical soundness bug,
## re-review verifier probe (`docs/RFC-chapulin-hardening.handoff.md`, N21).
##
## ROOT CAUSE: `tryRecognizePairLoopIdiom` (`dsl_parser.nim` ~5273) replaces
## the WHOLE `readOptions` pair-loop with `if iekStrInOptionRegion(s, i,
## bound): <empty block> else: <k-unroll fallback>` -- the member branch's
## empty block asserts "no defect possible on any member string". But the
## OLD region grammar (`runtime_strings.nim` 710-746) was bare segment-star,
## `((nonzero)* "\0")*` -- NO parity constraint tying it to how the real
## loop actually consumes the region. The real pair-loop reads a KEY, and
## only reads a VALUE (the second half of the pair) when the key is
## non-empty; it terminates cleanly either by (a) an empty-key segment
## (`break`, real chapulin's canonical double-NUL wire shape) or (b) the
## counter landing EXACTLY on `bound` after a whole number of complete
## pairs (the `while i < bound` guard itself going false, no `break`
## needed). The old grammar accepted ANY sequence of NUL-terminated
## segments regardless of parity -- so an ODD number of segments with a
## non-empty final segment (e.g. `"aa\x00bb\x00cc\x00"`, 3 segments) was
## wrongly accepted as a member, even though the real SUT reads key "cc" at
## the top of a third (uncompleted) pair, leaving the offset at `bound`,
## and the subsequent VALUE read immediately raises `ScanError`
## ("unterminated") since there is nothing left to scan.
##
## THE FIX (`runtime_strings.nim`'s `iekStrInOptionRegion` arm): the region
## grammar is strengthened to the pair-loop's ACTUAL clean-termination
## language --
##   PAIR   = (nonzero)+ "\0" (nonzero)* "\0"          -- one (key,value)
##            pair; key non-empty (else the loop would have broken instead
##            of reading a value), value may be empty.
##   REGION = PAIR* ( "\0" anybyte* )?
## i.e. zero or more complete pairs, OPTIONALLY followed by a lone
## terminator NUL (the empty-key segment that triggers `break`) with
## everything after that NUL entirely unconstrained (the loop never reads
## past it). Built with the SAME nim-z3 regex primitives the old grammar
## already used (`range`/`star`/`concat`/`matches`), plus `plus` (key must
## be non-empty) and `option` (the trailing terminator is OPTIONAL -- the
## natural "exactly N whole pairs, counter lands on bound" exit needs no
## terminator at all). Both exit shapes of the real loop are represented;
## neither is privileged.
##
## GROUND TRUTH VERIFICATION (per this slice's own instructions: hand-derive
## then CONFIRM against the concrete SUT, never guess). A throwaway concrete
## (non-symbolic) Nim script exercising `readCStringOpt`/`readOptionsSut`
## (byte-identical shapes to `tsymex_r6_b6_optionregion.nim`'s own) was
## compiled and run in the container for every literal pinned below. Two
## corrections that concrete run produced, against a naive guess:
##   - An even-pair region with NO trailing terminator (`"aa\x00bb\x00"`,
##     exactly 2 whole pairs) does NOT raise: the outer loop's own guard
##     `i < s.len` sees `i == s.len` (6 == 6) BEFORE any further read is
##     attempted, and exits cleanly. (A naive trace that forgets to
##     re-check the outer guard before assuming a next key-read happens
##     would wrongly predict a raise here -- this file pins the VERIFIED
##     behavior, not the naive guess.)
##   - Both empty-region edges (`""` and `"\x00"`) are ALSO clean under the
##     corrected grammar (0 real iterations / one immediate empty-key
##     break, respectively) -- the same verdict the OLD grammar already
##     produced for these two literals by coincidence (they are two of the
##     few shapes where bare segment-star and the corrected pair-grammar
##     agree). So the empty-region edge is NOT part of the wrong-verdict
##     class this slice fixes; it is pinned here as a regression lock, not
##     a behavior change.
##
## UNSAT-COMPANION HONESTY NOTE (requirement v): every "-unsat" pin below
## that queries `tRaisedExn("ScanError")` for a literal that IS a genuine
## member of the corrected grammar (N21-2-unsat, N21-3-unsat) -- and even
## the "done"-target unreachability companion for the ORIGINAL confirmed-bug
## literal (N21-1-unsat) -- honestly declines to `sxUnknown` rather than
## proving `sxUnsat`. This was hand-verified NOT to be a residual of this
## fix: it reproduces identically for the empty receiver
## (`tests/tsymex_r6_n10_coverage_matrix.nim`'s pre-existing N10d-5-decline
## pin, unaffected by this slice -- both old and new grammar already agree
## the empty region is a member), so it is the SAME pre-existing, separately
## cataloged decline class (N20: "k-unroll fallback reports
## beBudgetExhausted even when assumed iterations fit under maxLoopUnwind").
## `tryRecognizePairLoopIdiom`'s own doc comment already explains why: the
## walker descends into BOTH branches of the member/non-member fork
## UNCONDITIONALLY, so proving a defect UNREACHABLE always routes through
## the fallback's own k-unroll guard machinery, which does not special-case
## a `symexAssume`-derived concrete bound. This slice's fix closes the
## FALSE-VERDICT class (wrong sxSat, wrong sxUnknown-instead-of-sxRaised);
## it does not, and was not asked to, additionally close N20's orthogonal
## decline. Per Invariant 3, `sxUnknown` is an HONEST outcome, never a wrong
## one -- the pins below assert that honesty explicitly rather than a
## sxUnsat this engine build cannot currently deliver for this shape.
##
## Content-bearing pins below use the REAL chapulin delimiter (`'\0'`) and
## are STATUS-ONLY plus REPLAY-VIA-THE-KNOWN-ASSUMED-LITERAL (never
## `r.witness` extraction) -- same discipline `tsymex_r6_b6_optionregion.nim`
## established: a pre-existing, orthogonal witness-EXTRACTION bug corrupts
## any SOLVED string whose model requires an embedded NUL byte, but does not
## apply to a literal forced via `symexAssume(s == "...")` and replayed
## directly through that same literal (not through `r.witness`).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

proc readCStringOpt(s: string, offset: int): (string, int) =
  ## Byte-identical to `tsymex_r6_b6_optionregion.nim`'s own tracer.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc readOptionsSut(s: string, start: int) =
  ## Byte-identical shape to `tsymex_r6_b6_optionregion.nim`'s own
  ## `readOptionsSut` -- the exact 5-statement pair-loop body
  ## `tryMatchPairLoopIdiomShape` recognizes. Safe to call concretely for
  ## replay (`symexTarget` is a documented no-op outside symex).
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = readCStringOpt(s, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringOpt(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("done")

# ---------------------------------------------------------------------------
# 1. THE confirmed bug repro: an odd number of segments with a non-empty
#    final segment -- old grammar wrongly certifies "no defect possible";
#    ground truth is a real ScanError raise (container-confirmed, see the
#    handoff doc's N21 entry).
# ---------------------------------------------------------------------------

suite "symex round-6 N21 -- odd-segment member-branch false-SAT (confirmed bug repro)":

  test "N21-1: three segments (aa,bb,cc), odd/non-empty-final -> the modeled ScanError raise is reachable (sxRaised)":
    ## Pre-fix engine verdict (bug report): sxUnknown (defect never modeled
    ## -- the member fast-path preempts the sound k-unroll fallback that
    ## would otherwise find this raise). Post-fix: the region no longer
    ## certifies this literal a member, so the fallback's own pre-existing
    ## ScanError modeling finds it, exactly as B6-5 already does for a
    ## different truncated shape.
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00cc\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tRaisedExn("ScanError"))
    check r.status == sxRaised

  test "N21-1-replay: concrete replay of the pinned literal raises ScanError (ground truth, container-verified)":
    expect ScanError:
      readOptionsSut("aa\x00bb\x00cc\x00", 0)

  test "N21-1-unsat: reaching the post-loop target for the same odd-segment literal is no longer falsely SAT":
    ## Pre-fix engine verdict (bug report and this file's own RED baseline):
    ## sxSat with a NON-REPLAYING witness -- the false-SAT this slice exists
    ## to close. Post-fix: the region is correctly non-member, so ONLY the
    ## fallback branch is reachable -- but PROVING "done" unreachable
    ## through that fallback requires a universal (validity) proof over its
    ## own k-unroll guard machinery, which is a SEPARATE, pre-existing
    ## decline class (N20 / N10d-5-decline in
    ## `tests/tsymex_r6_n10_coverage_matrix.nim`: "the fallback branch's own
    ## reachability is an honest budget decline, not sxUnsat" -- confirmed
    ## reproducible even for the SIMPLEST possible member shape, the empty
    ## receiver). This slice's fix eliminates the FALSE-SAT (the actually
    ## wrong verdict); it does not, and is not required to, additionally
    ## close N20's separate k-unroll-validity decline. HONESTY RULE: expect
    ## the classified `sxUnknown` decline, not sxUnsat.
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00cc\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 2. Even-pair, NO trailing terminator -- ground truth (container-verified,
#    corrects a naive guess): CLEAN, the outer loop guard itself ends the
#    loop with the counter landing exactly on `bound`. A genuine MEMBER
#    shape under the corrected grammar (PAIR* alone, no terminator needed).
# ---------------------------------------------------------------------------

suite "symex round-6 N21 -- even-pair no-terminator (counter lands exactly on bound)":

  test "N21-2: two whole pairs (aa,bb), no terminator -> reaches the post-loop target (sxSat)":
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

  test "N21-2-replay: concrete replay of the pinned literal completes without raising":
    readOptionsSut("aa\x00bb\x00", 0)   # unhandled raise would fail this test

  test "N21-2-unsat: the modeled ScanError raise for this member literal is an honest decline, not sxUnsat":
    ## Attempted UNSAT companion (requirement v). This IS a genuine MEMBER
    ## shape under the new grammar (PAIR* with zero leftover): the
    ## fallback's raise arm is semantically infeasible. But actually PROVING
    ## that through the fallback's own k-unroll hits the SAME pre-existing
    ## N20/N10d-5-decline class as N21-1-unsat above -- confirmed by
    ## `tests/tsymex_r6_n10_coverage_matrix.nim`'s own N10d-5-decline pin
    ## declining identically (sxUnknown, not the predicted sxUnsat) for the
    ## simplest possible member shape (the empty receiver), which both the
    ## OLD and NEW grammar already agree is a member -- so this is
    ## demonstrably NOT something the N21 grammar fix introduces or could
    ## close; it is orthogonal, pre-existing engine scope (the walker
    ## descends into BOTH branches of the member/non-member fork
    ## unconditionally, per `tryRecognizePairLoopIdiom`'s own doc comment,
    ## and the fallback's `mkShortCircuitWhile` guard re-check does not
    ## special-case a `symexAssume`-derived concrete bound). HONESTY RULE:
    ## expect sxUnknown.
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tRaisedExn("ScanError"))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 3. Properly double-NUL-terminated shape -- the canonical clean wire shape,
#    a genuine MEMBER under both the old and new grammar. Pinned alongside
#    its attempted UNSAT raise-companion (requirement v) -- see N21-2-unsat's
#    comment for why that companion honestly declines rather than proving
#    sxUnsat (a separate, pre-existing N20/N10d-5-decline class).
# ---------------------------------------------------------------------------

suite "symex round-6 N21 -- properly terminated (PAIR* + terminator)":

  test "N21-3: two pairs plus the empty-key terminator -> reaches the post-loop target (sxSat)":
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

  test "N21-3-replay: concrete replay of the pinned literal completes without raising":
    readOptionsSut("aa\x00bb\x00\x00", 0)

  test "N21-3-unsat: the modeled ScanError raise for this member literal is an honest decline, not sxUnsat":
    ## Same N20/N10d-5-decline class as N21-2-unsat above -- see that pin's
    ## comment for the full evidence trail. HONESTY RULE: expect sxUnknown.
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tRaisedExn("ScanError"))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 4. Empty-region edge -- NOT part of the wrong-verdict class (both old and
#    new grammar agree here; verified concretely, not a behavior change).
#    Pinned as a regression lock per this slice's own scope check.
# ---------------------------------------------------------------------------

suite "symex round-6 N21 -- empty-region edge (regression lock, not a behavior change)":

  test "N21-4a: empty receiver (0 iterations, guard false immediately) -> reaches the post-loop target (sxSat)":
    proc sut(s: string) =
      symexAssume(s == "" and s.len == 0)
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

  test "N21-4a-replay: concrete replay of the empty literal completes without raising":
    readOptionsSut("", 0)

  test "N21-4b: immediate empty-key terminator (\"\\x00\") -> reaches the post-loop target (sxSat)":
    proc sut(s: string) =
      symexAssume(s == "\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

  test "N21-4b-replay: concrete replay of the immediate-NUL literal completes without raising":
    readOptionsSut("\x00", 0)

# ---------------------------------------------------------------------------
# 5. Walker version pin.
# ---------------------------------------------------------------------------

suite "symex round-6 N21 -- walker version pin":

  test "walker version floor >= 95 (pair-loop member-branch pair-terminator grammar)":
    check parseInt(symexWalkerVersion) >= 95
