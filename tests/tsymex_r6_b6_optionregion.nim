## Round-6 B6 (ADR-0028 leg, option-region membership) — walker v84.
##
## Chapulin's `readOptions` is a PAIR-LOOP: a while loop that re-invokes a
## `readCString`-shaped helper (the B4 closed form, `tryRecognizeAccumulatingScan`)
## TWICE per iteration — once for a key, once for a value, chained (the
## second call's start is the first call's own returned offset, B5's own
## chaining machinery) — breaking on an empty key and accumulating
## `(key, val)` pairs into a `seq[(string,string)]`. This is the ADR-0028
## Q2 residue: cross-iteration state (the `pairs` accumulation) over an
## UNCONSTRAINED trip count — no finite `maxLoopUnwind` decides a query that
## genuinely needs more iterations than the budget (default 5).
##
## `tryRecognizePairLoopIdiom`/`tryMatchPairLoopIdiomShape` (`dsl_parser.nim`)
## recognize this exact 5-statement loop body shape and replace the WHOLE
## loop with a two-way fork on a NEW region-membership predicate
## (`iekStrInOptionRegion`, `types.nim`/`runtime_strings.nim`):
##   s[i .. bound-1] ∈ ((nonzero)* "\0")*
## built directly from nim-z3's sequence-regex primitives (`range`/`star`/
## `concat`/`matches` — the same machinery `iekStrStrip` already uses for
## `(union chars)*`). STAR inner segments, not plus (round-2 depth
## correction): the real `readCString` returns "" freely and `readOptions`
## accepts mid-region empty keys and all-empty values, with the canonical
## double-NUL terminator itself an empty segment — `plus` would reject
## exactly the well-formed inputs a property search generates.
##
## `readOptionsSut` takes an explicit `start: int` param (not a bare `var i
## = 0`) SPECIFICALLY so the loop counter `i` (`var i = start`) rides
## `collectIntOffsetParams`'s EXISTING B4/B5 "wrapper" promotion (traces
## `start` -> the local rebind `i` -> `readCStringOpt`'s own traced
## `offset` param, one call boundary out — `dsl_parser.nim`, unchanged by
## this slice): `iekStrInOptionRegion`'s start/bound operands reuse
## `iekStrSubstr`'s CR-17 Int-sortedness discipline (a BV-represented
## bound declines rather than bv2int-bridging arithmetic into a
## Sequence-theory query — the same hang class CR-17 recorded), so `i`
## must arrive `svInt`, exactly like `iekStrSubstr`'s own LOW bound
## already requires in B3/B4. No NEW promotion machinery needed — this is
## the SAME mechanism B4 built for exactly this "wrapper calls a
## readCString-shaped helper" shape.
##
## MEMBER branch: certified defect-free by construction (empty — no
## statement in it can raise). NEITHER branch models the fold
## (`<pairs>.add(...)`) — not just the member branch: `itSeq[itTuple[
## string,string]]` has no backing in `allocateSeqDataRaw` this cycle (a
## recorded non-goal, the SAME gap the A6 exit-gate already flagged for
## `seq[(string,string)]` as a formal parameter), and dropping the fold
## from BOTH branches turned out to be load-bearing, not merely tidy: this
## engine's `isIf`/`isWhile` walker (`runtime.nim`) descends into every
## branch/iteration UNCONDITIONALLY (no feasibility pre-check before
## walking a branch body), and an unmodeled construct's Nim exception is
## caught only by `runSymexImpl`'s single top-level handler, which returns
## `sxUnknown` UNCONDITIONALLY — discarding any already-recorded `sxSat`
## witness. A syntactically-present-but-dynamically-infeasible `.add`
## would otherwise poison the ENTIRE query, member branch included. (A
## companion one-line rider in `lowerSeqLit`, `runtime.nim`, additionally
## makes the EMPTY-literal declaration `var pairs: seq[(string,string)] =
## @[]` itself walkable for ANY element type, not just supported ones — a
## length-0 literal seq needs no real backing array, since its `isIndex`
## OOB bound is unsatisfiable for every index, so `seqDataRaw` is never
## actually read on any live path.) Sound per the RFC's own "no verdict
## depends on them in the defect search" clause: every pin below probes
## reachability/raise-status, never `pairs`' or post-loop `i`'s content.
##
## NON-MEMBER branch: the SAME `mkShortCircuitWhile` k-unroll fallback
## every unrecognized loop shape already takes (minus the fold, per
## above), so a truncated/non-member region reaches the pre-existing
## modeled ScanError raise arm (B4's closed form, unchanged, inlined per
## real k-unrolled iteration) via ordinary per-iteration walking of the
## defect-relevant statements (both chained scans, the break-check, the
## index advance) — "per-prefix scoping, never all-or-nothing": a short
## truncated-after-one-valid-pair region still raises the REAL defect
## (pinned below), because the k-unroll fallback faithfully walks the
## valid leading pair before reaching the truncation, entirely on
## EXISTING B0/B3/B4/B5 machinery.
##
## All content-bearing pins below use the REAL chapulin delimiter, `'\0'`,
## and are STATUS-ONLY (never extract `r.witness`) — B4's file doc flags a
## pre-existing, orthogonal witness-EXTRACTION bug for any solved string
## whose model requires an embedded NUL byte (the byte round-trips as its
## own 5-character SMT-LIB escape text). Every pin here instead forces a
## KNOWN literal via `symexAssume(s == "...")` — a concrete ASSUMED
## constant, not an extracted model value, so the flagged bug does not
## apply (confirmed by B4's own precedent: asserting a NUL-bearing literal
## constraint is unaffected — only EXTRACTING a solved NUL-bearing string
## is broken).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

proc readCStringOpt(s: string, offset: int): (string, int) =
  ## B4's accumulating shape, real chapulin delimiter (`'\0'`) — the
  ## `readCString` twin `readOptions` calls twice per pair-loop iteration.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc readOptionsSut(s: string, start: int) =
  ## The canonical `readOptions` pair-loop shape `tryMatchPairLoopIdiomShape`
  ## recognizes: two chained `readCStringOpt` calls per iteration, break on
  ## an empty key, accumulate into `pairs`, advance `i` to the second call's
  ## returned offset. `start` is a real formal param (see file doc: this is
  ## what makes `i` ride the existing int-offset promotion).
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
# 1. Main defect proof (RFC Done-when: "a property over the option region
#    proves SAT/UNSAT rather than exhausting budget"). Four real pairs plus
#    the empty-key terminator segment needs 5 REAL outer-loop iterations to
#    reach the post-loop target through ordinary k-unrolling (default
#    `maxLoopUnwind` is 5) -- and the LAST of those five is itself the
#    empty-key break, so a strictly-less-than-5-real-iteration short-circuit
#    witness does not exist for this exact literal.
# ---------------------------------------------------------------------------

suite "symex round-6 B6 -- main option-region defect proof":

  test "B6-1: four-pair option region (5 real outer iterations) -> sxSat via the region-membership fast path":
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00cc\x00dd\x00ee\x00ff\x00gg\x00hh\x00\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

  test "B6-1-red: the SAME property, RECOGNIZER SHAPE BROKEN (non-.len bound), stays sxUnknown -- the RED baseline this pin retires":
    ## Structural trip-wire mirroring B6-1's exact literal/iteration count,
    ## but with a `let n = s.len` local-alias bound (same device as B6-6) so
    ## the recognizer does NOT fire and the loop takes the plain k-unroll
    ## path -- demonstrating, on THIS engine build, that budget exhaustion
    ## (not a solver limitation) is what B6's recognizer retires for the
    ## identical shape once the bound is syntactically `.len` again.
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00cc\x00dd\x00ee\x00ff\x00gg\x00hh\x00\x00")
      let n = s.len
      var pairs: seq[(string, string)] = @[]
      var i = 0
      while i < n:
        let (key, p1) = readCStringOpt(s, i)
        if key.len == 0:
          break
        let (val, p2) = readCStringOpt(s, p1)
        pairs.add((key, val))
        i = p2
      symexTarget("done")
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 2. Star-segment pins (RFC Done-when: empty-key / empty-value / double-NUL
#    pins -- "the star-segment cases plus would fail"). Each forces a
#    CONCRETE literal past the 5-iteration k-unroll horizon so the target
#    is reachable ONLY via the region-membership fast path (a `plus`-based
#    regex would reject the literal's empty segment, forcing the fallback,
#    which then budget-exhausts on these >5-real-iteration shapes -> a
#    real, falsifiable regression pin for the star-not-plus choice).
# ---------------------------------------------------------------------------

suite "symex round-6 B6 -- star-segment pins":

  test "B6-2 empty-key pin: the region's own terminator is a zero-length key segment, past the unroll horizon":
    ## Six real pairs then the empty-key terminator: 7 real outer
    ## iterations, well past `maxLoopUnwind` (5) -- the terminator's own
    ## empty segment ("\\0" with zero nonzero bytes before it) is exactly
    ## the star-not-plus case this pin exercises.
    proc sut(s: string) =
      symexAssume(s == "a1\x00b1\x00a2\x00b2\x00a3\x00b3\x00" &
                        "a4\x00b4\x00a5\x00b5\x00a6\x00b6\x00\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

  test "B6-3 empty-value pin: a genuinely empty VALUE segment mid-region, past the unroll horizon":
    ## Pair 3's value is empty ("k3\\0" immediately followed by "\\0") --
    ## `readCStringOpt` returns "" without breaking the loop (only an EMPTY
    ## KEY breaks it), so the loop continues to pair 4/5/6 and the
    ## terminator: 7 real outer iterations.
    proc sut(s: string) =
      symexAssume(s == "k1\x00v1\x00k2\x00v2\x00k3\x00\x00" &
                        "k4\x00v4\x00k5\x00v5\x00k6\x00v6\x00\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

  test "B6-4 double-NUL-terminator pin: the last value's terminator immediately followed by the empty-key terminator":
    ## The canonical wire shape: "...lastval" + "\\0" (ends the last VALUE
    ## segment) + "\\0" (the empty-KEY segment that breaks the loop) --
    ## two adjacent NUL bytes at the very end. Six real pairs precede it:
    ## 7 real outer iterations.
    proc sut(s: string) =
      symexAssume(s == "k1\x00v1\x00k2\x00v2\x00k3\x00v3\x00" &
                        "k4\x00v4\x00k5\x00v5\x00k6\x00v6\x00\x00")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# 3. Truncated-region fallback pin (RFC Done-when: non-member tail -> the
#    modeled ScanError raise arm / honest degrade; "the certified prefix
#    stays certified" -- one valid pair precedes the truncation, well
#    within k-unroll reach, so the fallback branch's ordinary per-iteration
#    walk faithfully processes it before reaching the real defect, entirely
#    on pre-existing B0/B3/B4/B5 machinery; no new fallback code in B6).
# ---------------------------------------------------------------------------

suite "symex round-6 B6 -- truncated-region fallback":

  test "B6-5: one valid pair then an unterminated key -> the modeled ScanError raise is reachable (sxRaised)":
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00cc")
      readOptionsSut(s, 0)
    let r = symexFind(sut, tRaisedExn("ScanError"))
    check r.status == sxRaised

# ---------------------------------------------------------------------------
# 4. Trip-wire -- a shape OUTSIDE the recognizer (bound not the scanned
#    string's own `.len`) still k-unrolls, proving the recognizer stays
#    narrow (mirrors B0/B3/B4/B5's own "local alias bound" / "non-.len
#    bound" trip-wires).
# ---------------------------------------------------------------------------

suite "symex round-6 B6 -- trip wire (recognizer stays narrow)":

  test "B6-6: non-.len outer bound is NOT recognized -> sxUnknown (unchanged, real trip-wire)":
    proc sut(s: string) =
      symexAssume(s == "aa\x00bb\x00cc\x00dd\x00ee\x00ff\x00gg\x00hh\x00\x00")
      let n = s.len
      var pairs: seq[(string, string)] = @[]
      var i = 0
      while i < n:
        let (key, p1) = readCStringOpt(s, i)
        if key.len == 0:
          break
        let (val, p2) = readCStringOpt(s, p1)
        pairs.add((key, val))
        i = p2
      symexTarget("done")
    let r = symexFind(sut, tLabel("done"))
    check r.status == sxUnknown

suite "symex round-6 B6 -- walker version pin":

  test "walker version floor >= 84 (option-region star-segment membership for the readOptions pair-loop)":
    check parseInt(symexWalkerVersion) >= 84
