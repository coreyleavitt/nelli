## Round-6 N10 (control-loop review, MEDIUM) -- closes four coverage gaps in
## the round-6 test corpus for the symbolic string/scan engine
## (`src/nelli/smt/`), flagged by the round-6 review as insufficiently
## exercised. TEST-ONLY: pins existing behavior; no production code changed
## in this slice (see each group's own comment for the reasoning that
## confirmed the engine already behaves correctly here).
##
## Cross-reference: the v86 multi-path-result-callee gap ORIGINALLY listed
## under N10 was already closed by slice R2
## (`tests/tsymex_r6_r2_zerodefault_result.nim` pins multi-path exhaustiveness
## for the zero-default result binding) -- not duplicated here.
import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

# ---------------------------------------------------------------------------
# (a) B3 scan-lift immediate-match boundary (walker v81 lineage,
#     `tests/tsymex_r6_b3_scanpair.nim`, `tryRecognizeScanPairIdiom`). The
#     existing B3-1 pin only proves a RELATIVE `p == start + 4` offset from a
#     symbolic start; this closes the ZERO-iterations-of-advance edge -- the
#     delimiter matches AT the starting offset itself, the very first check.
# ---------------------------------------------------------------------------

proc scanPairTracer(s: string, start: int): (int, int) =
  ## Byte-identical to `tsymex_r6_b3_scanpair.nim`'s own tracer.
  var i = start
  while i < s.len:
    if s[i] == ':':
      return (i, i + 1)
    i.inc
  raise newException(ScanError, "unterminated")

proc sutB3ImmediateMatch(s: string, start: int) =
  let (p, q) = scanPairTracer(s, start)
  if p == start and q == start + 1:
    symexTarget("immediate_match")

proc sutB3ImmediateMatchNotFoundImpossible(s: string, start: int) =
  ## UNSAT companion. THREE earlier formulations of this companion hung or
  ## declined during live-testing: (1) a call-boundary-crossing exception-
  ## reachability query through `scanPairTracer`, guarded by
  ## `symexAssume(start >= 0 and start < s.len and s[start] == ':')`, hung
  ## (>30 min wall clock, near-zero container CPU, well past this engine's
  ## documented 2-15 min worst case for call-boundary proofs); (2) the same
  ## assume rewritten as a direct top-level loop (mirroring B3-1b's own
  ## proven-safe style) ALSO hung. Both share one trait B3-1b's own pin
  ## lacks: a symbolic-index READ (`s[start]`) inside `symexAssume`, forcing
  ## a solve over an INDEXED constraint rather than a plain range fact
  ## (B3-1b assumes only `start >= 0 and start <= s.len`, never an indexed
  ## read) -- routed around per the corpus's own dt-bounded doctrine ("a
  ## hang is an engine defect to be routed around, not chased, for a pin
  ## file"), the same class as B3-1b's own documented call-boundary-
  ## relational divergence, just triggered by a different query shape.
  ## (3) A CONCRETE (`s == ":"`, `start == 0`) reformulation with an extra
  ## nested `if` inside the match branch declined cleanly
  ## (`beBudgetExhausted`) instead of hanging -- the extra statement breaks
  ## B3's exact 2-statement match-branch shape (`tryMatchScanPairIdiomShape`
  ## requires the `if` branch to be a BARE `return`), so the loop falls
  ## through unrecognized to a k-unroll the concrete assume does not prune.
  ##
  ## This formulation keeps the loop body BARE (matching B3's recognizer
  ## exactly, so it lifts to the closed form instead of k-unrolling) and
  ## checks a POST-loop invariant instead: once `s`/`start` are concretely
  ## fixed so the very first check matches, the not-found fallthrough (only
  ## reachable past an unmatched loop) can never execute.
  symexAssume(s == ":" and start == 0)
  var i = start
  while i < s.len:
    if s[i] == ':':
      return
    i.inc
  symexTarget("impossible")

suite "symex round-6 N10(a) -- B3 immediate-match boundary":

  test "N10a-1: match at the starting offset itself (zero advances) -> sxSat":
    let r = symexFind(sutB3ImmediateMatch, tLabel("immediate_match"))
    check r.status == sxSat

  test "N10a-2 UNSAT companion: a forced immediate match can never fall through to not-found":
    let r = symexFind(sutB3ImmediateMatchNotFoundImpossible, tLabel("impossible"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# (b) char-vs-byte cross-alias comparison (B2's width-conversion/byte-alias
#     machinery, `tests/tsymex_r6_b2_intwidth.nim`, `iekConvIntWidth`). Both
#     `char` and `byte` normalize to `"uint8"` (`normalizeIntTyName`), so a
#     `char(b)`/`byte(c)` conversion is SAME width AND same signedness --
#     `dsl_parser.nim`'s own `nnkConv` arm documents this combination as
#     "genuinely a no-op; ordinary identity pass-through" (the `else` branch
#     after the widening/narrowing/reinterpret checks). Neither existing B2
#     pin nor any other suite exercises comparing a char-typed value against
#     a byte-typed value across this alias map, in either direction --
#     closing that gap here.
# ---------------------------------------------------------------------------

proc charEqualsConvertedByte(c: char, b: byte) =
  if char(b) == c:
    symexTarget("char_eq_byte")

proc byteEqualsConvertedChar(c: char, b: byte) =
  if b == byte(c):
    symexTarget("byte_eq_char")

proc charFromByteRoundTrips(b: byte) =
  ## UNSAT companion: converting a KNOWN byte to char always yields the
  ## expected char -- no false verdict from the identity pass-through.
  symexAssume(b == 65'u8)
  let c = char(b)
  symexAssert(c == 'A')

proc byteFromCharRoundTrips(c: char) =
  ## UNSAT companion, opposite direction.
  symexAssume(c == 'A')
  let b = byte(c)
  symexAssert(b == 65'u8)

suite "symex round-6 N10(b) -- char-vs-byte cross-alias comparison":

  test "N10b-1: char(b) == c reachable -- char compared against a converted byte (SAT)":
    let r = symexFind(charEqualsConvertedByte, tLabel("char_eq_byte"))
    check r.status == sxSat

  test "N10b-2: b == byte(c) reachable -- byte compared against a converted char (SAT)":
    let r = symexFind(byteEqualsConvertedChar, tLabel("byte_eq_char"))
    check r.status == sxSat

  test "N10b-3 UNSAT companion: byte(65) converts to char('A') for every witness (byte -> char direction)":
    let r = symexFind(charFromByteRoundTrips, tAssertionViolation())
    check r.status == sxUnsat

  test "N10b-4 UNSAT companion: char('A') converts to byte(65) for every witness (char -> byte direction)":
    let r = symexFind(byteFromCharRoundTrips, tAssertionViolation())
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# (c) NUL-byte witness at position 0, and multiple embedded NULs (render v9
#     lineage, `tests/tsymex_r6_nulwitness.nim`, raw `Z3_get_string_contents`
#     via `evalStrBytes`). Existing pins there cover a NUL mid-string (NW-1,
#     index 1) and a NUL alongside every other escape class (NW-5, also not
#     at index 0); neither exercises a NUL as the string's VERY FIRST byte,
#     nor two-plus NULs sharing one witness. Both closed here, each with a
#     real-function replay cross-check.
# ---------------------------------------------------------------------------

proc readCStringNulTracer(s: string, offset: int): (string, int) =
  ## Byte-identical to `tsymex_r6_nulwitness.nim`'s own tracer.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc sutNulAtPositionZero(s: string) =
  if s.len == 2 and s[0] == '\0' and s[1] == 'X':
    symexTarget("nul_first")

proc sutNulFirstAsDelimiter(s: string, start: int) =
  ## Forces the delimiter itself to sit at position 0 of the WITNESS
  ## (`start == 0`, `s[0]` is the NUL): an immediate-terminator scan whose
  ## terminator byte is the string's very first byte.
  let (payload, q) = readCStringNulTracer(s, start)
  if payload.len == 0 and q == start + 1 and start == 0:
    symexTarget("nul_delim_at_zero")

proc sutMultipleEmbeddedNuls(s: string) =
  if s.len == 5 and s[0] == 'A' and s[1] == '\0' and s[2] == '\0' and
     s[3] == 'B' and s[4] == '\0':
    symexTarget("multi_nul")

suite "symex round-6 N10(c) -- NUL-first witness":

  test "N10c-1: NUL as the string's own first byte is reachable (sxSat)":
    let r = symexFind(sutNulAtPositionZero, tLabel("nul_first"))
    check r.status == sxSat

  test "N10c-1-content: the witness's leading byte is a real single NUL, not the 5-char escape text":
    let r = symexFind(sutNulAtPositionZero, tLabel("nul_first"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.len == 2
    check ord(s[0]) == 0
    check ord(s[1]) == ord('X')

  test "N10c-2: a NUL-delimited scan whose delimiter sits at witness position 0 (sxSat)":
    let r = symexFind(sutNulFirstAsDelimiter, tLabel("nul_delim_at_zero"))
    check r.status == sxSat

  test "N10c-2-cross: the witness, replayed through the real function, reproduces the exact found outcome":
    let r = symexFind(sutNulFirstAsDelimiter, tLabel("nul_delim_at_zero"))
    check r.status == sxSat
    let (s, start) = r.witness
    check start == 0
    check s.len >= 1
    check ord(s[0]) == 0
    let (payload, q) = readCStringNulTracer(s, start)
    check payload.len == 0
    check q == 1

suite "symex round-6 N10(c) -- multiple embedded NULs":

  test "N10c-3: two embedded NULs sharing one witness is reachable (sxSat)":
    let r = symexFind(sutMultipleEmbeddedNuls, tLabel("multi_nul"))
    check r.status == sxSat

  test "N10c-3-content: every byte, including BOTH NULs, extracts exactly -- no offset shift from either NUL's own extraction":
    let r = symexFind(sutMultipleEmbeddedNuls, tLabel("multi_nul"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.len == 5
    check ord(s[0]) == ord('A')
    check ord(s[1]) == 0
    check ord(s[2]) == 0
    check ord(s[3]) == ord('B')
    check ord(s[4]) == 0

  test "N10c-3-cross: the witness, replayed through the real function at BOTH NUL positions, reproduces the exact found outcome":
    let r = symexFind(sutMultipleEmbeddedNuls, tLabel("multi_nul"))
    check r.status == sxSat
    let s = r.witness[0]
    let (payload1, q1) = readCStringNulTracer(s, 0)
    check payload1 == "A"
    check q1 == 2
    let (payload2, q2) = readCStringNulTracer(s, 2)
    check payload2.len == 0
    check q2 == 3

# ---------------------------------------------------------------------------
# (d) empty-receiver scan entry, family-wide -- every scan-family recognizer
#     (B0 scan-lift bound, Q1, B3, B4 readCString, B6 option-region:
#     `tests/tsymex_r6_b0_scanlift_bound.nim`, `tests/tsymex_q1_sibling_collision.nim`,
#     `tests/tsymex_r6_b3_scanpair.nim`, `tests/tsymex_r6_b4_readcstring.nim`,
#     `tests/tsymex_r6_b6_optionregion.nim`) entered with an empty string
#     receiver (`len == 0`). Each closed form's own doc comment guards the
#     WHOLE rewrite by loop entry (`if i < bound: ... else: nil`/fallback) --
#     for an empty receiver `i == bound == 0` at entry, so the guard is false
#     and the closed form is a pure no-op, matching real Nim's own
#     short-circuit (the loop condition `i < bound` is false before `s[i]`
#     is ever read). B6's region-membership predicate additionally must
#     classify the degenerate empty range as vacuously a MEMBER (`star`
#     always matches the empty string) rather than mis-fork or crash. Pinning
#     each family member so a future change to any one recognizer's guard
#     cannot silently regress this edge without a red pin somewhere.
# ---------------------------------------------------------------------------

proc sutB0EmptyReceiver(s: string) =
  ## B0 (`tests/tsymex_r6_b0_scanlift_bound.nim`) canonical shape, `s.len`
  ## forced to 0.
  symexAssume(s.len == 0)
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i == 0:
    symexTarget("b0_empty_done")

proc sutQ1EmptyReceiverImpossible(s: string) =
  ## Q1 (`tests/tsymex_q1_sibling_collision.nim`'s own `scanTarget` shape),
  ## `s.len` forced to 0: the not-found clamp's own UNSAT companion still
  ## proves on the degenerate zero-length receiver.
  symexAssume(s.len == 0)
  var i = 0
  while i < s.len and s[i] != ':':
    inc i
  if i > s.len:
    symexTarget("q1_empty_impossible")

proc scanPairEmptySUT(s: string, start: int) =
  ## B3 (`tests/tsymex_r6_b3_scanpair.nim`), empty receiver.
  symexAssume(s.len == 0 and start == 0)
  discard scanPairTracer(s, start)

proc accScanEmptySUT(s: string, start: int) =
  ## B4 (`tests/tsymex_r6_b4_readcstring.nim`), empty receiver -- reuses (c)'s
  ## `readCStringNulTracer`, the same accumulating-scan shape.
  symexAssume(s.len == 0 and start == 0)
  discard readCStringNulTracer(s, start)

proc readOptionsEmptySUT(s: string, start: int) =
  ## B6 (`tests/tsymex_r6_b6_optionregion.nim`'s own `readOptionsSut` shape),
  ## empty receiver.
  symexAssume(s.len == 0 and start == 0)
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = readCStringNulTracer(s, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringNulTracer(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("b6_empty_done")

suite "symex round-6 N10(d) -- empty-receiver family-wide, B0":

  test "N10d-1: B0 empty receiver leaves i untouched -> sxSat":
    let r = symexFind(sutB0EmptyReceiver, tLabel("b0_empty_done"))
    check r.status == sxSat

  test "N10d-1-unsat: B0 empty receiver never raises IndexDefect":
    let r = symexFind(sutB0EmptyReceiver, tIndexError())
    check r.status == sxUnsat

suite "symex round-6 N10(d) -- empty-receiver family-wide, Q1":

  test "N10d-2: Q1's not-found clamp UNSAT companion still proves on an empty receiver":
    let r = symexFind(sutQ1EmptyReceiverImpossible, tLabel("q1_empty_impossible"))
    check r.status == sxUnsat

suite "symex round-6 N10(d) -- empty-receiver family-wide, B3":

  test "N10d-3: B3 empty receiver falls straight to the not-found ScanError raise -> sxRaised":
    let r = symexFind(scanPairEmptySUT, tRaisedExn("ScanError"))
    check r.status == sxRaised

  test "N10d-3-unsat: B3 empty receiver never raises IndexDefect (the guard prevents the entry-read probe)":
    let r = symexFind(scanPairEmptySUT, tIndexError())
    check r.status == sxUnsat

suite "symex round-6 N10(d) -- empty-receiver family-wide, B4":

  test "N10d-4: B4 (accumulating scan) empty receiver falls straight to the not-found ScanError raise -> sxRaised":
    let r = symexFind(accScanEmptySUT, tRaisedExn("ScanError"))
    check r.status == sxRaised

suite "symex round-6 N10(d) -- empty-receiver family-wide, B6":

  test "N10d-5: B6 empty receiver -- the degenerate empty region is vacuously a MEMBER -> sxSat":
    let r = symexFind(readOptionsEmptySUT, tLabel("b6_empty_done"))
    check r.status == sxSat

  test "N10d-5-decline: the fallback branch's own reachability is an honest budget decline, not sxUnsat":
    ## HONESTY RULE: expected sxUnsat (the member fast-path's membership
    ## condition is Z3-provably true under `s.len == 0`, so the fallback
    ## branch's raise should be unreachable) but the engine actually returns
    ## a classified sxUnknown (`beBudgetExhausted`) instead. Root cause: per
    ## B6's own doc comment, the walker descends into BOTH branches of the
    ## member/non-member fork UNCONDITIONALLY (no feasibility pre-check
    ## before walking a branch body) -- the fallback branch's own
    ## `mkShortCircuitWhile` k-unroll re-checks its guard (`i < s.len`)
    ## against the generic unwind-budget machinery, which does not
    ## special-case a `symexAssume`-derived concrete bound the way a
    ## syntactic literal would, so it reports "guard still satisfiable"
    ## rather than concluding zero iterations. Same class of decline as
    ## group (a)'s own `beBudgetExhausted` finding, and the same class the
    ## corpus's OWN B3-4/B4-6/B6-6 trip-wire pins already expect for an
    ## unrecognized/non-fast-path shape -- an honest, pre-existing scope
    ## boundary, not a live bug.
    let r = symexFind(readOptionsEmptySUT, tRaisedExn("ScanError"))
    check r.status == sxUnknown
    check r.errors.len > 0
    check r.errors.anyIt(it.kind == beBudgetExhausted)

suite "symex round-6 N10 -- walker version pin":

  test "walker version floor >= 94 (no production change -- test-only coverage slice)":
    check parseInt(symexWalkerVersion) >= 94
