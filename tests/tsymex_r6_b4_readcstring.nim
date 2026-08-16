## Round-6 B4 (ADR-0028 Leg 1, accumulating-string scan sibling) — walker v82.
##
## `tryRecognizeScanIdiom`/`tryMatchScanIdiomShape` (Q1/B0) recognize the
## skip-while-and-clamp scan idiom; `tryRecognizeScanPairIdiom` (B3)
## recognizes the early-return-on-match scan. Chapulin's `readCString`
## family is a THIRD shape — B3's early-return scan with one more body
## statement that ACCUMULATES the pre-terminator bytes into a string as the
## loop advances:
##
##   proc readCString(data: seq[byte], offset: int): (string, int) =
##     var s = ""
##     var i = offset
##     while i < data.len:
##       if data[i] == 0:
##         return (s, i + 1)
##       s.add char(data[i])
##       i.inc
##     raise newException(TftpDecodeError, "Unterminated string...")
##
## Pre-B4, this shape was UNRECOGNIZED: it k-unrolled and, once `s.len`
## grew unconstrained, exhausted `maxLoopUnwind` and degraded to
## `sxUnknown` — pinned empirically as the "B3-5" trip-wire in
## `tests/tsymex_r6_b3_scanpair.nim` BEFORE this slice landed (that pin is
## migrated alongside this file once B4 lands, since B4's own recognizer
## now claims the exact 3-statement shape B3-5 exercised).
##
## `tryRecognizeAccumulatingScan` (`dsl_parser.nim`) closes this gap: same
## `iekStrFind` 3-arg closed form and B0 not-found/OOB split as Q1/B3, plus
## one new binding — `<acc> = <acc's entry value> & iekStrSubstr(<s>, <i>,
## p - 1)`, the RFC's pinned inclusive-hi formula
## (`iekStrSubstr(s, offset, terminatorIx - 1)`).
##
## This file also pins two supporting fixes B4 needed to make the closed
## form actually PROVE (not just parse):
##   1. `collectIntOffsetParams` (`dsl_parser.nim`, ADR-0027's recorded
##      lift): `iekStrSubstr`'s LOW bound must be Int-sorted (its own
##      runtime arm declines a BV-represented bound — the CR-17
##      non-termination class); `<i>`'s ROOT formal param now allocates
##      `svInt` when its def-use reaches an accumulating-scan's index,
##      through at most one direct `var <i> = <param>` rebind. Unlike B1a's
##      `seq[byte]`-allocation classifier (a property of one proc's own
##      body), `readCString`-shaped helpers are naturally called through a
##      WRAPPER (chapulin's own `readOptions`: `let (k, p) = readCString(
##      data, pos)`), so the collector traces ONE call boundary outward too
##      — a wrapper's argument feeding a callee's own traced offset param
##      gets marked in the wrapper's scope as well (cycle-guarded, bounded
##      to direct calls).
##   2. `readSeqUInt8`'s string-backed-param witness-reader fix
##      (`runtime.nim`, B1's flagged gap): a `seq[byte]` param B1 marks
##      `isStringBacked` allocates as `svString`, so its solved value lands
##      in `RawWitness.strVals`, but the generated reader glue (picked off
##      the DECLARED `seq[byte]` type) calls `readSeqUInt8`, which
##      previously only read `seqLens`/`uintVals` — silently degrading to
##      an empty seq regardless of the solved model. `readSeqUInt8` now
##      checks `strVals` first.
##
## **Delimiter choice, and a discovered pre-existing engine bug (flagged at
## B4 landing time, FIXED by the Round-6 B4-rider —
## `tests/tsymex_r6_nulwitness.nim`, `runtime.nim`'s `evalStrBytes`):** the
## closed form itself is delimiter-VALUE-agnostic (any `nnkCharLit` works).
## Most pins below still use `':'`, matching B3's own precedent, rather than
## the real `'\0'` chapulin uses — kept as-is post-fix since they predate
## the rider and the ':' shape is still worth pinning independently. At B4
## landing time, isolated minimal repros (a bare `s[2] == '\0'`, and
## separately `s.find('\0')` — NEITHER touching this slice's new code)
## proved that witness EXTRACTION for any solved string whose model
## required an embedded NUL byte came back corrupted — the byte was
## replaced with the 5-character LITERAL TEXT of its own SMT-LIB escape
## spelling (`\u{0}`), inflating the length and breaking any byte-for-byte
## replay (traced to nim-z3's `evalStr`/`Z3_get_lstring`, NUL-specific —
## other escape-needing bytes tested clean; see the rider file's doc for
## the full empirical breakdown). B4-8 below now asserts CONTENT, not just
## status, and B4-8-cross replays the witness through the real function.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

proc readCStringTracer(s: string, offset: int): (string, int) =
  ## The canonical B4 shape, `string`-receiver spelling (Q1/B1/B3's own
  ## scope note: the scan-lift family is not widened to `seq[byte]`
  ## receivers). Delimiter is `':'`, not chapulin's real `'\0'` — see the
  ## file doc's flagged pre-existing witness-extraction bug. Called through
  ## a WRAPPER by every `symexFind` target below (chapulin's own real call
  ## shape — `readOptions` calls `readCString` the same way) and ALSO used
  ## directly, post-`symexFind`, to replay a witness through "the real Nim
  ## function" for the cross-check pins.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == ':':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

# ---------------------------------------------------------------------------
# 1. Symbolic-start lift SAT + witness cross-check.
# ---------------------------------------------------------------------------

proc sutAccPayloadAB(s: string, start: int) =
  let (payload, q) = readCStringTracer(s, start)
  if payload == "AB" and q == start + 3:
    symexTarget("payload_ab")

suite "symex round-6 B4 -- symbolic-start lift":

  test "B4-1: payload == \"AB\" reachable from a symbolic start -> sxSat":
    let r = symexFind(sutAccPayloadAB, tLabel("payload_ab"))
    check r.status == sxSat

  test "B4-1-cross: the witness, replayed through the real function, reproduces the exact found outcome":
    let r = symexFind(sutAccPayloadAB, tLabel("payload_ab"))
    check r.status == sxSat
    let (s, start) = r.witness
    check start >= 0 and start <= s.len
    let (payload, q) = readCStringTracer(s, start)
    check payload == "AB"
    check q == start + 3

# ---------------------------------------------------------------------------
# 2. Dedicated inclusive-hi pin (B4's Done-when): the payload excludes the
#    terminator and includes the last pre-terminator character, in both
#    directions -- a concrete empty-payload witness AND a universal
#    length-relation proof.
# ---------------------------------------------------------------------------

proc sutAccImmediateTerminatorEmptyPayload(s: string, start: int) =
  let (payload, q) = readCStringTracer(s, start)
  if payload.len == 0 and q == start + 1:
    symexTarget("empty_payload")

proc sutAccNotFoundClampImpossible(s: string, start: int) =
  ## UNSAT companion (mirrors B0/B3's own "not-found clamp never exceeds
  ## bound" pin style exactly — direct top-level loop, no wrapper call):
  ## B0's zero-iteration/clamp discipline carries over to the accumulating
  ## shape unchanged — a not-found scan (from a SYMBOLIC start) clamps `i`
  ## to `bound` (`s.len`) and never exceeds it. Deliberately does NOT cross
  ## a function-call boundary (B3-1b's own recorded finding: an
  ## inlined-callee UNIVERSAL/UNSAT relational proof of the FOUND branch's
  ## return-value shape diverges in this engine build regardless of B4 — a
  ## PRE-EXISTING general limitation, confirmed independently while landing
  ## this pin, out of scope to fix here; routed around per dt-bounded
  ## doctrine exactly as B3-1b documents). `start` is constrained to
  ## `[0, s.len]` — without it the property is vacuously reachable via
  ## B0's zero-iteration discipline (an unconstrained `start` past `s.len`
  ## leaves `i` untouched by a loop that never runs).
  symexAssume(start >= 0 and start <= s.len)
  var acc = ""
  var i = start
  while i < s.len:
    if s[i] == ':':
      return
    acc.add s[i]
    i.inc
  if i > s.len:
    symexTarget("impossible")

suite "symex round-6 B4 -- inclusive-hi pin":

  test "B4-2: immediate terminator -> empty payload, next offset = start+1 (sxSat)":
    ## `p == start` at loop entry: `iekStrSubstr`'s hi bound is `p - 1 <
    ## start` (the low bound) -- `(hi - lo) + 1 <= 0` -- so Z3's
    ## `seq.extract` reports the empty string. Proves the empty-payload case
    ## is expressible without a special case. Combined with B4-1's non-empty
    ## `payload == "AB"` / `q == start + 3` pin, this concretely validates
    ## the off-by-one arithmetic (`payload.len == q - start - 1`) at both
    ## the empty and non-empty boundary.
    let r = symexFind(sutAccImmediateTerminatorEmptyPayload, tLabel("empty_payload"))
    check r.status == sxSat

  test "B4-2-cross: the empty-payload witness, replayed through the real function, reproduces it":
    let r = symexFind(sutAccImmediateTerminatorEmptyPayload, tLabel("empty_payload"))
    check r.status == sxSat
    let (s, start) = r.witness
    let (payload, q) = readCStringTracer(s, start)
    check payload.len == 0
    check q == start + 1

  test "B4-3 UNSAT companion: not-found clamp never exceeds bound, for the accumulating shape":
    let r = symexFind(sutAccNotFoundClampImpossible, tLabel("impossible"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# 3. Not-found fork pin (per B0's split, reused verbatim).
# ---------------------------------------------------------------------------

proc sutAccDiscard(s: string, start: int) =
  discard readCStringTracer(s, start)

suite "symex round-6 B4 -- not-found fork":

  test "B4-4: no terminator present -> the modeled ScanError raise is reachable (sxRaised)":
    let r = symexFind(sutAccDiscard, tRaisedExn("ScanError"))
    check r.status == sxRaised

# ---------------------------------------------------------------------------
# 4. OOB / entry-guard pin (per B0's split -- negative symbolic start).
# ---------------------------------------------------------------------------

suite "symex round-6 B4 -- OOB entry guard":

  test "B4-5: negative symbolic start -> the entry-read probe deposits a real IndexDefect (sxRaised)":
    let r = symexFind(sutAccDiscard, tIndexError())
    check r.status == sxRaised

# ---------------------------------------------------------------------------
# 5. Trip-wire -- a shape OUTSIDE the recognizer (non-`.len` bound) still
#    k-unrolls, proving the recognizer stays narrow (mirrors B0/B3's own
#    "local alias bound" decline).
# ---------------------------------------------------------------------------

proc sutAccNonLenBoundImpossible(s: string) =
  let n = s.len
  var acc = ""
  var i = 0
  while i < n:
    if s[i] == ':':
      return
    acc.add s[i]
    i.inc
  if i > s.len:
    symexTarget("impossible")

suite "symex round-6 B4 -- trip wire (recognizer stays narrow)":

  test "B4-6: non-.len bound is NOT recognized -> sxUnknown (unchanged, real trip-wire)":
    let r = symexFind(sutAccNonLenBoundImpossible, tLabel("impossible"))
    check r.status == sxUnknown

# ---------------------------------------------------------------------------
# 6. The REAL chapulin delimiter, '\0'. Proves the recognizer genuinely
#    accepts chapulin's own delimiter, not just the test suite's substitute
#    ':'. STRENGTHENED (Round-6 B4-rider, `tests/tsymex_r6_nulwitness.nim`):
#    content extraction for a NUL-embedding string model was broken
#    pre-existing (flagged here, fixed by the rider) -- `extractLeaf`'s
#    `svString` arm now reads raw bytes via `evalStrBytes`
#    (`getStringContents`) instead of nim-z3's `evalStr`
#    (`Z3_get_lstring`-backed, which mis-rendered the embedded NUL as the
#    5-char literal text of its own escape spelling). B4-8 below now
#    asserts content, not just status.
# ---------------------------------------------------------------------------

proc readCStringNulTracer(s: string, offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc sutAccNulPayloadAB(s: string, start: int) =
  let (payload, q) = readCStringNulTracer(s, start)
  if payload == "AB" and q == start + 3:
    symexTarget("payload_ab_nul")

suite "symex round-6 B4 -- real chapulin delimiter ('\\0')":

  test "B4-8: the SAME closed form recognizes and proves the real '\\0' delimiter -> sxSat":
    let r = symexFind(sutAccNulPayloadAB, tLabel("payload_ab_nul"))
    check r.status == sxSat

  test "B4-8-content: the witness's real NUL terminator extracts as 1 raw byte, not 5-char escape text (Round-6 B4-rider)":
    let r = symexFind(sutAccNulPayloadAB, tLabel("payload_ab_nul"))
    check r.status == sxSat
    let (s, start) = r.witness
    check start >= 0 and start <= s.len
    check s.len == start + 3
    check s[start] == 'A'
    check s[start + 1] == 'B'
    check ord(s[start + 2]) == 0

  test "B4-8-cross: the witness, replayed through the real function, reproduces the exact found outcome (Round-6 B4-rider)":
    let r = symexFind(sutAccNulPayloadAB, tLabel("payload_ab_nul"))
    check r.status == sxSat
    let (s, start) = r.witness
    let (payload, q) = readCStringNulTracer(s, start)
    check payload == "AB"
    check q == start + 3

# ---------------------------------------------------------------------------
# 7. Witness-reader fix (B1's flagged gap): a string-backed `seq[byte]`
#    param's witness now renders real byte content instead of degrading to
#    an empty seq. Independent of B4's own recognizer (itString-only, per
#    Q1/B1/B3's scope note) -- exercised here via Q1's UNMODIFIED
#    `tryMatchScanIdiomShape`-based classifier (`collectStringBackedByteSeqParams`),
#    which marks a `seq[byte]` receiver string-backed for ALLOCATION
#    purposes independent of whether the scan LOOP itself gets
#    closed-form-lifted (it does not, for a `seq[byte]` receiver -- Q1's own
#    `itString`-only type gate declines it, so this loop k-unrolls, using
#    B1's `svString` totality backstops for `data[i]`/`data.len`). Forces
#    `data.len == 2` (the bound-exhaustion clamp, not a genuine byte match)
#    so this pin needs no delimiter byte value at all, staying clear of the
#    flagged NUL-extraction bug above.
# ---------------------------------------------------------------------------

proc byteFindTracer(data: seq[byte]): int =
  var i = 0
  while i < data.len and data[i] != 0:
    inc i
  i

proc sutByteWitness(data: seq[byte]) =
  let p = byteFindTracer(data)
  if p == 2 and data.len == 2:
    symexTarget("found_at_2")

suite "symex round-6 B4 -- string-backed witness reader fix":

  test "B4-9: string-backed seq[byte] param's witness renders real byte content, not an empty seq":
    let r = symexFind(sutByteWitness, tLabel("found_at_2"))
    check r.status == sxSat
    let data = r.witness[0]
    check data.len == 2
    check byteFindTracer(data) == 2

suite "symex round-6 B4 -- walker version pin":

  test "walker version floor >= 82 (accumulating-string scan-lift closed form)":
    check parseInt(symexWalkerVersion) >= 82
