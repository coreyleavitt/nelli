## Round-6 B4-rider — embedded-NUL witness EXTRACTION fix, flagged as a
## pre-existing bug (unfixed, not B4's own scope) in
## `tests/tsymex_r6_b4_readcstring.nim`'s file doc and the
## RFC-chapulin-hardening handoff's B4 bullet.
##
## Root cause (isolated with a `_deps`-only repro, no nelli code involved —
## a bare `mkString("\x00")` round-tripped through nim-z3's `evalStr`
## alone): `Z3_get_lstring` — the C API `evalStr`/`toStr` wrap — mis-renders
## a string containing an embedded NUL byte. For a 1-byte NUL string it
## returns 5 bytes: the LITERAL TEXT of that byte's SMT-LIB escape spelling,
## `\u{0}`, with the reported length inflated to match (so the corruption is
## not detectable from length alone). This reproduces with `Z3_get_lstring`
## called directly — no nelli, no nim-z3 binding bug, no solver model
## involved; a bare literal AST is enough.
##
## The bug is NUL-SPECIFIC, not a general "any escape-needing byte" defect —
## the original hand-off flag raised backslash/quote/control-bytes/0x7f+ as
## an open question, and this file settles it empirically: standalone
## (NUL-free) witnesses containing backslash, `"`, a <0x20 control byte,
## 0x7f, and 0xff all extract correctly even through the UNFIXED `evalStr`
## path (NW-3/NW-4/NW-4b/NW-4c/NW-4d below, which pass unchanged before and
## after the fix). Those bytes only come back wrong when they happen to
## SHARE a witness string with a real embedded NUL (NW-5 below) — because
## the NUL's own 5-character expansion shifts every later byte's offset,
## not because those bytes are individually mis-rendered. Plain printable
## ASCII is unaffected either way.
##
## Fix: `runtime.nim`'s `extractLeaf` (`svString` arm) now calls a new
## `evalStrBytes` helper instead of nim-z3's `evalStr`. `evalStrBytes` is
## built on `getStringLength`/`getStringContents`
## (`Z3_get_string_length`/`Z3_get_string_contents`) — a SEPARATE
## already-bound Z3 API (`z3/strings`, re-exported through the umbrella
## `import z3` nelli already uses) that returns raw Unicode codepoints, not
## a rendered string. The same isolated repro confirmed it round-trips
## every tested byte value correctly, both on a bare literal AST and on a
## solver-model evaluation. nelli's own byte-faithful string invariant
## (Phase 15 S3 / ADR-0006: every free `string` is constrained to `(re.range
## '\x00' '\xff')*` at allocation, `runtime.nim`'s `itString` arm) guarantees
## every codepoint `evalStrBytes` sees is in `[0, 255]`, so the codepoint ->
## Nim-byte mapping is exact and total for every string nelli ever models.
##
## Verdicts (sxSat/sxUnsat/sxUnknown/sxRaised) are UNCHANGED by this fix —
## only already-SAT witness CONTENT differs for strings containing an
## affected byte — so `symexWalkerVersion` does NOT bump.
## `renderAsChoicesVersion` bumps "8" -> "9" (genuinely new witness content
## reaching `renderAsChoices`, per "8"'s own B4 precedent).
##
## All SUTs below use only PRE-EXISTING `iekStrAt`/`iekStrFind` machinery —
## no new recognizer, no new IR kind. The fix is purely at the extraction
## chokepoint.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# 1. The headline repro: a solved string with an embedded NUL at a known
#    position, forced via three plain `iekStrAt` reads (`s[0]`, `s[1]`,
#    `s[2]`) plus `s.len`. Pre-fix: `r.witness[0]` came back as
#    "A\u{0}B" (5-char literal escape text in place of the 1 real NUL byte,
#    total length 6 instead of 3). Post-fix: exact byte-for-byte content.
# ---------------------------------------------------------------------------

proc sutEmbeddedNulAtIndex1(s: string) =
  if s.len == 3 and s[0] == 'A' and s[1] == '\0' and s[2] == 'B':
    symexTarget("hit")

suite "symex round-6 B4-rider -- embedded NUL at a known position":

  test "NW-1: s.len==3, s[1]=='\\0' is reachable (sxSat)":
    let r = symexFind(sutEmbeddedNulAtIndex1, tLabel("hit"))
    check r.status == sxSat

  test "NW-1-content: the witness is the exact 3 raw bytes, not the 5-char escape text":
    let r = symexFind(sutEmbeddedNulAtIndex1, tLabel("hit"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.len == 3
    check s == "A\x00B"
    check ord(s[0]) == ord('A')
    check ord(s[1]) == 0
    check ord(s[2]) == ord('B')

# ---------------------------------------------------------------------------
# 2. The NUL-delimited B4-shape scan witness -- the exact accumulating-scan
#    class `tests/tsymex_r6_b4_readcstring.nim` worked around with ':'
#    (its file doc's flagged bug) because content assertions on the real
#    '\0' delimiter were broken by this same extraction bug. Content is now
#    asserted directly, both on the raw witness string and by replaying the
#    witness through the real Nim function (same cross-check style B4 uses
#    elsewhere in that file).
# ---------------------------------------------------------------------------

type ScanError = object of CatchableError

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

suite "symex round-6 B4-rider -- NUL-delimited B4-shape scan, content strengthened":

  test "NW-2: real '\\0' delimiter, payload==\"AB\" is reachable (sxSat)":
    let r = symexFind(sutAccNulPayloadAB, tLabel("payload_ab_nul"))
    check r.status == sxSat

  test "NW-2-content: the witness's terminator byte is a real single NUL, not the 5-char escape text":
    let r = symexFind(sutAccNulPayloadAB, tLabel("payload_ab_nul"))
    check r.status == sxSat
    let (s, start) = r.witness
    check start >= 0 and start <= s.len
    check s.len == start + 3
    check s[start] == 'A'
    check s[start + 1] == 'B'
    check ord(s[start + 2]) == 0

  test "NW-2-cross: the witness, replayed through the real function, reproduces the exact found outcome":
    let r = symexFind(sutAccNulPayloadAB, tLabel("payload_ab_nul"))
    check r.status == sxSat
    let (s, start) = r.witness
    let (payload, q) = readCStringNulTracer(s, start)
    check payload == "AB"
    check q == start + 3

# ---------------------------------------------------------------------------
# 3. A low byte (< 0x20, chosen 0x01, distinct from NUL) round-trips.
# ---------------------------------------------------------------------------

proc sutLowByte(s: string) =
  if s.len == 1 and s[0] == '\x01':
    symexTarget("hit")

suite "symex round-6 B4-rider -- low byte (0x01)":

  test "NW-3: a solved single-byte string 0x01 round-trips exactly":
    let r = symexFind(sutLowByte, tLabel("hit"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.len == 1
    check ord(s[0]) == 1

# ---------------------------------------------------------------------------
# 4. A literal backslash round-trips (SMT-LIB's own escape-introducer byte).
# ---------------------------------------------------------------------------

proc sutBackslash(s: string) =
  if s.len == 1 and s[0] == '\\':
    symexTarget("hit")

suite "symex round-6 B4-rider -- backslash byte":

  test "NW-4: a solved single-byte backslash string round-trips exactly":
    let r = symexFind(sutBackslash, tLabel("hit"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.len == 1
    check ord(s[0]) == ord('\\')

# ---------------------------------------------------------------------------
# 4b. Standalone (NUL-free) single-byte pins for double-quote, 0x7f, and
#     0xff -- probing whether the corruption is genuinely NUL-specific or a
#     broader "any byte needing SMT-LIB escaping" class. Empirically these
#     round-trip fine even pre-fix (see NW-5 below for a case where the same
#     bytes DO come back wrong when they SHARE a witness with a real NUL --
#     but only because the NUL's own 5-char expansion shifts every later
#     byte's offset, not because these bytes are individually mis-rendered).
# ---------------------------------------------------------------------------

proc sutQuote(s: string) =
  if s.len == 1 and s[0] == '"':
    symexTarget("hit")

proc sut7f(s: string) =
  if s.len == 1 and s[0] == '\x7f':
    symexTarget("hit")

proc sutFF(s: string) =
  if s.len == 1 and s[0] == '\xff':
    symexTarget("hit")

suite "symex round-6 B4-rider -- standalone quote / 0x7f / 0xff":

  test "NW-4b: a solved single-byte double-quote string round-trips exactly":
    let r = symexFind(sutQuote, tLabel("hit"))
    check r.status == sxSat
    check ord(r.witness[0][0]) == ord('"')

  test "NW-4c: a solved single-byte 0x7f string round-trips exactly":
    let r = symexFind(sut7f, tLabel("hit"))
    check r.status == sxSat
    check ord(r.witness[0][0]) == 0x7f

  test "NW-4d: a solved single-byte 0xff string round-trips exactly":
    let r = symexFind(sutFF, tLabel("hit"))
    check r.status == sxSat
    check ord(r.witness[0][0]) == 0xff

# ---------------------------------------------------------------------------
# 5. A mixed string covering NUL alongside every OTHER flagged byte class
#    (a <0x20 control byte, double-quote, backslash, 0x7f, 0xff) in one
#    witness, bracketed by plain ASCII. Pre-fix, only the NUL byte is
#    individually mis-rendered (5-char escape text) -- but that expansion
#    SHIFTS every later byte's offset, so every downstream `check` in this
#    test fails too even though those bytes round-trip fine standalone
#    (section 4b). This is the case B4's own `readCString`/`readOptions`
#    shape hits in practice: a real chapulin string with a NUL delimiter
#    followed by more content.
# ---------------------------------------------------------------------------

proc sutMixedEscapeBytes(s: string) =
  if s.len == 9 and s[0] == 'A' and s[1] == '\x00' and s[2] == '\x01' and
     s[3] == '\x1f' and s[4] == '"' and s[5] == '\\' and s[6] == '\x7f' and
     s[7] == '\xff' and s[8] == 'B':
    symexTarget("hit")

suite "symex round-6 B4-rider -- mixed escaped-byte class in one witness":

  test "NW-5: every flagged byte class round-trips in a single witness":
    let r = symexFind(sutMixedEscapeBytes, tLabel("hit"))
    check r.status == sxSat
    let s = r.witness[0]
    check s.len == 9
    check ord(s[0]) == ord('A')
    check ord(s[1]) == 0x00
    check ord(s[2]) == 0x01
    check ord(s[3]) == 0x1f
    check ord(s[4]) == ord('"')
    check ord(s[5]) == ord('\\')
    check ord(s[6]) == 0x7f
    check ord(s[7]) == 0xff
    check ord(s[8]) == ord('B')

# ---------------------------------------------------------------------------
# 6. Regression pin: an unaffected plain-ASCII witness is untouched by the
#    extraction-path change (guards against overcorrection in `evalStrBytes`).
# ---------------------------------------------------------------------------

proc sutPlainAscii(s: string) =
  if s == "hello":
    symexTarget("hit")

suite "symex round-6 B4-rider -- plain-ASCII regression":

  test "NW-6: an unaffected plain-ASCII witness still round-trips exactly":
    let r = symexFind(sutPlainAscii, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == "hello"

# ---------------------------------------------------------------------------
# 7. Version pins.
# ---------------------------------------------------------------------------

suite "symex round-6 B4-rider -- version pins":

  test "walker version floor >= 84 (no verdict change from this rider)":
    check parseInt(symexWalkerVersion) >= 84

  test "renderAsChoicesVersion is now 9 (new witness CONTENT for affected strings)":
    check renderAsChoicesVersion == "9"
