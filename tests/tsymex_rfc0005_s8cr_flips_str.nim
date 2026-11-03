## RFC-0005 S8cr (DoD §6 item 3): the regex and pair-loop half of
## `tsymex_rfc0005_s8cr_flips.nim`, split at that boundary to keep each file under
## 60 s on Windows.
##
## The second half of this file covers §4.3's own named candidates. The n21 pins
## flipped and are justified here. The SND-3 family did NOT flip: its pins still
## read `sxUnknown`, so there is no `sxUnsat` for the helper to justify, and the
## suite at the end asserts why.
import std/[unittest, strutils, re]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    result.add $e.kind & "/" & $e.severity & " "

template justify(sut: untyped; tgt: untyped) =
  let r = symexFind(sut, tgt)
  checkpoint $r.status & " " & show(r.errors)
  checkUnsatOverTaintOnly(r)

# ---- regex --------------------------------------------------------------------

proc flAlternationOrder(s: string) =
  if s == "ab" and s.replace(re"a|ab", "x") == "x":
    symexTarget("aw_alternation")

proc flStar(s: string) =
  if s == "b" and s.replace(re"a*", "x") == "b":
    symexTarget("aw_star")

proc flSpace(s: string) =
  if s == "a b" and s.replace(re"a b", "x") == "a b":
    symexTarget("aw_space")

proc flReversedRange(s: string) =
  if s.replace(re"[z-a]", "x") == "q":
    symexTarget("aw_reversed")

proc flEndsWithAlt(s: string) =
  if s == "ab" and s.endsWith(re"a|ab"):
    symexTarget("ay_ends_alt")

proc flReplaceRe(s: string) =
  if s == "foofoo" and s.replace(re"f+", "x") == "xoxo":
    symexTarget("hit")

proc flFoundExceedsLast(s, t: string) =
  if t in s and s.find(t, 0) >= 0 and s.rfind(t) < s.find(t, 0):
    symexTarget("s8aq_found_exceeds_last")

suite "flips to sxUnsat: regex and search":
  # flip: c5c2d35a tsymex_rfc0005_s8aw_remainder
  test "S8bb: PCRE's alternation priority and NOTEMPTY_ATSTART are modelled":
    justify(flAlternationOrder, tLabel("aw_alternation"))
    justify(flStar, tLabel("aw_star"))
  # flip: b81bafdb tsymex_rfc0005_s8aw_remainder
  test "S8ay: re vs rex is in the IR, and a reversed range raises":
    justify(flSpace, tLabel("aw_space"))
    justify(flReversedRange, tLabel("aw_reversed"))
  # flip: 37f94ec2 tsymex_rfc0005_s8ay_remainder
  test "S8bb: endsWith whose answer is PCRE's match order":
    justify(flEndsWithAlt, tLabel("ay_ends_alt"))
  # flip: 04e3a97e tsymex_phase15_S6b_regex
  test "S8aw: regex replace is lowered in the walker (was seZ3VersionMissing)":
    justify(flReplaceRe, tLabel("hit"))
  # flip: 4a8e51f4 tsymex_rfc0005_s8aq_remainder
  # flip: 9da3af61 tsymex_rfc0005_s8aq_remainder
  test "S8au/S8aw: a found index never exceeds the last one (was beSolverUndef)":
    justify(flFoundExceedsLast, tLabel("s8aq_found_exceeds_last"))

# ---- the pair loop ------------------------------------------------------------

type ScanError = object of CatchableError

proc flReadCString(s: string, offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc flReadOptions(s: string, start: int) =
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = flReadCString(s, i)
    if key.len == 0:
      break
    let (val, p2) = flReadCString(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("done")

proc flReadOptionsCounter(s: string, start: int) =
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = flReadCString(s, i)
    if key.len == 0:
      break
    let (val, p2) = flReadCString(s, p1)
    pairs.add((key, val))
    i = p2
  if i == 6:
    symexTarget("correct")
  else:
    symexTarget("stale")

proc flN21Odd(s: string) =
  symexAssume(s == "aa\x00bb\x00cc\x00")
  flReadOptions(s, 0)

proc flN21Even(s: string) =
  symexAssume(s == "aa\x00bb\x00")
  flReadOptions(s, 0)

proc flN21Terminated(s: string) =
  symexAssume(s == "aa\x00bb\x00\x00")
  flReadOptions(s, 0)

proc flR5Literal(s: string) =
  symexAssume(s == "aa\x00bb\x00\x00")
  flReadOptionsCounter(s, 0)

proc flN10Empty(s: string, start: int) =
  symexAssume(s.len == 0 and start == 0)
  var pairs: seq[(string, string)] = @[]
  var i = start
  while i < s.len:
    let (key, p1) = flReadCString(s, i)
    if key.len == 0:
      break
    let (val, p2) = flReadCString(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("b6_empty_done")

suite "flips to sxUnsat: §4.3's n21 honest-decline pins and the pair-loop family":
  # flip: 70fb94cd tsymex_r6_n21_pairloop_member
  test "S8k N21-1: the odd literal never reaches \"done\"":
    justify(flN21Odd, tLabel("done"))
  test "S8k N21-2: the even literal never raises ScanError":
    justify(flN21Even, tRaisedExn("ScanError"))
  test "S8k N21-3: the terminated literal never raises ScanError":
    justify(flN21Terminated, tRaisedExn("ScanError"))
  # flip: 70fb94cd tsymex_r6_r5_pairloop_counter
  test "S8k R5: the counter is advanced, so \"stale\" is dead":
    justify(flR5Literal, tLabel("stale"))
  # flip: 1ea2c703 tsymex_r6_n10_coverage_matrix
  test "S8k N10d: an empty receiver never raises ScanError":
    justify(flN10Empty, tRaisedExn("ScanError"))

# ---- §4.3's SND-3 candidates: no flip -----------------------------------------

proc flDigitScanLoop(s: string) =
  if s.len == 0:
    return
  var i = 0
  while i < s.len and s[i] >= '0' and s[i] <= '9':
    inc i
  symexTarget("after_loop")

proc flOnlyViaDegraded(s: string) =
  var i = 0
  while i < s.len:
    if s[i] >= '0':
      symexTarget("only_via_degrade")
    inc i

proc flOutsideLoop(s: string) =
  if s.len > 0 and s[0] >= '0':
    symexTarget("outside_loop_degrade")

suite "§4.3's SND-3 family stays sxUnknown, so the helper has nothing to justify":
  ## The labels are reachable in Nim, so `sxUnsat` would be false and the helper
  ## must keep refusing these runs. The checks read that refusal directly.
  template stays(sut: untyped; label: string) =
    let r = symexFind(sut, tLabel(label))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    expect AssertionDefect:
      checkUnsatOverTaintOnly(r)

  test "SND-3-1: the digit scan loop":
    stays(flDigitScanLoop, "after_loop")
  test "SND-3-2: a target reachable only through the compare":
    stays(flOnlyViaDegraded, "only_via_degrade")
  test "SND-3-4: the compare outside a loop":
    stays(flOutsideLoop, "outside_loop_degrade")
  test "oracle: Nim reaches each label":
    symexCaptureBegin()
    flDigitScanLoop("12")
    flOnlyViaDegraded("5")
    flOutsideLoop("5")
    let got = symexCaptureEnd()
    check "after_loop" in got
    check "only_via_degrade" in got
    check "outside_loop_degrade" in got

suite "RFC-0005 S8cr (flips_str): walker version":
  test "symexWalkerVersion >= 245 (no walker change: this slice adds pins)":
    check parseInt(symexWalkerVersion) >= 245
