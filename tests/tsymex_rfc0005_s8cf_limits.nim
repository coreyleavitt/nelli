## RFC-0005 S8cf (items 1, 2; SOUNDNESS) -- a call can stop at PCRE's own
## limits: the default MATCH_LIMIT (-8), the JIT's 32 KiB stack (-27). Before
## S8cf the walker read every call as a match or a miss, so it refuted what
## the real run reaches. Each pin checks native std/re first, so the expected
## outcome is the library's, not the model's.
import std/[unittest, re, strutils]
import pcre
import nelli/symex
import nelli/smt/canonicalize

const
  a30 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  a10 = "aaaaaaaaaa"
  a2000 = static('a'.repeat(2000))

proc matchHit(s: string) =
  if s == a30 and s.match(re"(a|a)*[bc]"):
    symexTarget("cf_match_hit")

proc findCode(s: string) =
  if s == a30 and s.find(re"(a|a)*[bc]") == -8:
    symexTarget("cf_find_code")

proc matchLenCode(s: string) =
  if s == a30 and s.matchLen(re"(a|a)*[bc]") < -1:
    symexTarget("cf_matchlen_code")

proc boundsCode(s: string) =
  if s == a30 and s.findBounds(re"(a|a)*[bc]").first < -1:
    symexTarget("cf_bounds_code")

proc missOnLong(s: string) =
  if s == a30 and not s.match(re"(a|a)*[bc]"):
    symexTarget("cf_miss_long")

proc replaceStops(s: string) =
  if s == a30 and s.replace(re"(a|a)*[bc]|a", "x") == s:
    symexTarget("cf_replace_stops")

proc shortMatch(s: string) =
  if s == a10 and s.match(re"(a|a)*[bc]"):
    symexTarget("cf_short_match")

proc shortMiss(s: string) =
  if s == a10 and not s.match(re"(a|a)*[bc]"):
    symexTarget("cf_short_miss")

proc hitImpliesByte(s: string) =
  # A stopped call reads false here too, so this holds at every length.
  if s.contains(re"(a|b)*c") and not s.contains(re"c"):
    symexTarget("cf_hit_needs_c")

proc missImpliesNoByte(s: string) =
  # Past the stack a subject holding `c` can read false (-27 on the JIT).
  if not s.contains(re"(a|b)*c") and s.len > 0 and s[^1] == 'c':
    symexTarget("cf_miss_no_c")

proc jitStack(s: string) =
  if s == a2000 and s.find(re"(a|b)*c") == -27:
    symexTarget("cf_jit_stack")

proc jitBuild(): bool =
  var v: cint
  discard pcre.config(pcre.CONFIG_JIT, addr v)
  v == 1

suite "S8cf: PCRE's own limits":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 242

  test "native: what the calls surface":
    let r = re"(a|a)*[bc]"
    check a30.match(r)
    check a30.matchLen(r) == -8
    check a30.find(r) == -8
    check a30.findBounds(r).first == -8
    check not a30.contains(r)
    check a30.replace(re"(a|a)*[bc]|a", "x") == a30
    check not a10.match(r)
    check a10.find(r) == -1
    if jitBuild():
      check a2000.find(re"(a|b)*c") == -27

  test "a call past MATCH_LIMIT is not refuted":
    check symexFind(matchHit, tLabel("cf_match_hit")).status != sxUnsat
    check symexFind(findCode, tLabel("cf_find_code")).status != sxUnsat
    check symexFind(matchLenCode, tLabel("cf_matchlen_code")).status != sxUnsat
    check symexFind(boundsCode, tLabel("cf_bounds_code")).status != sxUnsat
    check symexFind(replaceStops, tLabel("cf_replace_stops")).status != sxUnsat

  test "a miss past MATCH_LIMIT is not a witness":
    check symexFind(missOnLong, tLabel("cf_miss_long")).status != sxSat

  test "within the safe length both outcomes stand":
    check symexFind(shortMatch, tLabel("cf_short_match")).status == sxUnsat
    check symexFind(shortMiss, tLabel("cf_short_miss")).status == sxSat

  test "a stopped call reads false: the refutation stands":
    check symexFind(hitImpliesByte, tLabel("cf_hit_needs_c")).status == sxUnsat

  test "a miss over an unbounded subject is not refuted":
    let r = symexFind(missImpliesNoByte, tLabel("cf_miss_no_c"))
    check r.status != sxUnsat

  test "the JIT's stack limit is not refuted":
    check symexFind(jitStack, tLabel("cf_jit_stack")).status != sxUnsat
