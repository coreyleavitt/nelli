## S8cf items 1, 2 (PCRE limits; open at e497dcf) from tsymex_rfc0005_s8cf_limits.
import std/re
import h

const
  a30 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  a10 = "aaaaaaaaaa"
  a2000 = static('a'.repeat(2000))

proc matchHit(s: string) =
  if s == a30 and s.match(re"(a|a)*[bc]"): symexTarget("cf_match_hit")
proc findCode(s: string) =
  if s == a30 and s.find(re"(a|a)*[bc]") == -8: symexTarget("cf_find_code")
proc matchLenCode(s: string) =
  if s == a30 and s.matchLen(re"(a|a)*[bc]") < -1: symexTarget("cf_matchlen_code")
proc boundsCode(s: string) =
  if s == a30 and s.findBounds(re"(a|a)*[bc]").first < -1: symexTarget("cf_bounds_code")
proc missOnLong(s: string) =
  if s == a30 and not s.match(re"(a|a)*[bc]"): symexTarget("cf_miss_long")
proc replaceStops(s: string) =
  if s == a30 and s.replace(re"(a|a)*[bc]|a", "x") == s: symexTarget("cf_replace_stops")
proc shortMatch(s: string) =
  if s == a10 and s.match(re"(a|a)*[bc]"): symexTarget("cf_short_match")
proc shortMiss(s: string) =
  if s == a10 and not s.match(re"(a|a)*[bc]"): symexTarget("cf_short_miss")
proc missImpliesNoByte(s: string) =
  if not s.contains(re"(a|b)*c") and s.len > 0 and s[^1] == 'c': symexTarget("cf_miss_no_c")
proc jitStack(s: string) =
  if s == a2000 and s.find(re"(a|b)*c") == -27: symexTarget("cf_jit_stack")
proc altPlus(s: string) =
  if s.len > 0 and s[0] == 'a' and not s.contains(re"(a|b)+c") and s[^1] == 'c' and s.len == 40:
    symexTarget("alt_plus")

echo "N|a30 matchLen=", a30.matchLen(re"(a|a)*[bc]"), " a30 find=", a30.find(re"(a|a)*[bc]"), " a2000 find=", a2000.find(re"(a|b)*c")
for s in [a30, a10, a2000, "", "c", 'a'.repeat(39) & "c"]:
  nat(matchHit(s)); nat(findCode(s)); nat(matchLenCode(s)); nat(boundsCode(s)); nat(missOnLong(s))
  nat(replaceStops(s)); nat(shortMatch(s)); nat(shortMiss(s)); nat(missImpliesNoByte(s)); nat(jitStack(s))
  nat(altPlus(s))
natDump()
v(matchHit, "cf_match_hit")
v(findCode, "cf_find_code")
v(matchLenCode, "cf_matchlen_code")
v(boundsCode, "cf_bounds_code")
v(missOnLong, "cf_miss_long")
v(replaceStops, "cf_replace_stops")
v(shortMatch, "cf_short_match")
v(shortMiss, "cf_short_miss")
v(missImpliesNoByte, "cf_miss_no_c")
v(jitStack, "cf_jit_stack")
v(altPlus, "alt_plus")
