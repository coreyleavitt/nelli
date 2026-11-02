## S8co item 10 / S8cf: an unbounded no-match refutation past the safe length. A stopped
## call reads false, so a subject that does match can read as a miss.
import std/re
import h
proc altMiss(s: string) =
  if s.len > 0 and s[s.len - 1] == 'c' and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_miss")
proc altMissB(s: string) =
  if s.len == 31 and s[30] == 'c' and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_miss_b")
proc altShort(s: string) =
  if s == "ac" and not s.contains(re"(a|a)*b|c$"):
    symexTarget("alt_short")
for s in ['a'.repeat(30) & "c", "ac", "c"]:
  nat(altMiss(s)); nat(altMissB(s)); nat(altShort(s))
natDump()
v(altMiss, "alt_miss")
v(altMissB, "alt_miss_b")
v(altShort, "alt_short")
