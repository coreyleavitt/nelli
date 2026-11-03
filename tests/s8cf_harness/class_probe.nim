# S8cf item 7: where 8.37's UTF classes differ from the model.
import std/[re, strutils, unicode, tables, algorithm]
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
const names = ["alpha","lower","upper","alnum","ascii","blank","cntrl","digit","graph","print","punct","space","word","xdigit"]
var pats: seq[string]
for nm in names:
  for pre in ["(*UTF)(*UCP)"]:
    pats.add pre & "[[:" & nm & ":]]"
    pats.add pre & "[[:^" & nm & ":]]"
    pats.add pre & "[^[:" & nm & ":]]"
    pats.add pre & "[^[:^" & nm & ":]]"
    pats.add pre & "[[:" & nm & ":]\\x{100}]"
    pats.add pre & "[[:^" & nm & ":]\\x{100}]"
    pats.add pre & "[[:" & nm & ":]_]"
    pats.add pre & "[[:^" & nm & ":]_]"
for e in ["\\S","\\D","\\W","\\H","\\V"]:
  for pre in ["(*UTF)", "(*UTF)(*UCP)"]:
    pats.add pre & "[" & e & "]"
    pats.add pre & "[^" & e & "]"
    pats.add pre & "[" & e & "a]"
    pats.add pre & "[^" & e & "a]"
    pats.add pre & "[" & e & "\\x{100}]"
    pats.add pre & "[^" & e & "\\x{100}]"
    pats.add pre & "[" & e & "\\x{e9}]"
var cps: seq[int]
for c in 0 .. 0x17F: cps.add c
for c in [0x180E,0x2000,0x2028,0x2029,0x202F,0x205F,0x3000,0x660,0x4E00,0xFF10,0x10000,0x10FFFF,0x1680,0x85,0x212A,0x17F]: cps.add c
var diffs = initTable[string, seq[int]]()
var total = 0
var declined = 0
for p in pats:
  let pr = parsePcre(p, false, pcreOlderThan(8, 45))
  if pr.status != psOk: echo "unread ", p, " ", pr.status; continue
  if pr.classPre845 and pcreOlderThan(8, 45): inc declined; continue
  let n = buildNfa(pr)
  if not n.ok: echo "noNfa ", p; continue
  let rx = re(p)
  for c in cps:
    let u = Rune(c).toUTF8
    inc total
    let nat = matchLen(u, rx) == u.len
    let g = pcreExec(n, u, 0, true)
    let mod0 = g[0] >= 0 and g[2] - g[1] == u.len
    if nat != mod0: diffs.mgetOrPut(p, @[]).add c
echo "declined ", declined, " total ", total, " patterns differing ", diffs.len
var ks: seq[string]
for k in diffs.keys: ks.add k
ks.sort
for k in ks:
  var v = diffs[k]
  var rng: seq[string]
  var i = 0
  while i < v.len and rng.len < 6:
    var j = i
    while j + 1 < v.len and v[j+1] == v[j] + 1: inc j
    rng.add toHex(v[i], 4) & (if j > i: "-" & toHex(v[j], 4) else: "")
    i = j + 1
  echo k, " n=", v.len, " ", rng.join(" ")
