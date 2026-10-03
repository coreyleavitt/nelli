## Compile probe: one escaped pattern per line; prints OK or the first
## line of the RegexError message and the caret offset.
import std/[re, strutils, os]
for p0 in readFile(paramStr(1)).splitLines():
  if p0.len == 0 or p0.startsWith("#"): continue
  let p = p0.unescape("", "")
  try:
    discard re(p)
    echo p0, " => OK"
  except RegexError as e:
    let ls = e.msg.splitLines()
    var off = -1
    if ls.len >= 3: off = ls[2].find('^')
    echo p0, " => E:", ls[0], " @", off
