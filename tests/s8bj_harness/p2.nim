import std/[re, strutils, os]
proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next
let args = readFile(paramStr(1)).splitLines()
let alpha = args[0].unescape("", "")
let maxLen = parseInt(args[1])
for p0 in args[2 .. ^1]:
  if p0.len == 0: continue
  let p = p0.unescape("", "")
  var rx: Regex
  try: rx = re(p)
  except RegexError as e:
    echo p0, " E:", e.msg.splitLines()[0]
    continue
  var line = p0 & " :"
  for s in words(alpha, maxLen):
    let fb = findBounds(s, rx)
    line.add " " & escape(s, "", "") & "=" & $find(s, rx) & "/" &
      $matchLen(s, rx) & "/" & $fb.last & "/" & escape(replace(s, rx, "-"), "", "")
  echo line
