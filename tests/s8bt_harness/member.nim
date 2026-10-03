## RFC-0005 S8bt -- membership of a word in a `pcre_select` regex (`RNode`),
## the marker symbols as S8bj's language tests use them, and the start
## variants' prefixes.
import std/tables
import nelli/smt/pcre_select

const markSym* = 256
const markSym2* = 257

var memo: Table[(pointer, int), seq[int]]

proc ends(r: RNode; w: seq[int]; i: int): seq[int] =
  ## Every end of a match of `r` from `i` in `w` (memoized per word).
  let key = (cast[pointer](r), i)
  if key in memo: return memo[key]
  case r.kind
  of rkEmpty: result = @[]
  of rkEps: result = @[i]
  of rkSet:
    result = (if i < w.len and w[i] < 256 and char(w[i]) in r.bytes: @[i + 1]
              else: @[])
  of rkMark:
    result = (if i < w.len and w[i] == markSym: @[i + 1] else: @[])
  of rkMark2:
    result = (if i < w.len and w[i] == markSym2: @[i + 1] else: @[])
  of rkCat:
    var cur = @[i]
    for k in r.kids:
      var nx: seq[int]
      for c in cur:
        for e in ends(k, w, c):
          if e notin nx: nx.add e
      cur = nx
    result = cur
  of rkAlt:
    for k in r.kids:
      for e in ends(k, w, i):
        if e notin result: result.add e
  of rkStar:
    result = @[i]
    var frontier = @[i]
    while frontier.len > 0:
      var nx: seq[int]
      for c in frontier:
        for e in ends(r.kids[0], w, c):
          if e notin result:
            result.add e
            nx.add e
      frontier = nx
  memo[key] = result

proc member*(r: RNode; w: seq[int]): bool =
  memo.clear()
  w.len in ends(r, w, 0)

proc toSyms*(s: string): seq[int] =
  for c in s: result.add ord(c)

proc prefixOf*(pc: PrevClass): string =
  case pc
  of pcStart: ""
  of pcOther: "b"
  of pcLF: "\n"
  of pcCRLF: "\r\n"
  of pcCR: "\r"
  of pcNl: "\x0c"
  # RFC-0005 S8bt: inside a character (no start variant).
  of pcU1: "\xC2"
  of pcU2: "\xE2"
  of pcU3: "\xE2\x80"
