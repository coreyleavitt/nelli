## RFC-0005 (soundness channels) slice S8bl, item 2 -- the unrecognised
## pair loop over a pinned input, with targets INSIDE its body.
##
## Item 2 grounds the scan (the pinned input, the callee's clean result), so
## most `if` guards in such a body fold to a literal. Walking the side a
## literal rules out kept both sides of every `if`: five folded guards in
## the body were 32 copies of one path per iteration, and this file's first
## SUT ran past 900 s (killed) where the S8bl base answered `sxUnknown` in
## 87 s. A folded guard now takes one side only (`guardLiteral`).
##
## The input holds four pairs (`aa=bb`, `cc=dd`, `ee=ff`, `gg=hh`) and the
## terminator, so the loop body runs five times (the fifth breaks).
import std/unittest
import nelli
import nelli/symex

type ScanError = object of CatchableError

proc readCStringOpt(s: string, offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

const pairsLit = "aa\x00bb\x00cc\x00dd\x00ee\x00ff\x00gg\x00hh\x00\x00"

proc plBody(s: string) =
  symexAssume(s == pairsLit)
  let n = s.len
  var c = 0
  var i = 0
  while i < n:
    if c == 3 and i == 18: symexTarget("pl_top_c3")
    if c == 3 and i != 18: symexTarget("pl_top_c3_dead")
    let (key, p1) = readCStringOpt(s, i)
    if c == 3 and key == "gg": symexTarget("pl_key_c3")
    if c == 3 and key != "gg": symexTarget("pl_key_c3_dead")
    if c == 4 and key.len != 0: symexTarget("pl_key_c4_dead")
    if key.len == 0:
      break
    let (val, p2) = readCStringOpt(s, p1)
    c += 1
    i = p2

proc plAfter(s: string) =
  symexAssume(s == pairsLit)
  let n = s.len
  var pairs: seq[(string, string)] = @[]
  var i = 0
  while i < n:
    let (key, p1) = readCStringOpt(s, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringOpt(s, p1)
    pairs.add (key, val)
    i = p2
  if pairs.len == 4 and pairs[3][1] == "hh": symexTarget("pl_four")
  if pairs.len != 4: symexTarget("pl_four_dead")

suite "RFC-0005 S8bl item 2 -- targets inside the pair loop":
  test "in-body targets: reached ones are sxSat, dead ones sxUnsat, all exact (was a hang past 900 s)":
    block:
      let r = symexFind(plBody, tLabel("pl_top_c3"))
      checkpoint $r.status & " " & $r.soundness & " " & $r.errors
      check r.status == sxSat
    block:
      let r = symexFind(plBody, tLabel("pl_key_c3"))
      checkpoint $r.status & " " & $r.soundness & " " & $r.errors
      check r.status == sxSat
    block:
      let r = symexFind(plBody, tLabel("pl_top_c3_dead"))
      checkpoint $r.status & " " & $r.soundness & " " & $r.errors
      check r.status == sxUnsat
    block:
      let r = symexFind(plBody, tLabel("pl_key_c3_dead"))
      checkpoint $r.status & " " & $r.soundness & " " & $r.errors
      check r.status == sxUnsat
    block:
      let r = symexFind(plBody, tLabel("pl_key_c4_dead"))
      checkpoint $r.status & " " & $r.soundness & " " & $r.errors
      check r.status == sxUnsat

  test "after the loop: four pairs collected, exactly":
    block:
      let r = symexFind(plAfter, tLabel("pl_four"))
      checkpoint $r.status & " " & $r.soundness & " " & $r.errors
      check r.status == sxSat
    block:
      let r = symexFind(plAfter, tLabel("pl_four_dead"))
      checkpoint $r.status & " " & $r.soundness & " " & $r.errors
      check r.status == sxUnsat
