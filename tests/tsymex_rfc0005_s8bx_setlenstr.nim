## RFC-0005 (soundness channels) slice S8bx, item 5 -- a string's `setLen`
## over a symbolic string.
##
## S8bl modelled `s.setLen(n)` on a string as the prefix `substr(s, 0, n)`
## when it shrinks and `s ++ pad` (a fresh pad of `n - len(s)` bytes in
## `("\0")*`) when it grows. Reading a byte back (`t[i]`, a `str.at` of the
## substr or the concat) was undecided by both pinned Z3s within
## `seqQueryRLimit` for a symbolic `s`, so S8bl pinned it on ground strings
## only. Each label below reads a byte of the result of a symbolic string
## and must decide: the dead ones `sxUnsat`, the live ones `sxSat` with a
## witness that replays.
import std/[unittest, strutils]
import nelli
import nelli/symex

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# A grown byte is NUL.
proc growPad(s: string, n: int) =
  if n < 0 or n > 12 or s.len > 8: return
  var t = s
  t.setLen(n)
  if n > s.len and t[n - 1] != '\0': symexTarget("grow_pad_dead")
  if n == s.len + 3 and s.len >= 1 and t[n - 1] == '\0' and t[0] == 'q':
    symexTarget("grow_pad_live")

# A grown string keeps its prefix.
proc growKeep(s: string, n: int) =
  if n < 0 or n > 12 or s.len > 8: return
  var t = s
  t.setLen(n)
  if n > s.len and s.len >= 2 and t[1] != s[1]: symexTarget("grow_keep_dead")
  if n > s.len and s.len == 3 and t[2] == 'z': symexTarget("grow_keep_live")

# A shrunk string keeps its prefix.
proc shrinkKeep(s: string, n: int) =
  if n < 0 or n > 12 or s.len > 8: return
  var t = s
  t.setLen(n)
  if n >= 1 and n < s.len and t[n - 1] != s[n - 1]:
    symexTarget("shrink_keep_dead")
  if n == 2 and s.len == 6 and t[1] == 'w': symexTarget("shrink_keep_live")

suite "S8bx (5): setLen over a symbolic string decides":

  test "a grown byte is NUL":
    let d = symexFind(growPad, tLabel("grow_pad_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(growPad, tLabel("grow_pad_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(growPad(r.witness[0], r.witness[1]), "grow_pad_live")

  test "a grown string keeps its prefix":
    let d = symexFind(growKeep, tLabel("grow_keep_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(growKeep, tLabel("grow_keep_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(growKeep(r.witness[0], r.witness[1]), "grow_keep_live")

  test "a shrunk string keeps its prefix":
    let d = symexFind(shrinkKeep, tLabel("shrink_keep_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let r = symexFind(shrinkKeep, tLabel("shrink_keep_live"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(shrinkKeep(r.witness[0], r.witness[1]),
                       "shrink_keep_live")
