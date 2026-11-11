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
##
## RFC-0016 W3-z int4x: the live witness's tail walk (`verifyTailDefined`)
## asks `t[0] == 'q'` of the grown string. Its scratch check left out the
## `pc` conjunct that defines `t` (`s ++ pad`), so it asked about any string
## and spent its whole bound undecided, three times: 849 s for this check,
## past CI's 900 s for the file, where main took 0.9 s.
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/smt/runtime

proc tailUnitLines(log: string): seq[int] =
  ## The units of each tail walk (`k10b-tail` lines of the K7 units log).
  for line in readFile(log).splitLines:
    let f = line.split('\t')
    if f.len >= 2 and f[1] == "k10b-tail": result.add parseInt(f[0])

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

  test "walker 352: a tail check carries its free symbols' definitions (int4x)":
    check parseInt(symexWalkerVersion) >= 352

  test "a grown byte is NUL":
    let d = symexFind(growPad, tLabel("grow_pad_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let log = getTempDir() / "s8bx_grow_pad_live_units.log"
    removeFile(log)
    putEnv(walkUnitsLogEnv, log)
    let r = try: symexFind(growPad, tLabel("grow_pad_live"))
            finally: delEnv(walkUnitsLogEnv)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    # int4x: every branch of the witness's tail is decided by the pins and
    # the `pc` that defines the grown string, so no scratch check of it may
    # spend its whole bound (`concreteBranchRLimit`). A check that does makes
    # its tail walk spend at least that bound, so each tail walk is pinned
    # below one.
    let tails = tailUnitLines(log)
    removeFile(log)
    checkpoint "tail walk units: " & $tails
    check tails.len >= 1
    for u in tails:
      check u < int(concreteBranchRLimit(defaultSymexSettings()))
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
