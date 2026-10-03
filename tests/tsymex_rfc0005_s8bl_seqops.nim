## RFC-0005 (soundness channels) slice S8bl, item 1 -- the rest of the job's
## list of `var`-parameter routines a target can call: `del`, `insert`,
## `delete`, `add` on a string and a seq, `inc` / `dec` with a second
## argument, and an explicit `=copy`. (`shallowCopy` is not declared under
## ORC, the toolchain's default; it stays classified as declined.) Each is
## modelled (its write is observed) or declines naming the magic; none is a
## silent no-op.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasMsg(errs: seq[SymexErrorInfo], needle: string): bool =
  for e in errs:
    if needle in e.msg: return true
  false

proc soDel(x: int) =
  var s = @[x, 2, 3]
  s.del(0)                         # the last element moves into slot 0
  if s.len != 2 or s[0] != 3 or s[1] != 2: symexTarget("del_dead")

proc soInsert(x: int) =
  var s = @[1, 2]
  s.insert(x, 1)
  if s.len != 3 or s[1] != x or s[2] != 2: symexTarget("ins_dead")

proc soDelete(x: int) =
  var s = @[1, x, 3]
  s.delete(1)
  if s.len != 2 or s[1] != 3: symexTarget("dlt_dead")

proc soStrAdd(c: char) =
  var s = "ab"
  s.add c
  s.add "yz"
  if s.len != 5 or s[2] != c or s[4] != 'z': symexTarget("sadd_dead")

proc soIncBy(x: int) =
  if x < -100 or x > 100: return
  var a = x
  inc(a, 3)
  dec(a, 5)
  if a != x - 2: symexTarget("incby_dead")

proc soCopy(x: int) =
  var a = @[x]
  var b: seq[int]
  `=copy`(b, a)
  if b.len != 1 or b[0] != x: symexTarget("copy_dead")

suite "S8bl (1): the rest of the var-parameter list":
  test "del, insert, delete on a seq":
    for (d, lbl) in [(symexFind(soDel, tLabel("del_dead")), "del_dead"),
                     (symexFind(soInsert, tLabel("ins_dead")), "ins_dead"),
                     (symexFind(soDelete, tLabel("dlt_dead")), "dlt_dead")]:
      checkpoint lbl & " " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat

  test "add on a string (a char, a string)":
    let d = symexFind(soStrAdd, tLabel("sadd_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "inc / dec with a second argument":
    let d = symexFind(soIncBy, tLabel("incby_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an explicit `=copy`":
    let d = symexFind(soCopy, tLabel("copy_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
