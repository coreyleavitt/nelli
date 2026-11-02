## RFC-0005 (soundness channels) slice S8bl, item 4 -- borrowed routines
## beyond S8bc: a borrow declaring fewer formals than its base, and an
## argument read at its base type by every type query of the base routine's
## arms (S8bc consulted the view in `classifyType` / `valueTypeName` only).
import std/[unittest, macros, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/dsl_parser

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

type
  FM = distinct int
  FName = distinct string

# Fewer formals than the base `inc(x: var T, y = 1)`. Nim 2.2.10's code
# generator crashes on a CALL of this borrow, so the SUT below is only
# parsed (`irOf`), never compiled to code.
proc inc(m: var FM) {.borrow.}

proc incFewer(x: int) =
  var m = FM(x)
  inc(m)
  if int(m) == 7: symexTarget("inc_fewer")

macro irOf(p: typed): untyped =
  newLit(render(parseProc(p.getImpl).body))

proc find(n: FName, c: char, start: Natural = 0, last = -1): int {.borrow.}
proc contains(n: FName, c: char): bool {.borrow.}
proc startsWith(n: FName, p: string): bool {.borrow.}

proc bvFind(n: FName) =
  if string(n).len == 3 and n.find('z') == 1: symexTarget("bv_find")
  if n.find('z') < -1: symexTarget("bv_find_dead")

proc bvContains(n: FName) =
  if string(n).len == 2 and n.contains('q') and string(n)[0] != 'q':
    symexTarget("bv_contains")

proc bvStarts(n: FName) =
  if string(n).len == 3 and n.startsWith("ab"): symexTarget("bv_starts")

suite "S8bl (4): a borrow with fewer formals than its base":
  test "inc(m) is the base's inc(m, 1) (was the inc arm's decline)":
    let ir = irOf(incFewer)
    checkpoint ir
    check "unsupported" notin ir.toLowerAscii
    check "m:=(bAdd m 1)" in ir

suite "S8bl (4): a borrowed routine's argument at its base type":
  test "find(n, c) on a distinct string":
    let r = symexFind(bvFind, tLabel("bv_find"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(bvFind(r.witness[0]), "bv_find")
    let d = symexFind(bvFind, tLabel("bv_find_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "contains(n, c) on a distinct string":
    let r = symexFind(bvContains, tLabel("bv_contains"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(bvContains(r.witness[0]), "bv_contains")

  test "startsWith(n, p) on a distinct string":
    let r = symexFind(bvStarts, tLabel("bv_starts"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(bvStarts(r.witness[0]), "bv_starts")
