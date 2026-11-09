## RFC-0016 ADM-IR (section 8.1, "Admission is a proof the IR demands").
##
## `Admit`'s fields are private, so only `admission.nim` can make one. The rule
## is that an IR constructor of a keyed-axis node takes the axis's `Admit`, so a
## parser arm that skips the table does not type-check. This file is that
## rule's test, one block per axis whose node has a constructor:
##
##   * type x memory-op (`typeop:fieldDefault/<kind>`): `mkZeroValue`.
##
## The compile-time half is `compiles(...)`: the call without a proof must not
## compile and the call with one must. The census half counts raw
## `IRExpr(kind: iekZeroValue` constructions outside `types.nim` (the IR
## module), allowlist zero. The behavioural half runs the real parser entry
## (`symexFind`): a declined row still declines, and an admitted one still
## decides as before.
import std/[unittest, strutils, os, tables]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/types
import nelli/smt/typeaxes

suite "ADM-IR: the type x memory-op axis (mkZeroValue)":
  let tbl = tTable(tString(), tInt(64, true))
  test "no proof, no node":
    check not compiles(mkZeroValue(tbl))
  test "a wrong-axis proof is not a proof":
    check not compiles(mkZeroValue(admitTypeClass(ntyInt, tcClassify), tbl))
  test "with the fieldDefault proof it builds":
    check compiles(mkZeroValue(admitTypeOp(itTable, moFieldDefault, toZeroValue), tbl))
    let a = admitTypeOp(itTable, moFieldDefault, toZeroValue)
    check a.admitted
    let e = mkZeroValue(a, tbl)
    check e.kind == iekZeroValue
    check e.zvTy == tbl
  test "a declined proof does not reach the constructor":
    let a = admitTypeOp(itUninterp, moFieldDefault, toZeroValue)
    check not a.admitted
    expect AssertionDefect:
      discard mkZeroValue(a, tTable(tString(), tInt(64, true)))
  test "a proof of another operation does not reach the constructor":
    let a = admitTypeOp(itTable, moLetCursor)
    expect AssertionDefect:
      discard mkZeroValue(a, tbl)

proc rawCount(): int =
  ## Raw constructions of the zero-value node outside the IR module.
  let dir = currentSourcePath().parentDir() / ".." / "src" / "nelli"
  let tok = "IRExpr(kind: " & "iekZeroValue"
  for f in walkDirRec(dir):
    if not f.endsWith(".nim") or f.endsWith("smt" / "types.nim"): continue
    for line in readFile(f).splitLines:
      let i = line.find('#')
      if tok in (if i >= 0: line[0 ..< i] else: line): inc result

suite "ADM-IR: no raw construction outside the IR module":
  test "iekZeroValue is built only by mkZeroValue":
    check rawCount() == 0

type Tab = Table[int, int]
proc zeroTable(k: int) =
  var t: Tab
  if t.len == 0: symexTarget("hit")
proc zeroTableNonEmpty(k: int) =
  var t: Tab
  if t.len > 0: symexTarget("hit")
proc zeroSeq(k: int) =
  var s: seq[int]
  if s.len == 0: symexTarget("hit")

suite "ADM-IR: verdicts through the real parser are unchanged":
  test "an admitted zero-value row still decides":
    let a = symexFind(zeroTable, tLabel("hit"))
    check a.status == sxSat
    let b = symexFind(zeroTableNonEmpty, tLabel("hit"))
    check b.status == sxUnsat
    check symexFind(zeroSeq, tLabel("hit")).status == sxSat

proc zeroCstring(k: int) =
  var f: cstring
  if k == 1: symexTarget("hit")

suite "ADM-IR: a declined fieldDefault row still declines through the parser":
  test "an uninterp zero is not built; the walk reports the decline":
    check not admitTypeOp(itUninterp, moFieldDefault, toZeroValue).admitted
    let r = symexFind(zeroCstring, tLabel("hit"))
    check r.status == sxUnknown
    var seen = false
    for e in r.errors:
      if e.kind == feUnsupportedParamType and "no zero value" in e.msg:
        seen = true
    check seen
