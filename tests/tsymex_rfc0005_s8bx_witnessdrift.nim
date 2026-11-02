## RFC-0005 (soundness channels) slice S8bx, item 2 -- the witness
## renderability predicate and the witness reader drifted.
##
## A case object's arm holding a seq of seqs is the unbacked scoped-decline
## placeholder, which `isRenderableWitnessTy` calls renderable whatever its
## element: the reader renders it as an empty literal. But the reader
## recursed into the element for its TYPE through `emitTyAndReader`, and an
## element no reader reads (an object holding a ref inside a Table) hit the
## reader's invariant guard at macro time: the whole file failed to compile
## ("seq witness reader for seq[Widget{...}] not yet implemented"). The seq
## reader and the predicate now share one classifier (`seqWitnessReader`),
## and a type is always rendered: a reader no witness reaches is never
## emitted, so only a reader that IS emitted can carry the guard.
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/types

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
  Widget = object
    a: int
    b: Table[string, ref int]

  ShapeKind = enum skWidgets, skCount

  Shape = object
    case kind: ShapeKind
    of skWidgets:
      widgets: seq[seq[Widget]]
    of skCount:
      count: int

  Holder = object
    tag: int
    nested: seq[seq[Widget]]

proc variantArm(s: Shape, y: int) =
  if y == 42:
    symexTarget("variant_arm")

proc plainField(h: Holder, y: int) =
  if h.tag == 3 and y == 1:
    symexTarget("plain_field")

suite "S8bx (2): a placeholder seq of an element no reader reads":

  test "a case-object arm renders (was a compile crash)":
    let r = symexFind(variantArm, tLabel("variant_arm"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[1] == 42
      check reproduces(variantArm(r.witness[0], r.witness[1]), "variant_arm")

  test "a plain object field renders (was a compile crash)":
    let r = symexFind(plainField, tLabel("plain_field"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].tag == 3
      check r.witness[0].nested.len == 0
      check reproduces(plainField(r.witness[0], r.witness[1]), "plain_field")

suite "S8bx (2): one classifier for the predicate and the reader":

  test "the element no reader reads is unrenderable on its own":
    let w = IRType(kind: itTuple, objectName: "Widget",
                   fields: @[tInt(), IRType(kind: itTable, tabKeyTy: tString(),
                     tabValTy: IRType(kind: itRef, refPointeeTy: tInt()))],
                   fieldNames: @["a", "b"])
    let s = IRType(kind: itSeq, seqElemTy: w)
    check seqWitnessReader(s) == swrNone
    check not isRenderableWitnessTy(s)
