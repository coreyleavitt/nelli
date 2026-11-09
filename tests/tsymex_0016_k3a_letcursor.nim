## RFC-0016 K3a -- the type x memory-op axis, end to end: `let c = g` over a
## case object that holds a seq arm.
##
## `holdsSharedMemory` had no `itVariant` arm, so `letCursorDecline` never
## fired for a variant: the walker decided `let c = gV; gV.s[0] = 9; c.s[0]`
## where the plain-object twin (same seq field) declines. Natively the `let`
## shares the memory under refc and copies under orc/arc (B-04, ran), so a
## verdict for one build would be wrong for the other. The axis row
## `typeop:letCursor/variant` now answers "holds shared memory" through its
## arms, and the shape declines like its twin; a variant of scalars is still a
## value and is still decided.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/canonicalize
import ./s8cu_helpers

type
  V = object
    case k: bool
    of true: s: seq[int]
    of false: n: int
  VScalar = object
    case k: bool
    of true: a: int
    of false: n: int
  Plain = object
    s: seq[int]

var
  gV: V
  gVS: VScalar
  gP: Plain
  gSq: seq[int]
  gSt: string

proc vcVariantSeq(x: int) =
  gV = V(k: true, s: @[x, 1])
  let c = gV
  gV.s[0] = 9
  if c.s[0] == 9: symexTarget("shared")

proc vcPlainSeq(x: int) =
  gP = Plain(s: @[x, 1])
  let c = gP
  gP.s[0] = 9
  if c.s[0] == 9: symexTarget("shared")

proc vcSeq(x: int) =
  gSq = @[x, 1]
  let c = gSq
  gSq[0] = 9
  if c[0] == 9: symexTarget("shared")

proc vcString(x: int) =
  gSt = "ab"
  let c = gSt
  gSt[0] = 'z'
  if c[0] == 'z' and x == 1: symexTarget("shared")

proc vcVariantScalar(x: int) =
  gVS = VScalar(k: true, a: x)
  let c = gVS
  gVS.a = 9
  if x != 9 and c.a == 9: symexTarget("copied")

suite "RFC-0016 K3a: let-cursor x type":
  test "version floor: K3a bumped the walker to 291":
    check parseInt(symexWalkerVersion) >= 291

  test "a variant holding a seq arm declines like its plain-object twin":
    pinDecline(vcPlainSeq, cellKey(axTypeOp, "letCursor/tuple"),
               feUnsupportedOp, target = tLabel("shared"))
    pinDecline(vcVariantSeq, cellKey(axTypeOp, "letCursor/variant"),
               feUnsupportedOp, target = tLabel("shared"))

  test "a seq and a string decline":
    pinDecline(vcSeq, cellKey(axTypeOp, "letCursor/seq"),
               feUnsupportedOp, target = tLabel("shared"))
    pinDecline(vcString, cellKey(axTypeOp, "letCursor/string"),
               feUnsupportedOp, target = tLabel("shared"))

  test "a variant of scalars is a value: still decided":
    let r = symexFind(vcVariantScalar, tLabel("copied"), pinSettingsConst)
    check r.status == sxUnsat
