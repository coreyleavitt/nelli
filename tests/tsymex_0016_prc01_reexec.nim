## RFC-0016 PRC-01. Windows re-exec replay marshals case objects instead of
## declining. Windows has no `fork`, so the replay re-executes the binary and
## hands the child the witness and every variable the SUT may reach; Linux runs
## that path under `-d:nelliReplayReexec` (this file's `.nim.cfg`), so every
## leg exercises the marshalling. Before PRC-01 a module-level variable of case
## object type, and a case object in a witness handed to `replayWitness`
## directly, declined with "replay not marshallable".
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/replayproc
from nelli/smt/runtime import hostAdmission

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

# `gG` is never written: a path past its read is a replay candidate.
var gG: int

type
  Kind = enum kA, kB
  Shape = object
    case kind: Kind
    of kA: a: int
    of kB: b: string
  Node = ref object
    v: int
    next: Node

proc caseObj(s: Shape) =
  if gG == 0 and s.kind == kB and s.b == "hi":
    symexTarget("t")

proc aliased(x, y: Node) =
  if gG == 0 and x != nil and x == y and x.v == 4:
    symexTarget("t")

# The host's global is a case object on its kB branch, holding a string: the
# child has to be handed the discriminator and then that branch.
var gShape = Shape(kind: kB, b: "zz")
proc caseGlobal(k: int) =
  if gG == 0 and k == 3 and gShape.kind == kB and gShape.b == "zz":
    symexTarget("t")

# The same global on its other branch: the SUT can only hit if the child reads
# the branch the host holds (the model may take either).
var gOther = Shape(kind: kA, a: 41)
proc caseGlobalA(k: int) =
  if gG == 0 and k == 3 and gOther.kind == kA and gOther.a == 41:
    symexTarget("t")

# A non-nil `ptr` global: its target is unknown memory, so this keeps declining,
# and says why.
var gBox = 5
var gPtr: ptr int = addr gBox
proc ptrGlobal(k: int) =
  if gG == 0 and k == 3 and gPtr[] == 5:
    symexTarget("t")

# A SUT with a result type and a constructor of a user type in its body: the
# footprint reads type symbols (INT-14), which must not decline it.
proc makeShape(k: int): Shape =
  if k == 3: Shape(kind: kB, b: "q") else: Shape(kind: kA, a: k)
proc typeSyms(k: int) =
  let s = makeShape(k)
  if gG == 0 and s.kind == kB:
    symexTarget("t")

suite "PRC-01: case objects cross to the re-executed child":
  test "a case-object global is handed over (kB branch with a string)":
    # A symexFind run is decided only on a verified build row; cpp under Z3
    # 4.13.4 has none by design (`feHostUnadmitted`), so the pin skips there.
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      let r = symexFind(caseGlobal, tLabel("t"))
      checkpoint show(r.errors)
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed

  test "a case-object global is handed over (kA branch)":
    # A symexFind run is decided only on a verified build row; cpp under Z3
    # 4.13.4 has none by design (`feHostUnadmitted`), so the pin skips there.
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      let r = symexFind(caseGlobalA, tLabel("t"))
      checkpoint show(r.errors)
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed

  test "a case-object witness given to replayWitness replays":
    let hit = replayWitness(caseObj, (Shape(kind: kB, b: "hi"),),
                            tLabel("t"), {})
    checkpoint hit.detail
    check hit.outcome == roConfirmed
    let miss = replayWitness(caseObj, (Shape(kind: kA, a: 1),),
                             tLabel("t"), {})
    checkpoint miss.detail
    check miss.outcome == roRefuted

  test "ref identity survives the crossing":
    let n = Node(v: 4)
    let hit = replayWitness(aliased, (n, n), tLabel("t"), {})
    checkpoint hit.detail
    check hit.outcome == roConfirmed
    let miss = replayWitness(aliased, (n, Node(v: 4)), tLabel("t"), {})
    checkpoint miss.detail
    check miss.outcome == roRefuted

  test "type symbols in the footprint do not decline":
    # A symexFind run is decided only on a verified build row; cpp under Z3
    # 4.13.4 has none by design (`feHostUnadmitted`), so the pin skips there.
    if hostAdmission().isSome:
      skipUnadmitted()
    else:
      let r = symexFind(typeSyms, tLabel("t"))
      checkpoint show(r.errors)
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed

  test "a non-nil ptr global still declines, naming the ptr":
    # `replayWitness` is the direct form: the walker does not model `gPtr`, so
    # no search reaches a replay of this SUT.
    let r = replayWitness(ptrGlobal, (3,), tLabel("t"), {})
    checkpoint r.detail
    when replayReexecs:
      check r.outcome == roDeclined
      check "replay not marshallable" in r.detail
      check "non-nil `ptr`" in r.detail
    else:
      check r.outcome == roConfirmed

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 296
