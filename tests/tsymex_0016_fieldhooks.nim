## RFC-0016 PRC-07 slice B: the union image is carried only for a variant type
## that is plain bits (`supportsCopyMem`). A discriminator write on a type with
## lifetime hooks runs the old arm's destructor/reset, so the old bytes are not
## the new arm's slots; the new arm is the sound havoc (`dwmHavoc`,
## `feUncheckedDiscBytes`). Built with `--fieldChecks:off` (its `.nim.cfg`).
import std/[unittest]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

type
  K = enum ka, kb
  Plain = object
    case k: K
    of ka: a: int
    of kb: b: int
  Hooked = object
    case k: K
    of ka: a: int
    of kb: b: int

var copies = 0
proc `=copy`(d: var Hooked; s: Hooked) =
  inc copies
  d.k = s.k

proc sutPlain(v: int) =
  var x = Plain(k: ka, a: v)
  x.k = kb
  if x.b == 3: symexTarget("hit")

proc sutHooked(v: int) =
  var x = Hooked(k: ka, a: v)
  x.k = kb
  if x.b == 3: symexTarget("hit")

suite "PRC-07 slice B: the union image needs supportsCopyMem":
  test "a plain-bits variant stays exact on a branch-changing write":
    let r = symexFind(sutPlain, tLabel("hit"))
    checkpoint show(r.errors)
    when defined(cpp):
      # cpp holds no image: the havoc model, and the read is an inactive member
      check r.errors.named(feUncheckedDiscBytes)
    else:
      check r.status == sxSat
      check r.witness[0] == 3
      check not r.errors.named(feUncheckedDiscBytes)

  test "a variant with a user copy hook is the havoc model, never exact":
    let r = symexFind(sutHooked, tLabel("hit"))
    checkpoint show(r.errors)
    check r.errors.named(feUncheckedDiscBytes)
