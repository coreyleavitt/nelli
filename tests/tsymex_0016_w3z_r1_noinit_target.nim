## RFC-0016 W3-z R1 (finding U3). `tUndefined` must hit `ubIndeterminateRead`
## at the `{.noinit.}` read site. The read travels as `ub` on a `feGlobalHavoc`
## degrade (`unwrittenUb`), which marks the path spurious, not incomplete, and
## the only hit test lived in `haltUndefined`: so `symexFind(f, tUndefined())`
## over a reachable indeterminate read was a trusted `sxUnsat`.
## `ubTailUnverified` is accepted by `tUndefined` but is never a hit.
## The guards are nested `if`s: a read inside an `and` operand is lowered
## unguarded (a lowering-time degrade is not an inline defect fork, so
## `shortCircuitPartIsPure` calls it pure), which is a separate gap.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutNoinitRead(k: int) =
  var x {.noinit.}: int
  if k > 3:
    if x == 0: symexTarget("z")

proc sutNoinitReadAlways() =
  var x {.noinit.}: int
  if x == 0: symexTarget("z")

proc sutNoinitWritten(k: int) =
  var x {.noinit.}: int
  x = k
  if x == 7: symexTarget("w")

proc sutNoinitGuarded(k: int) =
  ## The read is unreachable: `k > 3 and k < 2` is false.
  var x {.noinit.}: int
  if k > 3:
    if k < 2:
      if x == 0: symexTarget("z")

proc sutPlain(k: int) =
  if k == 3: symexTarget("hit")

suite "W3-z R1: tUndefined and the noinit read":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 312

  test "the default target finds a reachable indeterminate read":
    let r = symexFind(sutNoinitRead, tUndefined())
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check r.witness[0] > 3
    check UbKind(ubIndeterminateRead) in r.soundness.undefinedKinds
    check not r.trusted

  test "the listed kind is a hit":
    let r = symexFind(sutNoinitReadAlways, tUndefined({UbKind(ubIndeterminateRead)}))
    checkpoint show(r.errors) & " " & $r.soundness
    check r.status == sxSat
    check r.soundness.undefinedKinds == {UbKind(ubIndeterminateRead)}

  test "an unlisted kind is not a hit":
    let r = symexFind(sutNoinitReadAlways, tUndefined({UbKind(ubSignedOverflow)}))
    check r.status != sxSat

  test "a write before the read is no hit: trusted sxUnsat":
    let r = symexFind(sutNoinitWritten, tUndefined())
    check r.status == sxUnsat
    check r.trusted

  test "an unreachable read is no hit":
    let r = symexFind(sutNoinitGuarded, tUndefined())
    check r.status != sxSat

  test "a program with no read is still a trusted sxUnsat":
    let r = symexFind(sutPlain, tUndefined())
    check r.status == sxUnsat
    check r.trusted

  test "ubTailUnverified is refused, and the default omits it":
    expect AssertionDefect:
      discard tUndefined({UbKind(ubTailUnverified)})
    expect AssertionDefect:
      discard tUndefined({UbKind(ubIndeterminateRead), UbKind(ubTailUnverified)})
    check UbKind(ubTailUnverified) notin tUndefined().ubKinds
    check UbKind(ubIndeterminateRead) in tUndefined().ubKinds
