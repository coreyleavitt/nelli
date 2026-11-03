## RFC-0005 S8cu. One routine per check, for the command-line suites. Each raises
## under its check, and reaches `hit` without it.
import nelli/symex

type K* = enum kA, kB, kC, kD
type P* = object
  case k*: K
  of kA, kB: x*: int
  of kC: y*: int
  else: discard
type Par* = ref object of RootObj
  a*: int
type Ch* = ref object of Par
  b*: int

proc clField*(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("hit")

proc clOver*(v: int) =
  if v == high(int):
    let w = v + 1
    if w < 0: symexTarget("hit")

proc clRange*(v: int) =
  if v == 300:
    let w = int8(v)
    if w == 44'i8: symexTarget("hit")

proc clBound*(v: int) =
  var a = [1, 2, 3]
  if v == 3:
    discard a[v]
    symexTarget("hit")

proc clObj*(v: int) =
  let p = Par(a: v)
  let c = Ch(p)
  if c.a == v: symexTarget("hit")

proc clPure*(v: int) =
  ## Guards nothing a check covers, and walks no other routine.
  if v == 7: symexTarget("hit")

proc clFloat*(a: float) =
  if a == 1e308 and a * 10.0 > a: symexTarget("hit")

{.push fieldChecks: on.}
proc clFieldOn*(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("hit")
{.pop.}

{.push overflowChecks: on.}
proc clOverOn*(v: int) =
  if v == high(int):
    let w = v + 1
    if w < 0: symexTarget("hit")
{.pop.}

{.push checks: on.}
proc clAllOn*(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
  symexTarget("hit")
{.pop.}
