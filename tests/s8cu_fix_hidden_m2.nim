## RFC-0005 S8cu fixture: compiled first by `s8cu_fix_hidden_m1`'s import, under
## its push. Its own text has no pragma.
import nelli
type LK* = enum lkA, lkB
type LP* = object
  case k*: LK
  of lkA: x*: int
  of lkB: y*: int
type LPar* = ref object of RootObj
  a*: int
type LCh* = ref object of LPar
  b*: int

proc impField*(v: int) =
  var o = LP(k: lkA, x: v)
  o.y = v
  symexTarget("hit")
proc impRange*(v: int) =
  if v == 300:
    let w = int8(v)
    if w == 44'i8: symexTarget("hit")
proc impObj*(v: int) =
  let p = LPar(a: v)
  let c = LCh(p)
  if c.a == v: symexTarget("hit")
