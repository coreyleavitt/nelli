# RFC-0005 S8bk native probe: when does Nim take a var/addr actual's address
# relative to a later argument's call?
type Box = ref object
  x: int
type Outer = ref object
  inner: Box

var gP = Box(x: 10)
proc moveP(): int =
  gP = Box(x: 100)
  0
proc touch(v: var int; k: int) = v = v + 5 + k
proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k

block:
  let old = gP
  touch(gP.x, moveP())
  echo "var field: old.x=", old.x, " gP.x=", gP.x

block:
  gP = Box(x: 10)
  let old = gP
  touchP(addr gP.x, moveP())
  echo "addr field: old.x=", old.x, " gP.x=", gP.x

var a = [10, 20, 30]
var gi = 0
proc incI(): int =
  inc gi
  0
block:
  gi = 0
  touch(a[gi], incI())
  echo "index: a=", a, " gi=", gi

var gs = @[10, 20, 30]
block:
  gi = 0
  touch(gs[gi], incI())
  echo "seq index: gs=", gs, " gi=", gi

var gO = Outer(inner: Box(x: 10))
proc moveInner(): int =
  gO.inner = Box(x: 100)
  0
block:
  let old = gO.inner
  touch(gO.inner.x, moveInner())
  echo "field-of-field: old.x=", old.x, " gO.inner.x=", gO.inner.x

proc fwd(v: var int) = touch(v, moveP())
block:
  gP = Box(x: 10)
  let old = gP
  fwd(gP.x)
  echo "forward: old.x=", old.x, " gP.x=", gP.x

proc writeOld(): int =
  # writes the old object before rebinding
  gP.x = 50
  gP = Box(x: 100)
  0
block:
  gP = Box(x: 10)
  let old = gP
  touch(gP.x, writeOld())
  echo "copy-in: old.x=", old.x, " gP.x=", gP.x

var gx = 10
proc setX(): int =
  gx = 70
  0
block:
  touch(gx, setX())
  echo "plain var: gx=", gx

# index out of bounds after the later call
block:
  gi = 2
  proc incI2(): int =
    gi = 3
    0
  try:
    touch(a[gi], incI2())
    echo "oob-after: no raise a=", a
  except IndexDefect:
    echo "oob-after: IndexDefect"

let f = touch
block:
  gP = Box(x: 10)
  let old = gP
  f(gP.x, moveP())
  echo "proc var: old.x=", old.x, " gP.x=", gP.x
