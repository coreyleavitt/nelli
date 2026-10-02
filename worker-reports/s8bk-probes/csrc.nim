type Box = ref object
  x: int
var gP = Box(x: 10)
proc moveP(): int {.noinline.} =
  gP = Box(x: 100)
  0
proc touch(v: var int; k: int) {.noinline.} = v = v + 5 + k
var a = [10, 20, 30]
var gi = 0
proc incI(): int {.noinline.} =
  inc gi
  0
proc main() =
  touch(gP.x, moveP())
  touch(a[gi], incI())
main()
