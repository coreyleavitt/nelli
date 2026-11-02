# Pure-Nim probe: a destructor with a try/except, run on the raise path of a
# call's result temporary, on the C backend (goto exceptions).
type Obj = object
  p: int

var destroyed = 0
proc mayRaise(x: int) {.raises: [ValueError].} =
  if x == 999: raise newException(ValueError, "x")

proc `=destroy`(o: Obj) {.raises: [].} =
  try:
    mayRaise(o.p)
    inc destroyed
  except CatchableError:
    discard

proc f(n: int): seq[Obj] =
  result = @[Obj(p: n)]
  if n > 0: raise newException(IOError, "boom")

proc g(n: int): seq[Obj] =
  result = @[Obj(p: 1)]
  result = f(n)          # reassignment from a call

proc h(n: int): int =
  let s = g(n)
  s.len

try:
  echo "returned normally: ", h(1), " (LOST)"
except IOError:
  echo "caught IOError (OK)"
