## RFC-0016 K2c: the fixtures the K2c child-shape corpus parts share
## (`tsymex_0016_k2c_typeclass_{a,b,c}`): the parameter types the snippets
## name and their `$`. Each part keeps its own snippet procs and globals.

type
  E* = enum ea, eb, ec
  Obj* = object
    a*: int
    b*: bool
  Dist* = distinct int
  RefO* = ref object
    v*: int
  Box*[T] = object
    v*: T
  Al* = int

proc `$`*(d: Dist): string = $int(d)
proc `$`*(p: ptr int): string = (if p == nil: "nil" else: "ptr " & $p[])
proc `$`*(r: RefO): string = (if r == nil: "nil" else: $r.v)
