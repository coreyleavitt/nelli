## RFC-0016 PRC-47 -- types with a user `=dup`, declared in a module of
## their own (`tests/tsymex_0016_prc47_dupclose.nim` imports it).
type MObj* = object
  v*: int
proc `=dup`*(x: MObj): MObj = MObj(v: x.v + 1)
type MBox* = object
  o*: MObj
type
  MEarly* = object
    o*: MLate
  MLate* = object
    v*: int
proc `=dup`*(x: MLate): MLate = MLate(v: x.v + 1)
