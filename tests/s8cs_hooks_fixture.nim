## RFC-0005 S8cs: types whose lifetime hooks are not exported. A hook binds to its
## type all the same, and a macro in an importing module cannot name it. Imported
## by `tsymex_rfc0005_s8cs_routes2`.
var gM*: int
type
  PrivD* = object
    v*: int
  PrivC* = object
    v*: int
  PrivS* = object
    v*: int
  PrivU* = object
    v*: int
  PrivW* = object
    v*: int
  PrivT* = object
    v*: int
  Hid = object
    v: int
  Shown* = object
    h: Hid
  PlainB* = object
    v*: int
  WithSeq* = object
    s*: seq[int]
proc `=destroy`(d: PrivD) = gM = gM + 1
proc `=copy`(a: var PrivC; b: PrivC) =
  a.v = b.v
  gM = gM + 1
proc `=sink`(a: var PrivS; b: PrivS) =
  a.v = b.v
  gM = gM + 1
proc `=dup`(a: PrivU): PrivU =
  result.v = a.v
  gM = gM + 1
proc `=wasMoved`(a: var PrivW) = gM = gM + 1
proc `=trace`(a: var PrivT; env: pointer) = gM = gM + 1
proc `=destroy`(d: Hid) = gM = gM + 1
proc mkShown*(k: int): Shown = Shown(h: Hid(v: k))
proc mkPrivD*(k: int): PrivD = PrivD(v: k)
proc mkPrivS*(k: int): PrivS = PrivS(v: k)
proc useS*(x: PrivS): int = x.v
proc eatU*(x: sink PrivU) = discard x.v
