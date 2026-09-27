## RFC-0005 S8e helper module (not a test file): SUTs whose witness types
## the caller cannot name. The test file imports ONLY the SUT procs, so none
## of the user types below is in its scope, and it imports neither
## `std/tables` nor `std/sets`. The witness emitter builds each witness value
## in the CALLER's scope, so it must name every type by its symbol: an
## emitter that spells `Table`, `HashSet`, `Color`, `OrderedTable` or an
## enum member by name either fails to compile there or binds the name to
## whatever the caller's scope happens to hold under that spelling.
import std/[tables, sets]
from nelli/engine/markers import symexTarget

type
  OrderedTable* = object
    ## A NON-generic user type named like `std/tables.OrderedTable`. In a
    ## caller that imports `std/tables`, the bare name is the stdlib generic.
    a*: int
  Color* = enum
    cRed, cGreen, cBlue
  Meters* = distinct int
  ShapeKind* = enum
    skCircle, skSquare
  Shape* = object
    case kind*: ShapeKind
    of skCircle: r*: int
    of skSquare: side*: int
  TriKind* = enum
    tkA, tkB, tkC
  Tri* = object
    ## A variant with an `else` arm: the emitter renders one branch per
    ## else-covered member.
    case tk*: TriKind
    of tkA: av*: int
    else: rest*: int
  Holder* = object
    ## A plain object whose fields are user types.
    c*: Color
    m*: Meters
  AxKind* = enum
    axP, axQ
  AyKind* = enum
    ayR, ayS
  Dual* = object
    ## Two discriminator axes: the multi-variant emitter.
    case ax*: AxKind
    of axP: pv*: int
    of axQ: discard
    case ay*: AyKind
    of ayR: discard
    of ayS: sv*: int
  Node* = ref object
    ## A named ref object with a recursive field.
    v*: int
    next*: Node
  Plain* = object
    ## Reached through `ref Plain`: the witness allocates a `ref` cell of it.
    w*: int

proc s8eSeq*(s: seq[int]) =
  if s.len == 2 and s[0] == 5:
    symexTarget("s8e_w_seq")

proc s8eTable*(t: Table[string, int]) =
  if t.hasKey("a") and t["a"] == 3:
    symexTarget("s8e_w_table")

proc s8eSet*(s: HashSet[int]) =
  if 4 in s:
    symexTarget("s8e_w_set")

proc s8eOrdered*(o: OrderedTable) =
  if o.a == 7:
    symexTarget("s8e_w_ordered")

proc s8eEnum*(c: Color) =
  if c == cBlue:
    symexTarget("s8e_w_enum")

proc s8eDistinct*(m: Meters) =
  if int(m) == 9:
    symexTarget("s8e_w_distinct")

proc s8eVariant*(s: Shape) =
  if s.kind == skSquare and s.side == 4:
    symexTarget("s8e_w_variant")

proc s8eVariantElse*(t: Tri) =
  if t.tk == tkC and t.rest == 6:
    symexTarget("s8e_w_variant_else")

proc s8eHolder*(h: Holder) =
  if h.c == cGreen and int(h.m) == 3:
    symexTarget("s8e_w_holder")

proc s8eDual*(d: Dual) =
  if d.ax == axP and d.pv == 2 and d.ay == ayS and d.sv == 8:
    symexTarget("s8e_w_dual")

proc s8eNode*(n: Node) =
  if n != nil and n.v == 2:
    symexTarget("s8e_w_node")

proc s8eRefPlain*(p: ref Plain) =
  if p != nil and p.w == 6:
    symexTarget("s8e_w_refplain")

proc s8eSeqNode*(s: seq[Node]) =
  if s.len == 2:
    symexTarget("s8e_w_seqnode")

proc s8eSeqRefPlain*(s: seq[ref Plain]) =
  if s.len == 3:
    symexTarget("s8e_w_seqrefplain")
