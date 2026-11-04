## RFC-0005 S8ct. The state a re-executed replay child (`replayproc.nim`) is
## handed: the witness, and the variables the SUT may reach. A plain binary
## encoding of Nim values, inside one program: both ends are the same binary, so
## it carries no type information and has no compatibility to keep.
##
## What cannot cross a process raises `WireError` at the host's end and the
## replay declines: a non-nil `ptr`, `pointer`, proc value or `cstring`. A `ref`
## crosses with its identity kept (two references to one cell are one cell in
## the child, and a cycle closes), so that a graph of them means what it did.
##
## `isWireableType` is the compile-time half: a type that cannot be encoded
## whatever its value holds (an imported C struct, whose fields Nim does not
## know; a `ref` to an inheritable object, whose dynamic type the encoding does
## not carry; a case object).

import std/[macros, tables]
import std/typetraits

type
  WireError* = object of CatchableError
  WireWriter* = object
    data*: string
    cells: Table[pointer, int]
  WireReader* = object
    data*: string
    pos: int
    cells: seq[pointer]

proc initWireReader*(data: string): WireReader =
  WireReader(data: data)

proc putRaw(w: var WireWriter; p: pointer; n: int) =
  if n > 0:
    let at = w.data.len
    w.data.setLen(at + n)
    copyMem(addr w.data[at], p, n)

proc getRaw(r: var WireReader; p: pointer; n: int) =
  if n > 0:
    if n > r.data.len - r.pos:
      raise newException(WireError, "the replay's witness is truncated")
    copyMem(p, addr r.data[r.pos], n)
    r.pos += n

proc wirePut*[T](w: var WireWriter; x: T)
proc wireGet*[T](r: var WireReader; x: var T)

proc putLen(w: var WireWriter; n: int) =
  var v = int64(n)
  w.putRaw(addr v, 8)

proc getLen(r: var WireReader): int =
  var v: int64
  r.getRaw(addr v, 8)
  int(v)

proc getCount(r: var WireReader): int =
  ## A string's or seq's length (RFC-0005 0.9.1, review R1-20): never
  ## negative, and never more than the bytes left, which each element takes
  ## at least one of but for an empty one. A witness that says otherwise is
  ## not one the host wrote.
  result = r.getLen()
  if result < 0 or result > r.data.len - r.pos:
    raise newException(WireError, "the replay's witness is malformed")

proc wirePut*[T](w: var WireWriter; x: T) =
  when T is distinct:
    w.wirePut(distinctBase(T)(x))
  elif T is (SomeNumber | bool | char | enum | set | range):
    var v = x
    w.putRaw(addr v, sizeof(T))
  elif T is string:
    w.putLen(x.len)
    if x.len > 0: w.putRaw(unsafeAddr x[0], x.len)
  elif T is seq:
    w.putLen(x.len)
    for e in x: w.wirePut(e)
  elif T is array:
    for e in x: w.wirePut(e)
  elif T is ref:
    if x == nil:
      w.putLen(-1)
    else:
      let key = cast[pointer](x)
      if key in w.cells:
        w.putLen(w.cells[key])
      else:
        let id = w.cells.len
        w.cells[key] = id
        w.putLen(id)
        w.wirePut(x[])
  elif T is (tuple | object):
    for _, v in fieldPairs(x):
      w.wirePut(v)
  elif T is (ptr | pointer | cstring) or (T is proc):
    if not x.isNil:
      raise newException(WireError, "a live pointer or proc value")
  else:
    raise newException(WireError, "a value of an unmarshallable type")

proc wireGet*[T](r: var WireReader; x: var T) =
  when T is distinct:
    var b: distinctBase(T)
    r.wireGet(b)
    x = T(b)
  elif T is (SomeNumber | bool | char | enum | set | range):
    r.getRaw(addr x, sizeof(T))
  elif T is string:
    let n = r.getCount()
    x = newString(n)
    if n > 0: r.getRaw(addr x[0], n)
  elif T is seq:
    let n = r.getCount()
    x.setLen(n)
    for i in 0 ..< n: r.wireGet(x[i])
  elif T is array:
    for i in low(x) .. high(x): r.wireGet(x[i])
  elif T is ref:
    let id = r.getLen()
    if id < 0:
      x = nil
    elif id < r.cells.len:
      x = cast[T](r.cells[id])
    else:
      new(x)
      GC_ref(x)       # the graph may hold it only through a later cycle
      r.cells.add cast[pointer](x)
      r.wireGet(x[])
  elif T is (tuple | object):
    for _, v in fieldPairs(x):
      r.wireGet(v)
  elif T is (ptr | pointer | cstring) or (T is proc):
    x = nil
  else:
    raise newException(WireError, "a value of an unmarshallable type")

proc wireableRef(t: NimNode; seen: var seq[NimNode]): bool

proc wireableImpl(t: NimNode; seen: var seq[NimNode]): bool =
  case t.kind
  of nnkSym:
    for s in seen:
      if s == t: return true
    let k = t.typeKind
    case k
    of ntyBool, ntyChar, ntyEnum, ntyInt, ntyInt8, ntyInt16, ntyInt32, ntyInt64,
       ntyUInt, ntyUInt8, ntyUInt16, ntyUInt32, ntyUInt64, ntyFloat, ntyFloat32,
       ntyFloat64, ntyString, ntyCstring, ntyPointer:
      return true
    else:
      discard
    # A type imported from C (`SysLockObj` is `pthread_mutex_t`): its Nim
    # fields are a stand-in for the C layout, not the C layout.
    let def = t.getImpl
    if def.kind == nnkTypeDef and def[0].kind == nnkPragmaExpr:
      for p in def[0][1]:
        let name = (if p.kind in {nnkExprColonExpr, nnkCall}: p[0] else: p)
        if name.kind in {nnkIdent, nnkSym} and
           name.strVal in ["importc", "importcpp", "importjs", "importobjc",
                           "incompleteStruct"]:
          return false
    seen.add t
    # An alias (`Lock = SysLock = SysLockObj`): the named type, so its pragmas
    # are read, not the object it ends at.
    if def.kind == nnkTypeDef and def[2].kind == nnkSym and def[2] != t:
      return wireableImpl(def[2], seen)
    wireableImpl(t.getTypeImpl, seen)
  of nnkBracketExpr:
    case t[0].strVal
    of "seq", "array", "set", "range", "sink", "lent", "typeDesc":
      for i in 1 ..< t.len:
        if t[i].kind in {nnkSym, nnkBracketExpr, nnkTupleTy, nnkTupleConstr,
                         nnkRefTy, nnkPtrTy, nnkObjectTy} and
           not wireableImpl(t[i], seen):
          return false
      true
    of "ref":
      wireableRef(t[1], seen)
    of "ptr":
      true
    else:
      # An instance of a generic object: its fields, with its arguments bound.
      # A recursive instance (`next: Node[T]`) is met again on the way down;
      # an instance whose implementation is itself again makes no progress.
      for s in seen:
        if s.kind == nnkBracketExpr and s.repr == t.repr: return true
      let impl = t.getTypeImpl
      if impl.kind == nnkBracketExpr and impl.repr == t.repr: return false
      seen.add t
      wireableImpl(impl, seen)
  of nnkRefTy:
    wireableRef(t[0], seen)
  of nnkPtrTy, nnkProcTy, nnkEnumTy, nnkDistinctTy:
    if t.kind == nnkDistinctTy: wireableImpl(t[0], seen) else: true
  of nnkTupleTy, nnkTupleConstr:
    for d in t:
      var ty = d
      if d.kind == nnkIdentDefs: ty = d[^2]
      elif d.kind == nnkExprColonExpr: ty = d[1]
      if not wireableImpl(ty, seen): return false
    true
  of nnkObjectTy:
    if t.len > 0 and t[0].kind == nnkPragma: return false
    if t.len > 1 and t[1].kind == nnkOfInherit: return false
    if t.len > 2 and t[2].kind == nnkRecList:
      for d in t[2]:
        case d.kind
        of nnkIdentDefs:
          if not wireableImpl(d[^2], seen): return false
        of nnkEmpty, nnkNilLit:
          discard
        else:
          return false    # a case object, or a `when` in it
    true
  else:
    false

proc wireableRef(t: NimNode; seen: var seq[NimNode]): bool =
  ## A `ref`'s pointee: not inheritable, as its dynamic type would be lost.
  wireableImpl(t, seen)

proc isWireableType*(t: NimNode): bool =
  ## RFC-0005 S8ct. `t` (a `getTypeInst`) can be marshalled, values permitting.
  var seen: seq[NimNode]
  wireableImpl(t, seen)
