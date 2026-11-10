## RFC-0005 S8ct. The state a re-executed replay child (`replayproc.nim`) is
## handed: the witness, and the variables the SUT may reach. A plain binary
## encoding of Nim values, inside one program: both ends are the same binary, so
## it carries no type information and has no compatibility to keep.
##
## What cannot cross a process raises `WireError` at the host's end and the
## replay declines: a non-nil `ptr`, `pointer` or `cstring`, a closure with a
## captured environment other than its bytes alone (RFC-0016 W3-z R10), and a
## proc value naming no routine of `procs`. A `ref`
## crosses with its identity kept (two references to one cell are one cell in
## the child, and a cycle closes), so that a graph of them means what it did.
##
## A proc value crosses by identity (RFC-0016 PRC-02): an address differs
## between two processes of one binary (ASLR), but the child is the same
## binary, so both ends are given the same `procs`, a table of the routines the
## replayed code names, in one order. A proc value is written as its index, and
## read as the routine at that index. Those routines are the ones the footprint
## scan has read, so what a proc value runs is code whose state the child was
## handed.
##
## `isWireableType` is the compile-time half: a type that cannot be encoded
## whatever its value holds (an imported C struct, whose fields Nim does not
## know; a `ref` to an inheritable object, whose dynamic type the encoding does
## not carry). A case object crosses: the discriminator, then the active
## branch (RFC-0016 PRC-01).

import std/[macros, tables]
import std/typetraits

type
  WireError* = object of CatchableError
  EnvPut* = proc (w: var WireWriter; env: pointer) {.nimcall.}
    ## RFC-0016 W3-z R11. Writes the one value a closure environment holds.
  EnvGet* = proc (r: var WireReader; env: pointer) {.nimcall.}
    ## RFC-0016 W3-z R11. Reads it into the child's environment.
  WireWriter* = object
    data*: string
    cells: Table[pointer, int]
    procs*: seq[pointer]
    envOk*: seq[bool]
      ## RFC-0016 W3-z R10. Per slot of `procs`: a closure of that routine
      ## may carry its environment (its captured values are their bytes
      ## alone; `symex.nim`'s `envPlainWhy`). Missing: it may not.
    envBenign*: seq[bool]
      ## RFC-0016 W3-z R11. Per slot of `procs`: a closure of that routine
      ## carries an environment whose destructor, if any, is the compiler's
      ## and runs no user code (`dsl_parser.envBenignExpr`): it holds strings,
      ## seqs and objects of plain values. Missing: it does not.
    envPut*: seq[EnvPut]
      ## RFC-0016 W3-z R11. Per slot of `envBenign`: the writer of the one
      ## value the environment holds, or nil when it holds more than one (the
      ## order of an environment's fields is the compiler's).
    scratch*: bool
      ## RFC-0016 W3-z R11. The settle's check that every proc value names a
      ## routine of the table (`symex.emitProcValueLift`): nothing is handed
      ## to a child, so an `envBenign` environment is not written.
  WireReader* = object
    data*: string
    pos: int
    cells: seq[pointer]
    procs*: seq[pointer]
    envGet*: seq[EnvGet]
      ## RFC-0016 W3-z R11. Per slot of `procs`, `WireWriter.envPut`'s reader.

proc initWireReader*(data: string; procs: seq[pointer] = @[]): WireReader =
  WireReader(data: data, procs: procs)

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

proc envRefusal*(env: pointer): string =
  ## RFC-0016 W3-z R10. Empty when a closure environment `env` can be copied
  ## by its bytes: its type runs no destructor, so it holds no reference, no
  ## string or seq buffer and no lifetime hook (ARC/ORC: the environment's
  ## first field is its type's `TNimTypeV2`, whose first field is the
  ## destructor and second the size). What the bytes hold beyond that was
  ## checked when the slot was allowed an environment (`WireWriter.envOk`).
  when defined(gcArc) or defined(gcOrc) or defined(gcAtomicArc):
    let rti = cast[ptr pointer](env)[]
    if rti == nil:
      return "a closure whose environment has no type header"
    let f = cast[ptr UncheckedArray[int]](rti)
    if f[0] != 0:
      return "a closure whose captured environment runs a destructor"
    if f[1] < sizeof(pointer):
      return "a closure whose environment's type gives no size"
    ""
  else:
    "a closure with a captured environment, whose type this memory manager " &
      "does not describe"

proc envTypedRefusal*(env: pointer): string =
  ## RFC-0016 W3-z R11. Empty when a closure environment `env` names its type
  ## (ARC/ORC's `TNimTypeV2`, with a size), whatever its destructor.
  when defined(gcArc) or defined(gcOrc) or defined(gcAtomicArc):
    let rti = cast[ptr pointer](env)[]
    if rti == nil:
      return "a closure whose environment has no type header"
    if cast[ptr UncheckedArray[int]](rti)[1] < sizeof(pointer):
      return "a closure whose environment's type gives no size"
    ""
  else:
    "a closure with a captured environment, whose type this memory manager " &
      "does not describe"

proc envField*(env: pointer; offset, size: int): pointer =
  ## RFC-0016 W3-z R11. The address of the one value an environment holds, at
  ## `offset` of an object of `size` bytes: its type header, then the value
  ## (the mirror the generated codec lays out). An environment whose type
  ## gives another size is not the one the codec was made for.
  let rti = cast[ptr pointer](env)[]
  if rti == nil or cast[ptr UncheckedArray[int]](rti)[1] != size:
    raise newException(WireError, "a closure environment whose type is not " &
                       "the one its routine's capture describes")
  cast[pointer](cast[uint](env) + uint(offset))

proc putEnv(w: var WireWriter; code, env: pointer; put: EnvPut = nil) =
  ## RFC-0016 W3-z R10. A closure's environment, by its bytes (`envRefusal`),
  ## with the host's addresses of its routine, of its type and of the type's
  ## destructor, from which the child finds its own type (`getEnv`).
  ## RFC-0016 W3-z R11: an environment with a destructor is written by `put`,
  ## the codec of the one value it holds, never by its bytes (a buffer is an
  ## address in the host).
  let rti = cast[ptr pointer](env)[]
  let f = cast[ptr UncheckedArray[int]](rti)
  let size = f[1]
  w.putLen(size)
  var c = cast[int64](code)
  var t = cast[int64](rti)
  var d = cast[int64](f[0])
  w.putRaw(addr c, 8)
  w.putRaw(addr t, 8)
  w.putRaw(addr d, 8)
  if d == 0:
    w.putRaw(cast[pointer](cast[uint](env) + uint(sizeof(pointer))),
             size - sizeof(pointer))
  else:
    put(w, env)

proc getEnv(r: var WireReader; code: pointer; at: int): pointer =
  ## RFC-0016 W3-z R10. The child's copy of a closure environment `putEnv`
  ## wrote, or nil. The child is the same binary, loaded elsewhere: the
  ## environment's type lies where the host's did, moved as the routine
  ## moved (one image, one load offset), and must say what the host's said
  ## (the same size, and a destructor moved the same way, or none), or the
  ## witness is not the host's. RFC-0016 W3-z R11: an environment with a
  ## destructor is filled by the slot's codec (`envGet`) in a zeroed object
  ## of the child's type.
  let size = r.getLen()
  if size < 0: return nil
  if size < sizeof(pointer) or size - sizeof(pointer) > r.data.len - r.pos:
    raise newException(WireError, "the replay's witness is malformed")
  var hc, ht, hd: int64
  r.getRaw(addr hc, 8)
  r.getRaw(addr ht, 8)
  r.getRaw(addr hd, 8)
  let delta = cast[uint](code) - cast[uint](hc)
  let rti = cast[pointer](cast[uint](ht) + delta)
  let f = cast[ptr UncheckedArray[int]](rti)
  let dtor = if hd == 0: 0 else: cast[int](cast[uint](hd) + delta)
  if f[0] != dtor or f[1] != size:
    raise newException(WireError, "a closure environment whose type the " &
                       "child does not find where the host's was")
  if dtor != 0 and (at >= r.envGet.len or r.envGet[at] == nil):
    raise newException(WireError, "the replay's witness is malformed")
  var e: ref RootObj
  unsafeNew(e, size)
  let p = cast[pointer](e)
  cast[ptr pointer](p)[] = rti
  if dtor == 0:
    r.getRaw(cast[pointer](cast[uint](p) + uint(sizeof(pointer))),
             size - sizeof(pointer))
  else:
    r.envGet[at](r, p)
  GC_ref(e)
  p

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
  elif T is ptr:
    # RFC-0016 PRC-01. What a non-nil `ptr` addresses is unknown memory (a
    # variable, a field of another object, a C allocation): the child cannot
    # be given that address, and a fresh cell would silently drop the aliasing.
    # A `ptr` the solver's model puts in a witness is rebuilt by the child from
    # the model (`ChildWitness`), not carried here.
    if not x.isNil:
      raise newException(WireError, "a non-nil `ptr`, whose target the child cannot be given")
  elif T is (pointer | cstring):
    if not x.isNil:
      raise newException(WireError, "a non-nil `" & (when T is pointer: "pointer" else: "cstring") & "`, whose target the child cannot be given")
  elif (T is proc):
    # RFC-0016 PRC-02. By identity: the index of the routine in `procs`. A
    # closure type is a code pointer and an environment; one with an
    # environment holds the host's heap, which has no routine to name.
    # RFC-0016 W3-z R10: one with an environment crosses when its routine is
    # a slot allowed one (`envOk`) and the environment is its bytes alone
    # (`envRefusal`); the child rebuilds it (`getEnv`).
    if x.isNil:
      w.putLen(-1)
    else:
      when sizeof(T) > sizeof(pointer):
        let env = rawEnv(x)
        let code = rawProc(x)
      else:
        let env: pointer = nil
        let code = cast[pointer](x)
      var at = -1
      for i, p in w.procs:
        if p == code:
          at = i
          break
      # RFC-0016 W3-z R11: an environment whose destructor runs no user code
      # (`envBenign`) is named by the settle's scratch wire (a forked child
      # copies it) and written by its one value's codec (`envPut`) to a
      # re-executed child.
      var put: EnvPut = nil
      var skip = false
      if env != nil:
        if at < 0:
          raise newException(WireError, "a closure with a captured environment, whose routine the replayed code does not name (or names only inside a routine, where its address cannot be taken), which the child cannot be given")
        let plain = at < w.envOk.len and w.envOk[at]
        let benign = at < w.envBenign.len and w.envBenign[at]
        let why = envRefusal(env)
        if plain and why.len == 0:
          discard
        elif benign:
          let typed = envTypedRefusal(env)
          if typed.len > 0:
            raise newException(WireError, typed & ", which the child cannot be given")
          if w.scratch:
            skip = true
          elif at < w.envPut.len and w.envPut[at] != nil:
            put = w.envPut[at]
          else:
            raise newException(WireError, "a closure whose captured environment holds more than one value, a string or seq among them: the child rebuilds such an environment value by value, and the order of its values is the compiler's, which the child cannot be given")
        elif not plain:
          raise newException(WireError, "a closure with a captured environment holding a value that is not its bytes alone (an address, a buffer or a type header), which the child cannot be given")
        else:
          raise newException(WireError, why & ", which the child cannot be given")
      if at < 0:
        raise newException(WireError, "a proc value naming no routine the replayed code names, so the child could not run it")
      w.putLen(at)
      when sizeof(T) > sizeof(pointer):
        if env == nil or skip: w.putLen(-1)
        else: w.putEnv(code, env, put)
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
  elif T is object:
    # RFC-0016 PRC-01. A case object: `fieldPairs` yields the discriminator and
    # then the fields of the branch it selects, so the writer's order (the
    # discriminator first, then the active branch) is read back by assigning
    # the discriminator before the branch is visited. `reset` first: the target
    # may hold another branch (a global), whose fields the assignment would
    # otherwise leave unreleased.
    reset(x)
    {.cast(uncheckedAssign).}:
      for _, v in fieldPairs(x):
        r.wireGet(v)
  elif T is tuple:
    for _, v in fieldPairs(x):
      r.wireGet(v)
  elif T is (ptr | pointer | cstring):
    x = nil
  elif (T is proc):
    let at = r.getLen()
    if at < 0:
      x = nil
    elif at < r.procs.len:
      when sizeof(T) > sizeof(pointer):
        # A code pointer and its environment (RFC-0016 W3-z R10), or none.
        var c: array[2, pointer]
        c[0] = r.procs[at]
        if c[0] == nil:
          raise newException(WireError, "the replay's witness is malformed")
        c[1] = r.getEnv(c[0], at)
        copyMem(addr x, addr c[0], sizeof(T))
      else:
        x = cast[T](r.procs[at])
    else:
      raise newException(WireError, "the replay's witness is malformed")
  else:
    raise newException(WireError, "a value of an unmarshallable type")

proc wireableRef(t: NimNode; seen: var seq[NimNode]): bool
proc wireableCase(c: NimNode; seen: var seq[NimNode]): bool

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
        of nnkRecCase:
          if not wireableCase(d, seen): return false
        else:  # k2: fail-closed: false: not wireable, no wire replay
          return false    # a `when` in it
    true
  else:  # k2: fail-closed: false: not wireable, no wire replay
    false

proc wireableRecList(l: NimNode; seen: var seq[NimNode]): bool =
  case l.kind
  of nnkRecList:
    for d in l:
      if not wireableRecList(d, seen): return false
    true
  of nnkIdentDefs:
    wireableImpl(l[^2], seen)
  of nnkRecCase:
    wireableCase(l, seen)
  of nnkEmpty, nnkNilLit:
    true
  else:  # k2: fail-closed: false: not wireable, no wire replay
    false     # a `when` in it

proc wireableCase(c: NimNode; seen: var seq[NimNode]): bool =
  ## RFC-0016 PRC-01. A case object's discriminator, then every branch.
  if not wireableImpl(c[0][^2], seen): return false
  for i in 1 ..< c.len:
    let b = c[i]
    if not wireableRecList(b[^1], seen): return false
  true

proc wireableRef(t: NimNode; seen: var seq[NimNode]): bool =
  ## A `ref`'s pointee: not inheritable, as its dynamic type would be lost.
  wireableImpl(t, seen)

proc isWireableType*(t: NimNode): bool =
  ## RFC-0005 S8ct. `t` (a `getTypeInst`) can be marshalled, values permitting.
  var seen: seq[NimNode]
  wireableImpl(t, seen)
