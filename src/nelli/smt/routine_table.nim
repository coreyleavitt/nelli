## nelli/smt/routine_table -- the routine table a replay child carries: which
## routines a witness's footprint reaches, how their captured environments are
## wired across the process boundary (`EnvPut`/`EnvGet`), and the emitted
## table itself (`emitRoutineTable`).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged.

import std/[macros, sets, tables]
import ./dsl
import ./replay_footprint
import ./replaywire
import ./replayproc

proc plainBitsType(t: NimNode; depth = 0): bool =
  ## RFC-0016 W3-z R10. A value of type `t` is its bytes alone: no address
  ## (`ref`, `ptr`, `pointer`, `cstring`, a proc value, a string's or seq's
  ## buffer) and no type header (an inheritable object's), so a copy of the
  ## bytes into another process of the same binary is the same value.
  if depth > 24: return false
  case t.kind
  of nnkSym:
    case t.typeKind
    of ntyBool, ntyChar, ntyEnum, ntyInt, ntyInt8, ntyInt16, ntyInt32,
       ntyInt64, ntyUInt, ntyUInt8, ntyUInt16, ntyUInt32, ntyUInt64,
       ntyFloat, ntyFloat32, ntyFloat64, ntySet, ntyRange:
      true
    of ntyDistinct, ntyObject, ntyTuple, ntyArray, ntyGenericInst, ntyAlias:
      let impl = t.getTypeImpl
      impl != t and plainBitsType(impl, depth + 1)
    else: false
  of nnkObjectTy:
    # An inheritable object starts with its type's header, an address.
    if t.len > 1 and t[1].kind != nnkEmpty: return false
    if t.len > 0 and t[0].kind == nnkPragma: return false
    t.len > 2 and plainBitsType(t[2], depth + 1)
  of nnkRecList, nnkTupleTy, nnkTupleConstr:
    for c in t:
      if not plainBitsType(c, depth + 1): return false
    true
  of nnkIdentDefs:
    t.len >= 2 and plainBitsType(t[^2], depth + 1)
  of nnkDistinctTy:
    t.len > 0 and plainBitsType(t[0], depth + 1)
  of nnkEnumTy: true
  of nnkBracketExpr:
    if t.len == 0 or t[0].kind notin {nnkSym, nnkIdent}: return false
    case t[0].strVal
    of "set", "range": true
    of "array": t.len == 3 and plainBitsType(t[2], depth + 1)
    else:
      let impl = t.getTypeImpl
      impl != t and plainBitsType(impl, depth + 1)
  else: false  # k2: fail-closed: false: not plain bits, so the env is refused and the replay declines

proc envPlainWhy(r: NimNode): string =
  ## RFC-0016 W3-z R10. Empty when a closure of the nested routine `r` carries
  ## an environment whose captured values are their bytes alone
  ## (`plainBitsType`): the environment is the one the routine enclosing `r`
  ## builds, which holds every local of it that any routine nested in it
  ## names. Otherwise why not, naming the value.
  let o = owner(r)
  if o.kind != nnkSym or symKind(o) notin userRoutineSymKinds:
    return "`" & r.strVal & "` is not nested in a routine"
  let impl =
    try: o.getImpl
    except CatchableError: newEmptyNode()
  if impl.kind notin RoutineNodes or impl.len <= 6:
    return "the routine enclosing `" & r.strVal & "` has no body to read"
  var caps: seq[NimNode]
  collectClosureCaptures(impl[6], o, false, caps)
  for c in caps:
    let t =
      try: c.getTypeInst
      except CatchableError: newEmptyNode()
    if t.kind == nnkEmpty or not plainBitsType(t):
      return "its environment captures `" & c.strVal & "`, a value of a " &
             "type that is not its bytes alone (" & t.repr & ")"
  ""

proc envCodecs(r: NimNode): tuple[put, get: NimNode; why: string] =
  ## RFC-0016 W3-z R11. The wire's writer and reader of the environment of a
  ## closure of the nested routine `r` (`replaywire.EnvPut`/`EnvGet`), or nil
  ## literals and why not. The values follow the type header as they follow
  ## a pointer in a mirror object of the two (`envField` checks the
  ## environment's size against the mirror's). The values are of types
  ## `envBenignWhy` admits and the wire carries.
  ## RFC-0016 W3-z R12: two or more captured values of one type. The compiler
  ## orders an environment's fields as lambda lifting meets the captured
  ## locals, after every macro has run, and no type, `getTypeImpl` or
  ## run-time type header (`TNimTypeV2`: a destructor, a size, an alignment,
  ## no field table) says that order. Values of one type need none: every
  ## order lays them out as an array of that type after the header (a C
  ## struct of N members of one type has no padding between them), and the
  ## child, the same binary, has the same layout, so the value at each slot
  ## crosses to the same slot whichever local it is. A captured local whose
  ## `{.align.}` moves its field, or a capture this read miscounts, gives the
  ## environment another size than the mirror's, which `envField` refuses. Values of two or more
  ## types decline, saying so; so does an environment linked to the one of
  ## the routine enclosing its own (`envLinked`: its first field is an
  ## address in the host).
  result = (newNilLit(), newNilLit(), "")
  var nominal, caps: seq[NimNode]
  let benign = envBenignWhy(r, nominal, caps)
  if benign.len > 0:
    result.why = benign
    return
  if envLinked(r):
    result.why = "a closure of a routine nested in a nested one, whose " &
      "environment links to the environment of the routine enclosing it (an " &
      "address in the host), which the child cannot be given"
    return
  if caps.len == 0:
    result.why = "a closure whose environment captures no value this check " &
      "reads, which the child cannot be given"
    return
  let t =
    try: caps[0].getTypeInst
    except CatchableError: newEmptyNode()
  if t.kind == nnkEmpty:
    result.why = "a closure whose captured value's type cannot be read, which " &
      "the child cannot be given"
    return
  for c in caps:
    let ct =
      try: c.getTypeInst
      except CatchableError: newEmptyNode()
    if ct.kind == nnkEmpty or not sameType(ct, t):
      result.why = "a closure whose captured environment holds values of more " &
        "than one type, a string or seq among them: the child rebuilds such " &
        "an environment value by value, and the order of its values is the " &
        "compiler's (lambda lifting lays the fields out after every macro has " &
        "run, and no type or run-time type header names that order), which " &
        "the child cannot be given"
      return
  if not isWireableType(t):
    result.why = "a closure whose environment captures a value of `" & t.repr &
      "`, a type the replay's wire does not carry, which the child cannot " &
      "be given"
    return
  let n = newLit(caps.len)
  # Each lambda its own symbols: a symbol is owned by the routine that
  # declares it, and one shared would be a capture in the other.
  let mirror = genSym(nskType, "EnvMirror")
  let mirrorG = genSym(nskType, "EnvMirror")
  let w = genSym(nskParam, "w")
  let rd = genSym(nskParam, "r")
  let env = genSym(nskParam, "env")
  let envG = genSym(nskParam, "env")
  let putT = bindSym"EnvPut"
  let getT = bindSym"EnvGet"
  result.put = quote do:
    `putT`(proc (`w`: var WireWriter; `env`: pointer) {.nimcall.} =
      type `mirror` = object
        envMirrorHead: pointer
        envMirrorValue: array[`n`, `t`]
      let vals = cast[ptr array[`n`, `t`]](envField(`env`,
        offsetOf(`mirror`, envMirrorValue), sizeof(`mirror`)))
      for i in 0 ..< `n`: wirePut(`w`, vals[i]))
  result.get = quote do:
    `getT`(proc (`rd`: var WireReader; `envG`: pointer) {.nimcall.} =
      type `mirrorG` = object
        envMirrorHead: pointer
        envMirrorValue: array[`n`, `t`]
      let vals = cast[ptr array[`n`, `t`]](envField(`envG`,
        offsetOf(`mirrorG`, envMirrorValue), sizeof(`mirrorG`)))
      for i in 0 ..< `n`: wireGet(`rd`, vals[i]))

type RoutineTable* = object
  ## RFC-0016 PRC-02, W3-z R10/R11. `emitRoutineTable`'s expressions.
  ## W3-z R12: `envWhy`, per slot, why a benign environment has no codec.
  procs*, envOk*, envBenign*, envPut*, envGet*, envWhy*: NimNode

proc emitRoutineTable*(fp: ReplayFootprint): RoutineTable =
  ## RFC-0016 PRC-02, W3-z R10. The routine table a proc value crosses by
  ## (`replaywire.nim`), in one order for both ends: the top-level routines
  ## (`fp.routines`; a slot whose address cannot be taken holds nil), then
  ## the nested ones (`fp.nested`, `nestedRoutineAddrs`). `envOk` is, per
  ## slot, whether a closure of that routine may carry its environment
  ## (`envPlainWhy`): only a nested routine's can. RFC-0016 W3-z R11:
  ## `envBenign`, whether that environment's destructor, if any, runs no user
  ## code (`envBenignExpr`), and `envPut`/`envGet`, its codec (`envCodecs`).
  var items = nnkBracket.newTree()
  var ok = nnkBracket.newTree()
  var benign = nnkBracket.newTree()
  var puts = nnkBracket.newTree()
  var gets = nnkBracket.newTree()
  var whys = nnkBracket.newTree()
  for r in fp.routines:
    items.add quote do:
      (when compiles(cast[pointer](`r`)): cast[pointer](`r`)
       else: pointer(nil))
    ok.add newLit(false)
    benign.add newLit(false)
    puts.add newCall(bindSym"EnvPut", newNilLit())
    gets.add newCall(bindSym"EnvGet", newNilLit())
    whys.add newLit("")
  let probe = genSym(nskVar, "routineTableProbe")
  var nested = newCall(bindSym"nestedRoutineAddrs", probe)
  for r in fp.nested:
    nested.add r
    ok.add newLit(envPlainWhy(r).len == 0)
    benign.add envBenignExpr(r)
    let (p, g, why) = envCodecs(r)
    puts.add(if p.kind == nnkNilLit: newCall(bindSym"EnvPut", p) else: p)
    gets.add(if g.kind == nnkNilLit: newCall(bindSym"EnvGet", g) else: g)
    whys.add newLit(why)
  let top =
    if items.len == 0: quote do: newSeq[pointer]()
    else: quote do: @`items`
  result.procs = quote do:
    (block:
      var `probe` {.used.}: int
      `top` & `nested`)
  result.envOk =
    if ok.len == 0: quote do: newSeq[bool]()
    else: quote do: @`ok`
  result.envBenign =
    if benign.len == 0: quote do: newSeq[bool]()
    else: quote do: @`benign`
  let putT = bindSym"EnvPut"
  let getT = bindSym"EnvGet"
  result.envPut =
    if puts.len == 0: quote do: newSeq[`putT`]()
    else: quote do: @`puts`
  result.envGet =
    if gets.len == 0: quote do: newSeq[`getT`]()
    else: quote do: @`gets`
  result.envWhy =
    if whys.len == 0: quote do: newSeq[string]()
    else: quote do: @`whys`
