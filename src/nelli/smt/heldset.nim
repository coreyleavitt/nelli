## nelli/smt/heldset -- the held-set walk: what a module-level proc-valued
## variable may hold at a call through it, on any run of a routine
## (`heldAtCalls`), and the use check that decides whether the walk may be
## trusted for that variable (`procValueUses`).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. Both entry points are
## compile-time only; the walk's own helpers stay private.

import std/[macros, tables, strutils]
import ./dsl
import ./replay_footprint

proc procValueUses*(n, g: NimNode; assigned: var seq[NimNode]): bool =
  ## RFC-0016 W3-z R7. Every use of the module-level variable `g` in `n` is
  ## one the replay settle understands: a call through it, a comparison of it
  ## (`==`, `!=`, `isNil`), or an assignment of a routine's own symbol to it
  ## (added to `assigned`). Anything else (an address taken, a `var`
  ## argument, an assignment of any other value, a read into another
  ## variable) is false: what `g` holds at a call is then not known.
  proc isG(x: NimNode): bool =
    var x = x
    while x.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and x.len > 0:
      x = x[^1]
    x.kind == nnkSym and x == g
  # An `if` chain over the kind, not a `case`: every other kind (the
  # default) descends into the children below, so a use of `g` under any
  # kind is still found (no listed-kind `case` for the K2a census to read).
  if n.kind == nnkSym:
    return n != g
  if n.kind in {nnkAsgn, nnkFastAsgn}:
    if n.len == 2 and isG(n[0]):
      var v = n[1]
      while v.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and
            v.len > 0:
        v = v[^1]
      if v.kind == nnkSym and symKind(v) in procValueSymKinds:
        assigned.add v
        return true
      # RFC-0016 W3-z R8: a closure the run builds (an anonymous routine,
      # its captures included) names its routine as a symbol does.
      if v.kind in {nnkLambda, nnkDo} and v.len > 0 and v[0].kind == nnkSym:
        assigned.add v[0]
        return true
      return false
  elif n.kind in nnkCallKinds:
    if n.len > 0 and isG(n[0]):
      for i in 1 ..< n.len:
        if not procValueUses(n[i], g, assigned): return false
      return true
    if n.len > 0 and n[0].kind == nnkSym and
       n[0].strVal in ["==", "!=", "isNil"]:
      for i in 1 ..< n.len:
        if not isG(n[i]) and not procValueUses(n[i], g, assigned):
          return false
      return true
  for c in n:
    if not procValueUses(c, g, assigned): return false
  true

type
  HeldSet* = object
    ## RFC-0016 W3-z R8. What a module-level proc-valued variable may hold at
    ## one point of a run (`heldAtCalls`): `start`, the value it held when
    ## the run started (read at run time), and the routines code stored in
    ## it before the point. `dead`: no run reaches the point.
    dead*: bool
    start*: bool
    routines*: seq[NimNode]

  HeldTarget = object
    label: NimNode
    loop: bool
    brk, cont: HeldSet

  HeldWalk = object
    g: NimNode
    top: HeldSet          ## the start value and every routine stored anywhere
    atCalls: HeldSet      ## joined over every call through `g`
    failed: bool          ## the walk met what it does not order: use `top`
    stack: seq[string]
    returns: seq[HeldSet]
    targets: seq[HeldTarget]
    touchMemo: Table[string, bool]
    valueTouch: bool      ## a routine some value may hold may touch the variable
    precise: seq[string]  ## routines entered by a direct call the walk followed

func deadHeld(): HeldSet = HeldSet(dead: true)

proc joinHeld(a, b: HeldSet): HeldSet =
  if a.dead: return b
  if b.dead: return a
  result = HeldSet(start: a.start or b.start, routines: a.routines)
  for r in b.routines:
    if r notin result.routines: result.routines.add r

proc sameHeld(a, b: HeldSet): bool =
  if a.dead != b.dead or a.start != b.start or
     a.routines.len != b.routines.len: return false
  for r in a.routines:
    if r notin b.routines: return false
  true

proc stripConv(x: NimNode): NimNode =
  result = x
  while result.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and
        result.len > 0:
    result = result[^1]

proc heldIsG(w: HeldWalk; x: NimNode): bool =
  let x = stripConv(x)
  x.kind == nnkSym and x == w.g

proc storedRoutine(v: NimNode): NimNode =
  ## The routine an assignment to the variable stores (`procValueUses` admits
  ## only these), or nil.
  let v = stripConv(v)
  if v.kind == nnkSym and symKind(v) in procValueSymKinds: return v
  if v.kind in {nnkLambda, nnkDo} and v.len > 0 and v[0].kind == nnkSym:
    return v[0]
  nil

proc bodyOf(r: NimNode): NimNode =
  ## The body of a routine with one, or nil (magic, foreign, a borrow).
  let impl =
    try: r.getImpl
    except CatchableError: newEmptyNode()
  if impl.kind in RoutineNodes and impl.len > 6 and impl[6].kind != nnkEmpty:
    impl[6]
  else: nil

const heldDefs = RoutineNodes
  ## A routine's definition: it runs nothing where it stands.

proc isRoutineHead(h: NimNode): bool =
  h.kind == nnkSym and symKind(h) in procValueSymKinds + {nskMethod, nskIterator}

proc heldTouches(w: var HeldWalk; r: NimNode): bool

proc heldTouchesNode(w: var HeldWalk; n: NimNode): bool =
  ## `n` may store into the variable, call through it, or run code the walk
  ## cannot follow (an indirect call, a dispatch, foreign code handed a
  ## routine).
  if n.kind in heldDefs: return false          # a definition runs nothing
  elif n.kind in {nnkAsgn, nnkFastAsgn, nnkSinkAsgn}:
    if n.len == 2 and w.heldIsG(n[0]): return true
  elif n.kind in nnkCallKinds:
    if n.len > 0:
      let h = stripConv(n[0])
      if w.heldIsG(h): return true
      if isRoutineHead(h):
        if symKind(h) == nskMethod: return true
        if bodyOf(h) != nil:
          if w.heldTouches(h): return true
        else:
          for i in 1 ..< n.len:
            if n[i].typeKind == ntyProc and w.valueTouch: return true
      elif h.kind != nnkSym or symKind(h) notin {nskTemplate, nskMacro}:
        # An indirect call runs a routine some value holds.
        if h.typeKind == ntyProc and w.valueTouch: return true
  for c in n:
    if w.heldTouchesNode(c): return true
  false

proc heldTouches(w: var HeldWalk; r: NimNode): bool =
  let key = routineKey(r)
  if key in w.touchMemo: return w.touchMemo[key]
  w.touchMemo[key] = true            # a cycle is assumed to touch
  let b = bodyOf(r)
  let t = b == nil or w.heldTouchesNode(b)
  w.touchMemo[key] = t
  t

proc heldWalk(w: var HeldWalk; n: NimNode; s: var HeldSet)

proc heldBody(w: var HeldWalk; r: NimNode; s: var HeldSet) =
  ## A direct call of `r`: its body runs here, from `s`.
  let key = routineKey(r)
  if key in w.stack:
    w.failed = true                  # recursion: not ordered
    return
  if key notin w.precise: w.precise.add key
  w.stack.add key
  w.returns.add deadHeld()
  heldWalk(w, bodyOf(r), s)
  s = joinHeld(s, w.returns.pop())
  discard w.stack.pop()

proc heldLoop(w: var HeldWalk; cond, body: NimNode; havoc: bool;
              s: var HeldSet) =
  ## A loop, to a fixed point: its head joins what each pass leaves.
  var head = s
  for _ in 0 .. 32:
    if havoc: head = joinHeld(head, w.top)
    var c = head
    if cond != nil: heldWalk(w, cond, c)
    w.targets.add HeldTarget(label: newEmptyNode(), loop: true,
                             brk: deadHeld(), cont: deadHeld())
    var b = c
    heldWalk(w, body, b)
    let t = w.targets.pop()
    let nh = joinHeld(head, joinHeld(b, t.cont))
    if sameHeld(nh, head):
      s = joinHeld(c, t.brk)
      if havoc: s = joinHeld(s, w.top)
      return
    head = nh
  w.failed = true

proc heldWalk(w: var HeldWalk; n: NimNode; s: var HeldSet) =
  ## RFC-0016 W3-z R8. Follows the run's code in the order it executes,
  ## carrying what the variable holds (`s`), and joins it into `atCalls` at
  ## every call through the variable. A point where code the walk does not
  ## follow may run joins `top` in; a shape it does not order fails the walk.
  if n.isNil or w.failed: return
  if n.kind in heldDefs: discard
  elif n.kind in {nnkAsgn, nnkFastAsgn, nnkSinkAsgn}:
    if n.len == 2 and w.heldIsG(n[0]):
      heldWalk(w, n[1], s)
      let r = storedRoutine(n[1])
      if r.isNil: w.failed = true
      elif not s.dead: s = HeldSet(routines: @[r])
    else:
      for c in n: heldWalk(w, c, s)
  elif n.kind in nnkCallKinds:
    let h = if n.len > 0: stripConv(n[0]) else: newEmptyNode()
    if w.heldIsG(h):
      var before = s                 # var, not let: the VM aliases a let to the var param
      for i in 1 ..< n.len: heldWalk(w, n[i], s)
      if not s.dead:
        w.atCalls = joinHeld(w.atCalls, joinHeld(before, s))
        s = joinHeld(s, w.top)       # the callee may store into it
    elif isRoutineHead(h):
      for i in 1 ..< n.len: heldWalk(w, n[i], s)
      if symKind(h) in {nskMethod, nskIterator}:
        s = joinHeld(s, w.top)
      elif bodyOf(h) != nil:
        if w.heldTouches(h):
          # The stdlib's code names no variable of the program: what it runs
          # of the program's is not followed, only joined.
          if isStdlibDecl(h): s = joinHeld(s, w.top)
          else: heldBody(w, h, s)
      else:
        for i in 1 ..< n.len:
          if n[i].typeKind == ntyProc and w.valueTouch:
            s = joinHeld(s, w.top)
    else:
      for c in n: heldWalk(w, c, s)
      if h.kind != nnkSym or symKind(h) notin {nskTemplate, nskMacro}:
        if h.typeKind == ntyProc and w.valueTouch: s = joinHeld(s, w.top)
  elif n.kind in {nnkIfStmt, nnkIfExpr}:
    var cur = s
    var outs = deadHeld()
    var hadElse = false
    for br in n:
      if br.kind in {nnkElifBranch, nnkElifExpr} and br.len == 2:
        heldWalk(w, br[0], cur)
        var b = cur
        heldWalk(w, br[1], b)
        outs = joinHeld(outs, b)
      elif br.kind in {nnkElse, nnkElseExpr} and br.len == 1:
        hadElse = true
        var b = cur
        heldWalk(w, br[0], b)
        outs = joinHeld(outs, b)
      else:
        w.failed = true
    s = if hadElse: outs else: joinHeld(outs, cur)
  elif n.kind in {nnkCaseStmt}:
    if n.len == 0:
      w.failed = true
      return
    heldWalk(w, n[0], s)
    var outs = s                     # conservatively: no branch taken too
    for i in 1 ..< n.len:
      var b = s
      if n[i].len > 0: heldWalk(w, n[i][^1], b)
      outs = joinHeld(outs, b)
    s = outs
  elif n.kind in {nnkWhileStmt}:
    heldLoop(w, n[0], n[1], false, s)
  elif n.kind in {nnkForStmt}:
    let it = n[^2]
    var havoc = false
    if it.kind in nnkCallKinds and it.len > 0:
      for i in 1 ..< it.len: heldWalk(w, it[i], s)
      let h = stripConv(it[0])
      havoc = h.kind != nnkSym or w.heldTouchesNode(it)
    else:
      heldWalk(w, it, s)
    heldLoop(w, nil, n[^1], havoc, s)
  elif n.kind in {nnkBlockStmt, nnkBlockExpr}:
    w.targets.add HeldTarget(label: n[0], loop: false,
                             brk: deadHeld(), cont: deadHeld())
    heldWalk(w, n[1], s)
    let t = w.targets.pop()
    s = joinHeld(s, t.brk)
  elif n.kind in {nnkBreakStmt}:
    var at = -1
    for i in countdown(w.targets.high, 0):
      if n.len == 0 or n[0].kind == nnkEmpty or
         (w.targets[i].label.kind == nnkSym and n[0].kind == nnkSym and
          w.targets[i].label == n[0]):
        at = i
        break
    if at < 0:
      w.failed = true
      return
    w.targets[at].brk = joinHeld(w.targets[at].brk, s)
    s = deadHeld()
  elif n.kind in {nnkContinueStmt}:
    var at = -1
    for i in countdown(w.targets.high, 0):
      if w.targets[i].loop:
        at = i
        break
    if at < 0:
      w.failed = true
      return
    w.targets[at].cont = joinHeld(w.targets[at].cont, s)
    s = deadHeld()
  elif n.kind in {nnkReturnStmt}:
    for c in n: heldWalk(w, c, s)
    if w.returns.len > 0:
      w.returns[^1] = joinHeld(w.returns[^1], s)
    s = deadHeld()
  elif n.kind in {nnkRaiseStmt}:
    for c in n: heldWalk(w, c, s)
    s = deadHeld()
  elif n.kind in {nnkTryStmt}:
    # A handler or `finally` starts from any point of the body, or of a
    # routine it calls: from `top`. So does what follows.
    heldWalk(w, n[0], s)
    for i in 1 ..< n.len:
      var h = w.top
      heldWalk(w, n[i], h)
    s = w.top
  elif n.kind in {nnkDefer}:
    var d = w.top
    for c in n: heldWalk(w, c, d)
    s = joinHeld(s, w.top)
  elif n.kind in {nnkYieldStmt}:
    w.failed = true
  else:
    for c in n: heldWalk(w, c, s)

proc heldCalls(n, g: NimNode): bool =
  ## `n` (a routine's body) calls through `g`, outside its nested routines.
  if n.kind in heldDefs: return false
  elif n.kind in nnkCallKinds:
    if n.len > 0:
      let h = stripConv(n[0])
      if h.kind == nnkSym and h == g: return true
  for c in n:
    if heldCalls(c, g): return true
  false

proc collectRoutineValues(n: NimNode; acc: var seq[string]) =
  ## Every routine `n` names other than as the head of a call: one a value
  ## may hold, run where the walk does not follow.
  if n.kind in {nnkLambda, nnkDo}:
    if n.len > 0 and n[0].kind == nnkSym: acc.add routineKey(n[0])
  elif n.kind in routineShapedForClosureDetect:
    discard
  elif n.kind in {nnkSym}:
    if symKind(n) in procValueSymKinds: acc.add routineKey(n)
  elif n.kind in nnkCallKinds:
    if n.len > 0 and not isRoutineHead(stripConv(n[0])):
      collectRoutineValues(n[0], acc)
    for i in 1 ..< n.len: collectRoutineValues(n[i], acc)
  else:
    for c in n: collectRoutineValues(c, acc)

proc collectHeads(n: NimNode; acc: var seq[NimNode]) =
  if n.kind in heldDefs: return
  if n.kind in nnkCallKinds and n.len > 0:
    let h = stripConv(n[0])
    if isRoutineHead(h): acc.add h
  for c in n: collectHeads(c, acc)

proc heldAtCalls*(fn, g: NimNode; userRoutines: seq[NimNode];
                 assigned: seq[NimNode]): HeldSet =
  ## RFC-0016 W3-z R8. What the module-level proc-valued variable `g` may hold
  ## at a call through it, on any run of `fn`: `start` when a call may run
  ## the value it held as the run began, and the routines stored in it before
  ## a call. The answer is ordered: a store after the last call, or a start
  ## value replaced before every call, is not in it. It follows the direct
  ## calls from `fn` (`heldWalk`); a call in a routine a run may enter
  ## otherwise (through a proc value, as a hook, from code the walk did not
  ## follow) holds `top`, the unordered answer (R7's: the start value and
  ## every routine stored in it anywhere), as does every call when the walk
  ## fails.
  var w = HeldWalk(g: g, top: HeldSet(start: true, routines: assigned),
                   atCalls: deadHeld())
  for r in userRoutines:
    # A lifetime hook runs where the compiler inserts it, at no point the
    # walk orders.
    if strVal(r).startsWith("="): return w.top
  # A routine a proc value may hold runs at an indirect call (or one in
  # foreign code handed it): only one the program names as a value, and only
  # one that may touch the variable, makes such a call matter. Decided with
  # every indirect call assumed to touch (a value that makes one counts).
  var values: seq[string]
  for r in userRoutines:
    let b = bodyOf(r)
    if b != nil: collectRoutineValues(b, values)
  w.valueTouch = true
  var vt = false
  for r in userRoutines:
    if routineKey(r) in values and w.heldTouches(r): vt = true
  w.valueTouch = vt
  w.touchMemo.clear()
  var s = HeldSet(start: true)
  heldBody(w, fn, s)
  if w.failed: return w.top
  var implicit: seq[string]
  var stack: seq[NimNode]
  for r in userRoutines:
    let k = routineKey(r)
    if k in values or strVal(r).startsWith("=") or k notin w.precise:
      stack.add r
  while stack.len > 0:
    let r = stack.pop()
    let k = routineKey(r)
    if k in implicit: continue
    implicit.add k
    let b = bodyOf(r)
    if b == nil: continue
    if heldCalls(b, g): w.atCalls = joinHeld(w.atCalls, w.top)
    var callees: seq[NimNode]
    collectHeads(b, callees)
    for c in callees: stack.add c
  w.atCalls
