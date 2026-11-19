## nelli/smt/replay_footprint -- what a witness replay may read: the replay
## eligibility rules (`replayEligible`, `replayInScope`, `replayReached`) and
## the compile-time footprint scan of the SUT and every routine it reaches
## (globals, hooks, threadvars, nested routines).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The `{.compileTime.}`
## memo tables (`routineFootprints`, `fileHookMemo`, `typeHookMemo`) and the
## `CacheTable` for runtime files live here and nowhere else.

import std/[macros, sets, tables, strutils, macrocache, compilesettings]
from std/os import fileExists
from ./check_scan import libRelPath
import ./dsl
import ./scan_kinds
from ./scoped_names import isModuleGlobal, isRoutineGlobal, globalIRName
import ./replayproc

# ---- Witness replay (RFC-0005 S2, §4.2) --------------------------------------
#
# The execution contract behind RFC-0005's SAT relaxation: a `sxSat`/`sxRaised`
# the engine would newly permit on a `scSpurious`-tainted path must first have
# its witness RUN against the real `fn`. S2 lands the substrate only -- the
# outcome type, the target-shaped `replayWitness` macro, the eligibility gate
# and (in `engine/markers.nim`) the stackable capture context. S10 wires it
# into the verdict of BOTH `runSymex` consumers (`symexFind` and the
# `symexFindAllWitnesses` codegen).
#
# WHY A MACRO. Invoking the SUT means splatting a typed witness tuple into its
# parameter list with `var`-param wrapping -- the same codegen
# `assertCoveredBy` does -- and `runSymex` is runtime code with no `fn`. So
# replay runs in macro-generated code AFTER `runSymex` returns (§4.2
# "Plumbing"). `emitReplayWitness` is the macro-time half S10 splices into
# the entry macros, which already hold the parsed `params`.
#
# CONTRACT (§4.2, for §8.1 / S11's migration note): `symexFind` EXECUTES `fn` on
# solver-chosen inputs, where it never ran `fn` before. A `scSpurious` path is
# tainted precisely because it ran through an unmodelled (often effectful:
# `echo`/`writeFile`, #137) call. Effects outside the process (a file written)
# happen for real. Effects inside it do not reach the host.
#
# RFC-0005 S8ct. No replay runs in the host process. A witness on a path the
# model may have wrong can reach anything the real program can: `quit`, a raw C
# `exit`, `abort`, a nil dereference, unbounded recursion, heap exhaustion, a wild
# write. No in-process interception contains the last few, and a corrupted host
# is what must not happen. So each replay runs in a child (`replayproc.nim`) and
# the host keeps only what the child reported: `fork` on POSIX, a re-execution of
# the program on Windows. A replay that cannot get a child does not run, and the
# verdict stays declined (`roDeclined`).
#
# NON-TERMINATION (§4.2). The eligibility gate declines a `dcFabricated` (k-unroll
# survivor) witness without running it. Any other witness may still drive a routine
# the model never walked into a loop: the child is killed past
# `SymexSettings.replayTimeoutMs` (`roTimedOut`). Nothing is left running, so one
# replay's state cannot meet another's.
#
# Re-execution hands the child what the SUT may reach (`replayFootprint`). A SUT
# that may reach what cannot be handed over does not run.

type ReplayFootprint* = object
  ## RFC-0005 S8cb. The state a replay may reach beyond its arguments: the
  ## module-level variables (and C routines of the stdlib) its code names,
  ## transitively. `open`: some code it may run cannot be read, so it may reach
  ## anything. RFC-0005 S8ct: `globals` holds the variables' symbols, which a
  ## re-executed child is handed.
  open*: bool
  why*: string
  globals*: seq[NimNode]
  routines*: seq[NimNode]
    ## RFC-0016 PRC-02. The program's own top-level routines the scan read: the
    ## table a proc value crosses by (`replaywire.nim`).
  methods*: seq[NimNode]
    ## RFC-0016 PRC-02b. Every method the scan read: the bodies the child may
    ## run, which the toolchain's dispatch table is checked against.
  dispatched*: seq[NimNode]
    ## RFC-0016 PRC-02b. The methods the code calls through a dispatcher: the
    ## dispatchers the table is asked about (`methodDispatchRefusal`).
  userRoutines*: seq[NimNode]
    ## RFC-0016 W3-z R7. Every routine of the program the scan read, nested
    ## and generic ones included: the code a replay may run that can name a
    ## module-level variable (`procValueUses`).
  nested*: seq[NimNode]
    ## RFC-0016 W3-z R10. The program's nested routines the scan read inside
    ## a routine it also read (a closure's code): the table's slots after
    ## `routines`, whose addresses only top-level code can take
    ## (`nestedRoutineAddrs`).

func replayEligible*(pathTaint: Taint): bool =
  ## RFC-0005 §4.2 eligibility gate: replay is attempted only for a candidate
  ## whose path taint derives ENTIRELY from `dcFreshSymbol` sites. Read off
  ## `RawResult.pathTaint` (RFC-0005 S1) via the class algebra rather than a
  ## site list: `pathTaint(dcFreshSymbol) == {scSpurious}` and `dcOmitted`
  ## contributes `{}`, while `dcSubstituted`/`dcFabricated`/`dcNoAnswer` all
  ## put `scIncomplete` on the PATH -- so "entirely fresh-symbol" is exactly
  ## "within `pathTaint(dcFreshSymbol)`". A clean path (`{}`) is trivially
  ## eligible. A `dcFabricated` candidate is thereby `roInconclusive` by
  ## construction, at no cost (§0.3: the k-unroll SAT payoff is empty), and
  ## that is the bound on the non-termination hazard.
  pathTaint <= pathTaint(dcFreshSymbol)

func replayInScope*(target: SymexTarget): bool =
  ## RFC-0005 §4.2 "Defect-flavoured targets": the target kinds replay may
  ## execute. Outside scope the answer is `roInconclusive`, without running.
  ##   * `stkNilAccess` -- never: a raw-`ptr` nil deref is a SIGSEGV, not a
  ##     catchable Defect, and a `ref` nil deref is catchable only under
  ##     nil-checking builds. Executing could kill the caller's process.
  ##   * EVERY target under `--panics:on` (`nimPanics`), where a Defect is
  ##     not catchable and aborts the process. S2 declined only the Defect
  ##     TARGETS there; RFC-0005 S10 widens it to all targets, because S10
  ##     runs replay implicitly inside `symexFind`/`symexFindAllWitnesses`
  ##     on a CANDIDATE -- a witness from a path whose model diverges from
  ##     reality by construction (`scSpurious`), so the real `fn` may hit a
  ##     Defect the model never forked (an `IndexDefect` before a label, a
  ##     user `Defect` subtype the `endsWith("Defect")` convention misses)
  ##     even when the target itself is a label.
  ##   * `stkRaisedExn` for `NilAccessDefect` -- never, for `stkNilAccess`'s
  ##     reason (RFC-0005 S8k). S10 replays an `sxRaised` candidate against
  ##     `tRaisedExn(<its type>)`, and the walker's only producer of that
  ##     type is its nil-dereference fork, whose real run is a SIGSEGV in
  ##     the default build of the pinned toolchain (probed: a `ref` read or
  ##     write through nil, `--nilchecks:on` or not, never reaches an
  ##     `except NilAccessDefect` arm), not a Defect.
  ##   * otherwise every kind (`stkLabel`, the Defect targets, any other
  ##     `stkRaisedExn`): an escaping exception, Defects included, is caught
  ##     by the replay frame and classified.
  const panics = buildSemantics.panics
  if panics: return false
  case target.kind
  of stkLabel, stkAssertionViolation, stkIndexError, stkFieldDefect: true
  of stkRaisedExn: target.typeFilter != "NilAccessDefect"
  of stkNilAccess: false
  of stkUndefined: false   ## RFC-0016 K10a-target: a witness that reaches
                           ## undefined behaviour is never run (section 9.1
                           ## item 6); the replay would cross it for real.

func replayReached*(target: SymexTarget; hits: HashSet[string];
                    escaped: ref Exception): bool =
  ## RFC-0005 §4.2: did one real execution reach `target`? `hits` is the
  ## execution's own capture frame; `escaped` is the exception that escaped
  ## `fn` (nil when it returned normally). A label counts if it was hit at
  ## all, even if `fn` raised afterwards. The raise kinds mirror what the
  ## walker reports as the finding: an exception ESCAPING the SUT frame
  ## (`routeRaise`'s step 3 -- a handler-caught raise is never a finding),
  ## matched by exact type name for `stkRaisedExn` (the walker's
  ## `typeFilter == typeId` test) and by subtype for the builtin Defects
  ## (`assertCoveredBy`'s precedent).
  case target.kind
  of stkLabel:              target.label in hits
  of stkAssertionViolation: not escaped.isNil and escaped of AssertionDefect
  of stkIndexError:         not escaped.isNil and escaped of IndexDefect
  of stkFieldDefect:        not escaped.isNil and escaped of FieldDefect
  of stkRaisedExn:
    not escaped.isNil and
      (target.typeFilter.len == 0 or $escaped.name == target.typeFilter)
  of stkNilAccess:          false   ## out of scope; never executed
  of stkUndefined:          false   ## RFC-0016 K10a-target: never executed

proc formalParamTypes*(fn: NimNode): seq[NimNode] =
  ## RFC-0005 S10. The declared parameter types of the typed proc `fn`, one
  ## per parameter, `var` stripped -- what replay's splat converts the
  ## rendered witness to. Empty when `fn`'s type is not a plain proc type
  ## (the caller then declines to replay).
  let ty = getTypeImpl(fn)
  if ty.kind != nnkProcTy or ty.len == 0 or ty[0].kind != nnkFormalParams:
    return @[]
  for i in 1 ..< ty[0].len:
    let d = ty[0][i]
    var t = d[^2]
    if t.kind == nnkVarTy: t = t[0]
    # RFC-0016 K2c: `openArray[T]`/`varargs[T]` are not types a local can have
    # (`var p: openArray[int]` stops the compile), and the witness renders them
    # as the `seq[T]` they are modelled as, which converts to either at the call.
    if t.kind == nnkBracketExpr and t.len == 2 and t[0].kind in {nnkSym, nnkIdent} and
       t[0].strVal in ["openArray", "varargs"]:
      t = nnkBracketExpr.newTree(bindSym"seq", t[1])
    for _ in 0 ..< d.len - 2: result.add t

proc isThreadvarSym(n: NimNode): bool =
  ## RFC-0005 S8bo. `n` is the symbol of a `{.threadvar.}` variable.
  if n.kind != nnkSym or symKind(n) != nskVar: return false
  let impl =
    try: n.getImpl
    except CatchableError: return false
  if impl.kind != nnkIdentDefs or impl.len < 1 or
     impl[0].kind != nnkPragmaExpr or impl[0].len < 2:
    return false
  for p in impl[0][1]:
    if p.kind in {nnkIdent, nnkSym} and p.strVal == "threadvar": return true
  false

proc routineKey*(r: NimNode): string =
  ## RFC-0005 S8cb. Tells routines apart, including generic instances:
  ## `signatureHash` alone is the same for every routine of a module with the
  ## same parameter types, so a scan keyed by it read only the first of them.
  ## RFC-0016 W3-z R10: and the declaration's position. `symBodyHash` is the
  ## same for two routines of one name whose bodies read alike (every
  ## anonymous routine is `:anonymous`): `proc (v: int): int = v + n` in two
  ## routines, one under `push overflowChecks: off`, shared one memoised
  ## answer (`routineUndefinedMemoised`), so the unchecked one read as checked.
  ## The position is the definition's (`getImpl`), not the node's: a symbol
  ## node carries the position of its use.
  let at =
    try:
      let impl = r.getImpl
      if impl.kind in RoutineNodes: impl.lineInfo else: ""
    except CatchableError: ""
  r.strVal & "#" & r.symBodyHash & "@" & at

type RoutineFootprint* = object
  ## RFC-0005 S8cb. What one routine's own body names (`scanFootprint`).
  ## RFC-0005 S8ct: `why` names what made it open.
  globals*: seq[NimNode]
  callees*: seq[NimNode]
  ownGlobals*: seq[NimNode]
    ## RFC-0016 PRC-02. A `{.global.}` of another routine, which is the child's
    ## own if that routine is one the child runs (`replayFootprint` decides).
  dispatched*: seq[NimNode]
    ## RFC-0016 PRC-02b. The methods this body calls through their dispatcher
    ## (a `procCall` is a static call, so is not one).
  open*: bool
  why*: string

var routineFootprints {.compileTime.}: Table[string, RoutineFootprint]
  ## RFC-0005 S8cb. Per routine (`routineKey`), so that a program's replays
  ## read each of the stdlib routines they share once.

var fileHookMemo {.compileTime.}: Table[string, bool]
var typeHookMemo {.compileTime.}: Table[string, bool]

proc textNamesHook(text: string): bool =
  ## RFC-0005 S8ct. `text` holds `=destroy`, `=sink`, `=copy`, `=dup` or
  ## `=trace`. RFC-0016 W3-z R10 follow-up: in one pass over the text, from
  ## one `=` to the next, stopping at the first. Five whole-text searches (one
  ## per hook, none stopping) cost the compile-time VM five iterations a byte,
  ## and a replay's scan reads every module of the program it reaches
  ## (`types.nim` alone is 330 kB): past the VM's default iteration limit
  ## (`tsymex_0016_w3z_r10_nestedreplay`).
  var i = text.find('=')
  while i >= 0:
    for h in ["destroy", "sink", "copy", "dup", "trace"]:
      if text.continuesWith(h, i + 1): return true
    i = text.find('=', i + 1)
  false

proc fileDeclaresHook(path: string): bool =
  ## RFC-0005 S8ct. A type's hooks must be declared in its module. The macro API
  ## cannot ask a type for its hooks, so the module's text is what is read; one
  ## it cannot read counts as declaring them.
  ## A path with no file behind it (a type declared by code a macro made with
  ## `parseStmt`, which carries a pseudo path, empty under Windows) is not
  ## read at all: the compile-time VM's `readFile` raises past the VM, so the
  ## `try` below cannot catch it and the compiler stops ("cannot open:").
  if path in fileHookMemo: return fileHookMemo[path]
  result = true
  if path.len > 0 and fileExists(path):
    try:
      result = textNamesHook(readFile(path))
    except CatchableError:
      discard
  fileHookMemo[path] = result

proc typeMayHaveHook(t: NimNode; seen: var seq[string]): bool =
  ## RFC-0005 S8ct. A program type in `t` (a type, as `getTypeInst` gives it) may
  ## have a hook the compiler inserts calls to, which code in the routine's body
  ## does not name. The stdlib's hooks hold no state of the program's.
  case t.kind
  of nnkSym:
    if symKind(t) != nskType: return false
    if t.typeKind in {ntyBool, ntyChar, ntyString, ntyCstring, ntyPointer,
                      ntyInt .. ntyInt64, ntyFloat .. ntyFloat128,
                      ntyUInt .. ntyUInt64}:
      return false
    if isStdlibDecl(t): return false
    let impl =
      try: t.getImpl
      except CatchableError: newEmptyNode()
    # A type the program declares has a definition. One with none is a builtin
    # constructor (`array`, `seq`), whose hooks are the runtime's.
    if impl.kind != nnkTypeDef: return false
    # Where the type is declared: the symbol's own position is that of the node
    # `getTypeInst` made, which is in this module.
    let at = impl.lineInfoObj
    let key = t.strVal & "@" & at.filename & ":" & $at.line
    if key in typeHookMemo: return typeHookMemo[key]
    if key in seen: return false
    seen.add key
    result = fileDeclaresHook(at.filename)
    if not result: result = typeMayHaveHook(impl[2], seen)
    typeHookMemo[key] = result
  of nnkIdent, nnkEmpty, nnkNilLit, nnkCharLit .. nnkFloat128Lit,
     nnkStrLit .. nnkTripleStrLit, nnkType, nnkCommentStmt:
    discard
  of mayScanNoCodeKinds + mayScanStructuralKinds + RoutineNodes + {nnkRecList,
     nnkRecCase, nnkRecWhen, nnkOfInherit, nnkEnumFieldDef}:
    # RFC-0016 K2F-3: a type's structure, or an expression inside one (a range
    # bound): a hook is a type symbol's, read above.
    for c in t:
      if typeMayHaveHook(c, seen): return true
  else:  # k2: fail-closed: true: the type may have a hook, so the routine's footprint is opened
    # RFC-0016 K2F-3 (RFC section 8.1): a type shape not listed may hold a
    # program type this scan cannot see.
    return true

proc isImportedVar(n: NimNode): bool =
  ## RFC-0005 S8ct. `n` is a C variable, as opposed to storage of this program.
  let impl =
    try: n.getImpl
    except CatchableError: return false
  if impl.kind != nnkIdentDefs or impl.len < 1 or
     impl[0].kind != nnkPragmaExpr or impl[0].len < 2:
    return false
  for p in impl[0][1]:
    let head = if p.kind == nnkExprColonExpr: p[0] else: p
    if head.kind in {nnkIdent, nnkSym} and
       head.strVal in ["importc", "importcpp", "header"]:
      return true
  false

proc markOpen(acc: var RoutineFootprint; why: string) =
  acc.open = true
  if acc.why.len == 0: acc.why = why

proc unlistedOpen(acc: var RoutineFootprint; n: NimNode; owner: string) =
  ## RFC-0016 K2F-3. A node kind `scanFootprint` does not list: what it may
  ## reach is not named, so the replay declines.
  acc.markOpen("a `" & $n.kind & "` in `" & owner & "`, which the footprint " &
               "does not read")

proc scanFootprint(n: NimNode; user: bool; owner: string; selfKey: string;
                   acc: var RoutineFootprint) =
  ## RFC-0005 S8cb. See `replayFootprint`. `user`: `n` is code of the program,
  ## not of the stdlib; `owner`: the routine's name.
  case n.kind
  of nnkSym:
    case symKind(n)
    of nskVar, nskLet, nskParam, nskForVar, nskResult:
      # A stdlib `let` cannot change, and its module has initialised by the time
      # a child reaches the call site. A stdlib thread variable is the child's
      # own, as it would be any new thread's.
      if symKind(n) in {nskVar, nskLet} and isThreadvarSym(n):
        if user: acc.globals.add n
      elif symKind(n) in {nskVar, nskLet} and isModuleGlobal(n):
        if isImportedVar(n):
          # A C variable holds what no marshalling can see. The stdlib's are the
          # C library's (`stdout`), which the child has its own of.
          if user: acc.markOpen("`" & n.strVal & "`, a C variable")
        elif isRoutineGlobal(n):
          # Naming a routine's `{.global.}` from outside that routine does not
          # link: a C `extern` emitted first takes the place of its definition.
          # RFC-0016 W1-m: from inside it does. The child runs that routine
          # itself, so the variable is the child's own, initialised by its
          # own declaration: a state the program can be in, which the walk
          # models as any value of its type. (Declining here refused every
          # re-executed replay of such a SUT, so on Windows its SAT stayed
          # `sxUnknown` where a fork confirmed it.)
          # RFC-0016 PRC-02: the same of a routine nested in, or called by, the
          # one that declares it, as long as the child runs the declaring
          # routine: `replayFootprint` checks that once it has the whole set.
          let o = owner(n)
          if not user or o.kind != nnkSym:
            acc.markOpen("`" & n.strVal & "`, a routine's `{.global.}`")
          elif routineKey(o) != selfKey:
            acc.ownGlobals.add n
        elif user or symKind(n) == nskVar:
          acc.globals.add n
      # RFC-0016 PRC-02. A proc value the program holds names code this scan
      # reads, or came to it through state the wire carries: a routine named
      # in code the scan reads is itself scanned, and the wire writes a proc
      # value only as a routine of the scan (`replaywire.nim`), declining any
      # other, a closure with an environment included.
      # RFC-0016 INT-47. A template body's `except T as e` binds an `e` the
      # semchecker never typed (see `routeScan`): `getTypeInst` on it is a hard
      # "node has no type" error, reached only where a replay is re-executed
      # (Windows). It names no value of a type this scan misses; the expanded
      # copy of the body carries a typed `e`. Such an `e` reports `ntyNone` or
      # `ntyGenericInvocation` (the `ref`-of-exception it was to be), never a
      # type `getTypeInst` can give.
      if user and n.typeKind notin {ntyNone, ntyGenericInvocation}:
        var seen: seq[string]
        if typeMayHaveHook(n.getTypeInst, seen):
          acc.markOpen("`" & n.strVal & "`, of a type whose module declares a hook")
    of nskMethod:
      # RFC-0016 PRC-02b. With a toolchain that emits a per-binary dispatch
      # table the method is read, with every override visible to the entry, and
      # the replay checks the table at run time: a body it lists that no scan
      # read declines (`methodDispatchRefusal`). Stock Nim declines here.
      when hasMethodTable:
        if user:
          acc.callees.add n
          acc.dispatched.add n
          for o in registeredMethods(n.strVal): acc.callees.add o
        else:
          acc.markOpen("`" & n.strVal & "`, a method of the stdlib")
      else:
        # RFC-0016 PRC-02. Not closable: the override that runs depends on the
        # receiver's dynamic type, and the macro API cannot list a method's
        # overrides (they are collected into the dispatcher after this scan).
        # RFC-0016 PRC-02 / probes 3 and 4. The dispatcher is built after every
        # module is semmed and an override may sit in a module the entry cannot
        # see (or twice, in two modules: Nim accepts both and picks one), so no
        # list of overrides can be closed. A fork copies the process and replays
        # it, so the decline names the run that can. `<entry>` is filled in by
        # `replayFootprint`, which knows the routine it was asked about.
        var base = "its first parameter's type"
        let t = n.getTypeImpl
        if t.kind == nnkProcTy and t.len > 0 and t[0].kind == nnkFormalParams and
           t[0].len > 1 and t[0][1].kind == nnkIdentDefs:
          base = t[0][1][^2].repr
        acc.markOpen("`" & n.strVal & "`, a method on `" & base & "`, whose " &
                     "overrides the scan cannot list (one may be declared in a " &
                     "module `<entry>` cannot see; a Linux or macOS run forks " &
                     "and replays it)")
    of nskType:
      # RFC-0005 batch 11. A value no variable holds still has its hooks run: a
      # constructor's or a conversion's temporary, passed on to a callee that
      # consumes it, is destroyed at a call the compiler inserts.
      if user:
        var seen: seq[string]
        if typeMayHaveHook(n, seen):
          acc.markOpen("`" & n.strVal & "`, a type whose module declares a hook")
    else:
      if symKind(n) in userRoutineSymKinds: acc.callees.add n
  of nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit,
     nnkHiddenCallConv:
    # RFC-0016 K2F-3: every call syntax, an operator's and a converter's too:
    # its result is a temporary just the same.
    if user and n.len > 0 and n[0].kind == nnkSym and
       symKind(n[0]) in userRoutineSymKinds:
      # RFC-0005 batch 11. A call's result is a value no variable need hold.
      # The callee's own type, the instance's for a generic: a node of the
      # body need not carry one.
      #
      # RFC-0016 INT-4a. A callee sym the semchecker never typed (the head of a
      # call inside a template body the scan reaches before its expansion)
      # reports `ntyNone`, and `getTypeImpl` on it is the same hard "node has
      # no type" error as the `getTypeInst` guard below, reached only where a
      # replay is re-executed (Windows). It names no result type this scan
      # misses: the expanded copy of the body carries a typed head.
      let pt =
        if n[0].typeKind == ntyNone: newEmptyNode()
        else: n[0].getTypeImpl
      let t =
        if pt.kind == nnkProcTy and pt.len > 0 and pt[0].kind == nnkFormalParams:
          pt[0][0]
        else: newEmptyNode()
      var seen: seq[string]
      if t.kind != nnkEmpty and typeMayHaveHook(t, seen):
        acc.markOpen("a call in `" & owner & "` whose result is of a type " &
                     "whose module declares a hook")
    # RFC-0016 PRC-02: a call through a proc value is read as a call of the
    # routines the scan reads (see the symbol case above).
    if n.kind in {nnkCall, nnkCommand} and n.len == 2 and
       n[0].kind == nnkSym and
       n[0].strVal == "procCall" and isStdlibDecl(n[0]) and
       n[1].kind in nnkCallKinds and
       n[1].len > 0 and n[1][0].kind == nnkSym and
       symKind(n[1][0]) == nskMethod:
      # `procCall m(args)` is a static call of `m`'s own body: no dispatch, so
      # no override can run. Scan `m` as a plain routine.
      acc.callees.add n[1][0]
      for i in 1 ..< n[1].len: scanFootprint(n[1][i], user, owner, selfKey, acc)
    else:
      for c in n: scanFootprint(c, user, owner, selfKey, acc)
  of nnkAsmStmt:
    if user: acc.markOpen("`asm` in `" & owner & "`")
  of nnkPragma:
    for p in n:
      let emits = p.kind == nnkExprColonExpr and
                  p[0].kind in {nnkIdent, nnkSym} and p[0].strVal == "emit"
      if emits and user: acc.markOpen("`emit` in `" & owner & "`")
  of mayScanLeafKinds:
    discard
  of mayScanNoCodeKinds + mayScanStructuralKinds + RoutineNodes - {nnkCall,
     nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit,
     nnkHiddenCallConv, nnkPragma}:
    for c in n: scanFootprint(c, user, owner, selfKey, acc)
  else:
    # RFC-0016 K2F-3 (RFC section 8.1): a kind not listed may reach state the
    # footprint does not name.
    if user: acc.unlistedOpen(n, owner)
    for c in n: scanFootprint(c, user, owner, selfKey, acc)

const runtimeFileMemo = CacheTable"nelli.symex.runtimeFile"
  ## RFC-0016 W3-z R10 follow-up. `isRuntimeCode`'s answer per file, as 1 or
  ## 0. A compiler table, so a lookup is one VM operation, not a loop.

proc isRuntimeFile(path: string): bool =
  ## `isRuntimeCode`, of the file a routine is declared in.
  if path in runtimeFileMemo: return runtimeFileMemo[path].intVal == 1
  let f = path.replace('\\', '/')
  var inSystem = false
  var i = f.find('/')
  while i >= 0 and not inSystem:
    inSystem = f.continuesWith("/lib/system/", i)
    i = f.find('/', i + 1)
  # RFC-0016 PRC-43: also under the configured lib path, whatever its name.
  let rel = libRelPath(f, querySetting(libPath))
  result = inSystem or f.endsWith("/lib/system.nim") or
    rel == "system.nim" or rel.startsWith("system/") or
    f.endsWith("/sysatomics.nim") or f.endsWith("/nelli/engine/markers.nim")
  runtimeFileMemo[path] = newLit(ord(result))

proc isRuntimeCode(impl: NimNode): bool =
  ## RFC-0005 S8cb. `impl` is in Nim's runtime (`lib/system*`, its atomics) or
  ## nelli's replay markers, whose state is per-thread, or synchronised, or of
  ## no consequence to what the program computes. A variable of it the program
  ## names is still the program's footprint (`scanFootprint`).
  ## RFC-0016 W3-z R10 follow-up: answered once per file (`runtimeFileMemo`),
  ## and `/lib/system/` is looked for by `continuesWith` at each `/`, not
  ## `in`, whose skip table costs the compile-time VM 256 iterations a call
  ## before it reads the path. A replay's footprint asks it of every routine
  ## it reads (`tsymex_0016_w3z_r10_nestedreplay`).
  isRuntimeFile(impl.lineInfoObj.filename)

proc routineFootprint(r: NimNode): RoutineFootprint =
  ## RFC-0005 S8cb. The routine `r`'s own footprint (`routineFootprints`).
  let key = routineKey(r)
  if key in routineFootprints: return routineFootprints[key]
  let user = not isStdlibDecl(r)
  let impl =
    try: r.getImpl
    except CatchableError: newEmptyNode()
  if impl.kind notin RoutineNodes or impl.len <= 6:
    # No definition this scan can read.
    if user: result.markOpen("`" & r.strVal & "`, with no definition to read")
  elif isRuntimeCode(impl):
    discard
  elif impl[6].kind == nnkEmpty:
    # Foreign code. The program's may do anything; the stdlib's are the C
    # library's, whose state the host and the child each have their own of.
    if user: result.markOpen("`" & r.strVal & "`, a foreign routine")
  else:
    scanFootprint(impl[6], user, r.strVal, key, result)
    # RFC-0005 batch 11. A parameter the body never names, or a result it never
    # spells, is still destroyed at the routine's end.
    if user and impl[3].kind == nnkFormalParams and not result.open:
      var seen: seq[string]
      for i in 0 ..< impl[3].len:
        let d = impl[3][i]
        let t = if i == 0: d elif d.len >= 2: d[^2] else: newEmptyNode()
        if t.kind != nnkEmpty and typeMayHaveHook(t, seen):
          result.markOpen("`" & r.strVal & "`, whose signature holds a type " &
                          "whose module declares a hook")
          break
  routineFootprints[key] = result

proc addressable*(r: NimNode): bool =
  ## RFC-0016 PRC-02. `r` can be a proc value: a routine with a body of its own.
  ## A `{.borrow.}` (whose body is the base type's operation, often a magic), a
  ## `magic`, `importc` or `compilerproc` routine, or a generic one has none the
  ## compiler can take the address of (`cast[pointer](==)` is an internal error
  ## for a borrowed `==`), so it is not in the table and a proc value naming it
  ## declines, as one naming any routine the scan did not read does.
  ## RFC-0016 W3-z R10: an anonymous routine (a closure's code) is read too.
  let impl = resolveRoutineOrLambdaImpl(r)
  if impl.isNil or impl.len <= 6: return false
  if impl[6].kind == nnkEmpty: return false
  if impl[2].kind != nnkEmpty: return false
  if impl[4].kind == nnkPragma:
    for p in impl[4]:
      let id = if p.kind == nnkExprColonExpr: p[0] else: p
      if id.kind in {nnkIdent, nnkSym} and
         id.strVal.normalize in ["magic", "importc", "compilerproc", "borrow",
                                 "importcpp", "importobjc", "dynlib"]:
        return false
  true

proc replayFootprint*(fn: NimNode): ReplayFootprint =
  ## RFC-0005 S8cb. The state a replay of `fn` may reach. A replay's parameters
  ## and locals are its own, and it reaches anything else through a module-level
  ## variable (or `{.global.}`, or thread variable) named in code it may run: the
  ## routines `fn` names, transitively, the stdlib's included. Open when some of
  ## that code cannot be read: a method, a proc value, a foreign routine or `emit`
  ## of the program, a routine that captures its caller's variables (a nested
  ## routine whose enclosing one the scan never entered), or a value of a type
  ## whose module declares a hook, which the compiler calls without naming it.
  ##
  ## RFC-0005 S8ct: only a re-executed child reads this: `fork` copies everything.
  if fn.kind != nnkSym or symKind(fn) notin userRoutineSymKinds or
     symKind(fn) == nskMethod:
    return ReplayFootprint(open: true, why: "a routine that is not a plain symbol")
  # RFC-0016 W3-z R10 follow-up: a set, not a list. A replay nested in the
  # routine reaches a thousand routines, and a list's membership test made
  # the scan quadratic in them (`tsymex_0016_w3z_r10_nestedreplay`).
  var seen: HashSet[string]
  var routines: seq[NimNode]
  var ownerGlobals: seq[(NimNode, string)]
  var nestedSeen: seq[NimNode]
  var stack = @[fn]
  while stack.len > 0:
    let r = stack.pop()
    let key = routineKey(r)
    if key in seen: continue
    seen.incl key
    routines.add r
    if not isStdlibDecl(r): result.userRoutines.add r
    if symKind(r) == nskMethod: result.methods.add r
    let f = routineFootprint(r)
    for d in f.dispatched: result.dispatched.add d
    if f.open and not result.open:
      result.open = true
      result.why = f.why.replace("<entry>", fn.strVal)
    if symKind(r) in procValueSymKinds and not isStdlibDecl(r) and
       addressable(r):
      let ro = owner(r)
      if ro.kind != nnkSym or symKind(ro) notin userRoutineSymKinds:
        result.routines.add r      # top level: its address can be named
      else:
        nestedSeen.add r           # W3-z R10: kept when its owner was read
    for g in f.ownGlobals:
      let o = owner(g)
      if o.kind == nnkSym: ownerGlobals.add (g, routineKey(o))
    for g in f.globals:
      var have = false
      for h in result.globals:
        if h == g:
          have = true
          break
      if not have: result.globals.add g
    for c in f.callees: stack.add c
  for (g, ok) in ownerGlobals:
    if ok notin seen and not result.open:
      result.open = true
      result.why = "`" & g.strVal & "`, a routine's `{.global.}`"
  for r in routines:
    let o = owner(r)
    if o.kind == nnkSym and
       symKind(o) in userRoutineSymKinds and
       routineKey(o) notin seen:
      result.open = true
      if result.why.len == 0:
        result.why = "`" & r.strVal & "`, nested in a routine it may capture from"
  for r in nestedSeen:
    if routineKey(owner(r)) in seen: result.nested.add r
