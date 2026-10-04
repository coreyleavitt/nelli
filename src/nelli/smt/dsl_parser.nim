## Layer 1 of the predicate DSL (ADR-0002): typed Nim AST → IR.
##
## This is the algorithmically subtle layer the ADR calls out as the
## one worth testing in isolation. It runs at macro time only.
##
## Supported fragment (cumulative across phases):
##
##   * Statements: `nnkStmtList`, `nnkBlockStmt`, `nnkIfStmt`,
##                 `nnkLetSection`/`nnkVarSection`, `nnkReturnStmt`,
##                 the body markers, and (Phase 3) user-defined proc
##                 calls.
##   * Expressions: int / bool / fixed-width-int literals + vars,
##                  `nnkInfix`/`nnkPrefix` arithmetic + comparison +
##                  boolean, `nnkHiddenStdConv`/`nnkConv` passthrough,
##                  and (Phase 3) calls to user procs — A-normalised
##                  into a preamble of `isCall` statements that bind
##                  fresh `__sym_<name>_<n>` temporaries.
##
## A-normalisation: each call expression `foo(args)` in expression
## position contributes:
##
##   1. An `isCall` stmt in the surrounding statement's *preamble*
##      that runs before the statement.
##   2. A fresh `mkVar(<synth>)` in place of the call.
##
## The walker only ever sees calls as statements.

# RFC-0005 S8e: `scoped_names.strVal` keys a name by its symbol.
# RFC-0005 S8bl: `dsl_typebridge`'s `typeKind` / `getTypeInst` /
# `getTypeImpl` read a borrowed routine's argument at its base type.
import std/macros except strVal, typeKind, getTypeInst, getTypeImpl
import std/effecttraits   ## RFC-0005 S8ax: an opaque routine's inferred `raises`
import std/options    ## RFC-chapulin-hardening Q1: tryRecognizeScanIdiom's Option[IRStmt]
import std/strformat
import std/strutils
import std/sets
import std/tables
import std/algorithm   ## Phase 15 G1a: sorted type-tuple in the inst key
import std/hashes      ## Phase 15 C1: lambda-site body-hash (lineInfo fallback)
import std/unicode     ## Phase 16 A7-S3: toRunes/runeLen for literal decode at parse time
import ./types
import ./dsl_typebridge
from ./abstraction import collectVarRefs   ## RFC-0005 S8bl: `writesName`
import ./stdlib_models
import ./exn_hierarchy   ## Phase 15 E4a: exnTypeTable (known-base sentinel)
import ./scoped_names    ## RFC-0005 S8e: scope-keyed names (`strVal`, claims)
import ./pcre_syntax     ## RFC-0005 S8ay: the regex `strOp` encoding; a rejected `re"..."` is a raise site

template typeKind(n: NimNode): NimTypeKind = viewTypeKind(n)
  ## RFC-0005 S8bl: every type query of the parser reads a borrowed
  ## routine's argument at its base type (`dsl_typebridge.viewTypeKind`).
template getTypeInst(n: NimNode): NimNode = viewTypeInst(n)
template getTypeImpl(n: NimNode): NimNode = viewTypeImpl(n)

# ---- Cluster N: routine-impl resolution (RFC-parser-normalization #146/#148) --
#
# The parser's effective input language is every AST shape the compiler can
# emit for the same meaning (RFC §0 Thesis). `walkableRoutineKinds` is one
# routine-kind vocabulary defined once; `resolveRoutineImpl` is the shared
# nil-core every resolution site's failure POLICY wraps. Invariant-3
# (load-bearing, RFC §0): per-site failure policies stay deliberate and
# distinct — API entry macros hard-error (`resolveEntryImpl`),
# `ensureProcRegistered` classified-degrades, pragma/generics predicates
# return false. Consolidation means one *predicate* with per-policy
# wrappers, never one merged *behavior*. N2 migrates the remaining
# resolution sites in this file onto `walkableRoutineKinds`/
# `resolveRoutineImpl`; N1 introduces the core and migrates symex.nim's
# nine public entry macros.

const walkableRoutineKinds* = {nnkProcDef, nnkFuncDef}
  ## The routine-kind vocabulary the walker's boundary accepts. A `func` is,
  ## for every purpose this parser cares about, AST-shape-identical to a
  ## `proc` (`799b0bc` widened 19 call sites to this effect; N0 completed
  ## the widening at the three sites the round-1 grep-audit had missed).
  ## Defined once so a hypothetical future accepted kind is a one-line
  ## change here plus at this const's consumers, not a re-audit of the
  ## whole file.

const routineShapedForClosureDetect* = RoutineNodes - {nnkDo, nnkLambda}
  ## RFC-parser-normalization N3. Answers: "does `calleeSym.getImpl` report
  ## an actual routine DEFINITION" — the negative of this test is the
  ## closure-call detector's trigger (`earlyClosureCallDetect`/
  ## `closureCallDetect`/the statement-position detector guarding
  ## `ensureProcRegistered`'s call fall-through): when `impl.kind` is NOT
  ## one of these AND the symbol's type is `nnkProcTy`, `calleeSym` names a
  ## proc-VALUED variable/param (a closure), not a defined routine, and the
  ## call is routed to `mkClosureCall` instead of ordinary user-proc
  ## dispatch.
  ##
  ## Defined against `std/macros.RoutineNodes` (all nine node kinds Nim's
  ## grammar recognises as a routine definition) with two exclusions, BOTH
  ## unreachable as a `getImpl` result — probe-verified 2026-08-13 (this
  ## slice) and by the N2 audit before it, kept out for definitional
  ## precision, not because including them would misclassify anything:
  ##
  ## - `nnkDo` — a `do:` block is parser-level sugar rewritten to an
  ##   `nnkLambda` node before semcheck produces any typed impl; no symbol's
  ##   `getImpl` can ever report `nnkDo` (`scratchpad/probe_n3_do_shape.nim`:
  ##   the typed `treeRepr` of a `do:`-block call argument shows `Lambda`,
  ##   never `Do`).
  ## - `nnkLambda` — an anonymous proc/lambda is not itself named by a
  ##   symbol whose `getImpl` reports it; a `let`/`var` binding a lambda
  ##   VALUE resolves (on the variable's OWN symbol) to `nnkIdentDefs`, not
  ##   `nnkLambda` (N2's audit finding: `getImpl` on
  ##   `nsk{Param,Let,Var,ForVar,Result}` never yields a walkable/routine
  ##   kind — this is exactly the mechanism the closure-call detector relies
  ##   on to fire). This set is therefore unchanged in MEMBERSHIP from the
  ##   pre-N3 7-element literal — only its spelling changed, from an inline
  ##   list to a named, audited exclusion from the canonical vocabulary.

const nestedRoutineScanBoundary* = RoutineNodes - {nnkDo}
  ## RFC-parser-normalization N3. Answers: "does this node start a NESTED
  ## scope the A3 (ADR-0014) shallow scanners — `hasYieldShallow`,
  ## and `hasReturnShallow`, `hasKindShallow` (and so
  ## `hasBreakContinueShallow`) — must not descend into". A `yield`/`return`/
  ## `break`/`continue` occurrence inside a nested routine
  ## definition belongs to THAT routine, not to the iterator body being
  ## characterized for A3's inline transform, so descent stops here.
  ##
  ## Defined against `std/macros.RoutineNodes` with one exclusion:
  ##
  ## - `nnkDo` — unreachable in a typed impl tree for the same reason noted
  ##   on `routineShapedForClosureDetect` above (`do:` blocks are already
  ##   `nnkLambda` by the time these scanners see the tree). A `do:` block's
  ##   own body is therefore already excluded from descent via `nnkLambda`,
  ##   which was already a member of the pre-N3 6-element literal.
  ##
  ## `nnkMethodDef` and `nnkConverterDef` are NEW members versus the pre-N3
  ## 6-element literal — closing the RFC's named latent gap. Both `method`
  ## and `converter` are Nim TOP-LEVEL-ONLY definitions — probe-verified
  ## 2026-08-13 (`scratchpad/probe_n3_nested_method.nim` /
  ## `probe_n3_nested_converter.nim`): the compiler rejects both with
  ## "'method'/'converter' is only allowed at top level" when nested inside
  ## a proc body. A `nnkMethodDef`/`nnkConverterDef` node can therefore
  ## never appear NESTED inside a body one of these scanners descends into
  ## — the gap the RFC flagged was real in the sense that the vocabulary
  ## was inconsistent, but never reachable at runtime. Adding them is
  ## behavior-identical hardening: it also makes this set's exclusion list
  ## (`{nnkDo}`) match `routineShapedForClosureDetect`'s reasoning exactly,
  ## even though the two consts answer different questions and are kept
  ## separate for that reason.

const routineImplMinArity = 7
  ## RFC-parser-normalization C1 totality clause. The fixed `RoutineNodes`
  ## layout (name, pattern, genericParams, formalParams, pragmas, reserved,
  ## body) is 7 slots; probe-verified 2026-08-14
  ## (`scratchpad/probe_c1_dumptree3.nim`) that real `nnkFuncDef`/
  ## `nnkProcDef` impls carry 7 children for a block/discard body and 8 for
  ## a bare-expression body (an implicit-`result` trailer past the fixed 7)
  ## — 7 is the floor observed across every shape probed, never a case
  ## below it. This is a defensive arity floor guarding the re-tree below,
  ## not a claim that 7 is the ONLY legal arity.

var methodRegistry {.compileTime.}: Table[string, seq[NimNode]]
  ## RFC-0005 S8bn (item 6). Per method name, the methods of that name
  ## visible where an entry macro was called. A macro cannot list a
  ## method's overrides (the dispatcher Nim builds is codegen's), and a
  ## `bindSym` resolves in the library's scope, not the caller's; so an
  ## entry macro whose SUT calls a method first emits, into the caller's
  ## scope, `symexRegisterMethods("<name>", <name>)`, whose argument the
  ## compiler resolves there to every overload of the name, and then
  ## expands again (`unregisteredMethodNames`).
var methodNamesTried {.compileTime.}: HashSet[string]
  ## RFC-0005 S8bn (item 6). The names an entry has registered (or found
  ## not visible), so a re-expansion ends.

macro symexRegisterMethods*(name: static string; overloads: typed): untyped =
  ## RFC-0005 S8bn (item 6). Record `overloads` (a symbol, or a choice of
  ## every overload visible at the call) as the methods named `name`.
  ## Emitted by the entry macros, never written by a user.
  methodNamesTried.incl name
  var syms: seq[NimNode]
  if overloads.kind == nnkSym: syms.add overloads
  else:
    for c in overloads:
      if c.kind == nnkSym: syms.add c
  for c in syms:
    if c.symKind == nskMethod:
      var seen = false
      for m in methodRegistry.getOrDefault(name):
        if m == c: seen = true
      if not seen: methodRegistry.mgetOrPut(name, @[]).add c
  newEmptyNode()

macro symexRegisterNoMethods*(name: static string): untyped =
  ## RFC-0005 S8bn (item 6). The method name `name` is not visible where
  ## the entry macro was called: its calls stay undispatched (declined).
  methodNamesTried.incl name
  newEmptyNode()

proc unregisteredMethodNames*(fn: NimNode): seq[string] =
  ## RFC-0005 S8bn (item 6). The names of the methods `fn` calls,
  ## transitively through the user routines it names and the overrides
  ## registered so far, that no entry has registered yet.
  var work: seq[NimNode]
  var seenR: seq[NimNode]
  if fn.kind == nnkSym: work.add fn
  for _, ms in methodRegistry:
    for m in ms: work.add m
  var i = 0
  proc scan(n: NimNode; acc: var seq[string]; work: var seq[NimNode]) =
    if n == nil: return
    if n.kind == nnkSym:
      if n.symKind == nskMethod:
        let nm = macros.strVal(n)
        if nm notin methodNamesTried and nm notin acc: acc.add nm
      elif isUserRoutine(n) and n.getImpl.kind != nnkNilLit:
        work.add n
      return
    for c in n: scan(c, acc, work)
  while i < work.len:
    let r = work[i]
    inc i
    var dup = false
    for x in seenR:
      if x == r: dup = true
    if dup: continue
    seenR.add r
    let impl = r.getImpl
    if impl.kind notin RoutineNodes or impl.len < 7: continue
    scan(impl[6], result, work)

var dispatchedMethods {.compileTime.}: seq[NimNode]
  ## RFC-0005 S8bn (item 6). The method symbols a dispatch on the run-type
  ## tag (`methodDispatchStmt`) calls: each is walked as the override it
  ## is, chosen for the receiver's dynamic type. Never cleared: an entry is
  ## a fact about a symbol.

proc resolveRoutineImpl*(sym: NimNode): NimNode =
  ## THE shared nil-core (RFC-parser-normalization Invariant-3's "one
  ## predicate"). `getImpl`s `sym`; returns the impl node when its kind is
  ## in `walkableRoutineKinds`, `nil` otherwise. This proc never raises and
  ## never degrades — it has no policy of its own. Every failure policy
  ## (hard-error, classified-degrade, boolean-false) is a wrapper written
  ## OVER this core; none of them is folded into it. `resolveEntryImpl`
  ## below is the hard-error wrapper; N2 threads the classified-degrade
  ## (`ensureProcRegistered`) and boolean-false (pragma/generics predicates)
  ## wrappers onto this same core.
  ##
  ## RFC-parser-normalization C1 (canonical routine kind at the boundary,
  ## confined entirely to this proc's body — the RFC's confinement
  ## invariant): an accepted `nnkFuncDef` impl is RE-TREED to `nnkProcDef`
  ## before being returned, so every downstream consumer — all of which
  ## read `impl` by fixed child index after this gate (N2's migration
  ## removed every other `impl.kind` branch in the file) — sees ONE
  ## canonical routine kind by construction, never a live `nnkFuncDef`.
  ##
  ## Evidence obligation (a) — layout identity (RFC C1): `func` and `proc`
  ## impls are shape-IDENTICAL at every child index for a given body shape
  ## — same arity, same per-index child KIND — differing only in whether
  ## index 4 (pragmas) is populated. Probe-verified 2026-08-14 across three
  ## body shapes (`scratchpad/probe_c1_dumptree2.nim`,
  ## `probe_c1_dumptree3.nim`): a bare-expression body (`func f(x:int):int =
  ## x+1`) yields 8 children (`Sym,Empty,Empty,FormalParams,Empty,Empty,
  ## Asgn,Sym` for `func`; identical but `Pragma` at index 4 for `proc
  ## {.noSideEffect.}`); a multi-statement body with explicit `return`
  ## yields the same 8-child pattern with `StmtList` at index 6; a `void`
  ## body yields 7 children (`...,Empty,Empty,DiscardStmt`) for BOTH kinds.
  ## `func` is sugar compiled through the identical routine-node
  ## constructor as `proc` — there is no real compiler output where the two
  ## diverge in shape. Re-treeing is therefore mechanical: `newTree` with
  ## the SAME child objects (no deep copy, no reconstruction), confirmed
  ## non-lossy by `scratchpad/probe_c1_retree.nim` (`retreed[i] == impl[i]`
  ## holds for every `i`; line info preserved via `copyLineInfo`).
  ##
  ## Deliberately unmemoized (Review finding L6, RFC #146): a `func` callee
  ## resolved from N call sites allocates N fresh `nnkProcDef` shells, one
  ## per call — memoization was considered and rejected. Caching the shell
  ## would hand the SAME `NimNode` to multiple consumers; since `NimNode` is
  ## a mutable reference, one consumer mutating its result would contaminate
  ## every other holder of the cached node. The fresh shell keeps aliasing
  ## scoped to each caller — children are shared (no deep copy, per the
  ## evidence above), but the shell itself is never shared — for negligible
  ## compile-time cost.
  ##
  ## Totality clause: an arity below `routineImplMinArity` deviates from
  ## every observed proc/func layout and is treated as unresolved (`nil`,
  ## the SAME degrade every other rejection path here already takes) rather
  ## than re-treed and returned malformed. Unreachable for real compiler
  ## output (documented above); no negative test is constructible without
  ## hand-building a synthetic `NimNode`, which is not real compiler output
  ## and so out of this proc's contract — the totality clause's own
  ## "real compiler output only" carve-out applies.
  ## Implementation note: the branches below deliberately test kind
  ## MEMBERSHIP (`notin walkableRoutineKinds`, `in {nnkFuncDef}`), never a
  ## bare `impl.kind == nnkProcDef`/`!= nnkFuncDef` comparison — the same
  ## house style N2's permanent audit test enforces everywhere else in this
  ## file (`tests/tsymex_phase15_N2_kindgate_audit.nim`), which this proc,
  ## as the nil-core those bare gates were migrated ONTO, is not exempt
  ## from.
  ##
  ## RFC-0005 S8c: a `converter` is re-treed the same way. It is a routine
  ## with a proc's exact layout, called statically like one (the compiler
  ## inserts it as `nnkHiddenCallConv` at an implicit conversion); once S8c
  ## routes user callees by symbol, a user converter reaches here and is
  ## walked instead of declined. A `method` is deliberately NOT: the
  ## resolved symbol names the base method, but the call dispatches on the
  ## receiver's dynamic type, so walking the base body would substitute one
  ## override for another -- it stays unresolved (a recorded callee decline).
  let impl = sym.getImpl
  # RFC-0005 S8bn (item 6): a method the dispatch selected for the
  # receiver's dynamic type is walked like a proc.
  var dispatched = false
  if impl.kind == nnkMethodDef:
    for m in dispatchedMethods:
      if m == sym: dispatched = true
  if impl.kind notin walkableRoutineKinds + {nnkConverterDef} and
     not dispatched:
    result = nil
  elif impl.kind in {nnkFuncDef, nnkConverterDef} or dispatched:
    if impl.len >= routineImplMinArity:
      var kids: seq[NimNode]
      for c in impl.children: kids.add c
      result = newTree(nnkProcDef, kids)
      result.copyLineInfo(impl)
    else:
      result = nil   ## totality clause: unreachable for real compiler output
  else:
    result = impl    ## already nnkProcDef

proc resolveEntryImpl*(fn: NimNode, apiName: string): NimNode =
  ## The hard-error policy wrapper over `resolveRoutineImpl`, used by every
  ## public entry macro that requires `fn` to resolve to a `proc`/`func`
  ## body. Named to avoid the codebase's load-bearing `target`/
  ## `SymexTarget` vocabulary (a round-1 draft of this RFC named it
  ## `parseEntryTarget`, which reintroduced exactly that collision).
  ##
  ## Error text is UNIFIED across all nine `symex.nim` entry macros
  ## (RFC-parser-normalization round-2 §Resolved forks F4 — deliberate,
  ## the one intentional behavior change in an otherwise behavior-identical
  ## slice): `symexForAll`'s historical `" for \`fn\`"` suffix is dropped.
  ## It disambiguated nothing — `symexForAll` has exactly one `typed`
  ## parameter, and `assertCoveredBy`, which has two, never carried a
  ## suffix at all — and no test or downstream harness depends on the
  ## exact compile-error text (pinned by `not compiles(...)` only).
  result = resolveRoutineImpl(fn)
  if result == nil:
    error(apiName & ": expected a `proc` symbol", fn)

# ---- emit: macro-time IR → runtime-construction NimNode -----------------------

proc emitBinop(op: IRBinop): NimNode =
  newDotExpr(bindSym"IRBinop", ident($op))

proc emitUnop(op: IRUnop): NimNode =
  newDotExpr(bindSym"IRUnop", ident($op))

proc emitIRType*(t: IRType): NimNode
proc emitStmt*(s: IRStmt): NimNode
proc emitParam(p: IRParam): NimNode     ## fwd: Phase 15 C1 (lambdaParams)

var globalTyCache {.compileTime.}: Table[string, IRType]

proc globalVarTy(name: string): IRType =
  ## RFC-0005 S8bw. The declared type of the module-level global `name`
  ## (`__gl:`-named), or nil for any other name or a global of a kind the
  ## walk holds no value for (a proc, a ref or ptr, an opaque type): a read
  ## of an unwritten global is a value of this type, where it was an `int`
  ## stand-in whatever the type (`gArr[2] = k` then faulted reading
  ## `gArr[2]`).
  if not isGlobalEnvName(name): return nil
  if globalTyCache.hasKey(name): return globalTyCache[name]
  let sym = globalSymOf(name)
  if sym != nil and sym.typeKind in {ntyBool, ntyChar, ntyEnum, ntyInt,
       ntyInt8, ntyInt16, ntyInt32, ntyInt64, ntyUInt, ntyUInt8, ntyUInt16,
       ntyUInt32, ntyUInt64, ntyFloat, ntyFloat32, ntyFloat64, ntyString,
       ntyArray, ntyTuple, ntyObject, ntySequence, ntyDistinct, ntyRange,
       ntyGenericInst}:
    result = classifyType(sym).ty
  globalTyCache[name] = result

proc emitExpr*(e: IRExpr): NimNode =
  case e.kind
  of iekIntLit:
    newCall(bindSym"mkIntLit", newLit(e.ival))
  of iekFloatLit:
    newCall(bindSym"mkFloatLit", newLit(e.fval), newLit(e.fwidth))
  of iekConvIntToFloat:
    newCall(bindSym"mkConvIntToFloat", emitExpr(e.convOperand), newLit(e.convWidth))
  of iekConvFloatToInt:
    newCall(bindSym"mkConvFloatToInt", emitExpr(e.convOperand), newLit(e.convWidth),
            newLit(e.convSigned), newLit(e.convHasRange), newLit(e.convLo),
            newLit(e.convHi))
  of iekConvIntWidth:
    newCall(bindSym"mkConvIntWidth", emitExpr(e.ciwOperand),
            newLit(e.ciwSrcWidth), newLit(e.ciwSrcSigned),
            newLit(e.ciwTgtWidth), newLit(e.ciwTgtSigned),
            newLit(e.ciwHasRange), newLit(e.ciwLo), newLit(e.ciwHi))
  of iekConvIntReinterpret:
    newCall(bindSym"mkConvIntReinterpret", emitExpr(e.cirOperand),
            newLit(e.cirWidth), newLit(e.cirTgtSigned))
  of iekMathCall:
    var argLit = newTree(nnkBracket)
    for a in e.mathArgs: argLit.add emitExpr(a)
    newCall(bindSym"mkMathCall", newLit(e.mathOp), prefix(argLit, "@"))
  of iekBoolLit:
    newCall(bindSym"mkBoolLit", newLit(e.bval))
  of iekVar:
    let gty = if e.vGlobalTy != nil: e.vGlobalTy else: globalVarTy(e.vname)
    if gty != nil:   # RFC-0005 S8bw
      newCall(bindSym"mkGlobalVar", newLit(e.vname), emitIRType(gty),
              newLit(e.vCopy))
    else:
      newCall(bindSym"mkVar", newLit(e.vname))
  of iekBinop:
    newCall(bindSym"mkBinop", emitBinop(e.bop), emitExpr(e.lhs), emitExpr(e.rhs))
  of iekUnop:
    newCall(bindSym"mkUnop", emitUnop(e.uop), emitExpr(e.operand))
  of iekBorrowOp:   ## Phase 15 G5
    newCall(bindSym"mkBorrowOp", emitBinop(e.borrowOp),
            emitExpr(e.borrowLhs), emitExpr(e.borrowRhs),
            newLit(e.borrowReturnsDistinct), emitIRType(e.borrowDistinctTy))
  of iekField:
    newCall(bindSym"mkField", emitExpr(e.obj),
            newLit(e.fieldIx), newLit(e.fieldName))
  of iekIndex:
    newCall(bindSym"mkIndex", emitExpr(e.arr), emitExpr(e.idx))
  of iekArrayLit:
    var lit = newTree(nnkBracket)
    for c in e.lelems: lit.add emitExpr(c)
    newCall(bindSym"mkArrayLit", prefix(lit, "@"), emitIRType(e.lelemTy))
  of iekTupleLit:
    var lit = newTree(nnkBracket)
    for c in e.telems: lit.add emitExpr(c)
    newCall(bindSym"mkTupleLit", prefix(lit, "@"), emitIRType(e.ttupleTy))
  of iekVariantLit:
    var armLit = newTree(nnkBracket)
    for c in e.vlArmFields: armLit.add emitExpr(c)
    var plainLit = newTree(nnkBracket)
    for c in e.vlPlainFields: plainLit.add emitExpr(c)
    newCall(bindSym"mkVariantLit", emitIRType(e.vlVariantTy),
            newLit(e.vlTagOrd), newLit(e.vlTagName),
            prefix(armLit, "@"), prefix(plainLit, "@"))
  of iekMultiVariantLit:
    var axesLit = newTree(nnkBracket)
    for fs in e.mvlAxisFields:
      var lit = newTree(nnkBracket)
      for c in fs: lit.add emitExpr(c)
      axesLit.add prefix(lit, "@")
    var plainLit = newTree(nnkBracket)
    for c in e.mvlPlainFields: plainLit.add emitExpr(c)
    let tagsLit = newTree(nnkBracket)
    for t in e.mvlAxisTags: tagsLit.add newLit(t)
    newCall(bindSym"mkMultiVariantLit", emitIRType(e.mvlTy),
            prefix(tagsLit, "@"), prefix(axesLit, "@"), prefix(plainLit, "@"))
  of iekVariantFieldSet:   ## RFC-0005 S8s
    let tagsLit = newTree(nnkBracket)
    for t in e.vfsTags: tagsLit.add newLit(t)
    newCall(bindSym"mkVariantFieldSet", emitExpr(e.vfsRecv),
            newLit(e.vfsFieldName),
            prefix(tagsLit, "@"),
            emitExpr(e.vfsVal))
  of iekSeqLen:
    newCall(bindSym"mkSeqLen", emitExpr(e.lenObj), newLit(e.lenLoc))
  of iekSeqSlice:
    newCall(bindSym"mkSeqSlice", emitExpr(e.ssBase),
            emitExpr(e.ssLo), emitExpr(e.ssHi), newLit(e.ssView))
  of iekSeqSplice:   ## RFC-0005 S8bu
    newCall(bindSym"mkSeqSplice", emitExpr(e.spBase),
            emitExpr(e.spAt), emitExpr(e.spPart))
  of iekStrLit:
    newCall(bindSym"mkStrLit", newLit(e.sval))
  of iekContains:
    newCall(bindSym"mkContains", emitExpr(e.container), emitExpr(e.key))
  of iekSeqAdd:
    newCall(bindSym"mkSeqAdd", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of iekSeqDel:
    newCall(bindSym"mkSeqDel", emitExpr(e.delSeq), emitExpr(e.delIdx),
            newLit(e.delShift))
  of iekSeqInsert:
    newCall(bindSym"mkSeqInsert", emitExpr(e.insSeq),
            emitExpr(e.insVal), emitExpr(e.insIdx), newLit(e.insGrow))
  of iekSeqPop:
    newCall(bindSym"mkSeqPop", emitExpr(e.popSeq))
  of iekTableSet:
    newCall(bindSym"mkTableSet", emitExpr(e.tabRecv),
            emitExpr(e.tabKey), emitExpr(e.tabVal))
  of iekTableDel:
    newCall(bindSym"mkTableDel", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of iekSetIncl:
    newCall(bindSym"mkSetIncl", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of iekSetExcl:
    newCall(bindSym"mkSetExcl", emitExpr(e.mutRecv), emitExpr(e.mutArg))
  of StrOpKinds:
    # Phase 15 Cluster S (S1). Re-emit a runtime-reconstructible string-op node:
    # `mkStrOp(kind, op, @[args], retTy)`. The kind is emitted through
    # `newLit` (a conversion via the enum type's symbol; RFC-0005 S8e).
    # Fix-slice item 5: `strRetTy` must round-trip too — an
    # `iekStrUnsupported` node reconstructed via the macro-emit path (rather
    # than built directly by the parser) would otherwise silently fall back
    # to `mkStrOp`'s `itString` default, losing a threaded int/bool/float
    # type and reintroducing the exact type-mismatch this fix closes.
    var argsLit = newTree(nnkBracket)
    for a in e.strArgs: argsLit.add emitExpr(a)
    newCall(bindSym"mkStrOp", newLit(e.kind), newLit(e.strOp),
            prefix(argsLit, "@"), emitIRType(e.strRetTy))
  of iekGetCurrentExn:    newCall(bindSym"mkGetCurrentExn")      ## Phase 15 E8
  of iekGetCurrentExnMsg: newCall(bindSym"mkGetCurrentExnMsg")   ## Phase 15 E8
  of iekLambda:           ## Phase 15 C1
    var paramsLit = newTree(nnkBracket)
    for p in e.lambdaParams: paramsLit.add emitParam(p)
    var capsLit = newTree(nnkBracket)
    for c in e.lambdaCaptures: capsLit.add newLit(c)
    var mutCapsLit = newTree(nnkBracket)     ## RFC-0005 S9
    for c in e.lambdaMutCaptures: mutCapsLit.add newLit(c)
    let lam = newCall(bindSym"mkLambda",
            newLit(e.lambdaSite.siteHash), newLit(e.lambdaSite.declOrder),
            prefix(paramsLit, "@"), emitStmt(e.lambdaBody),
            prefix(capsLit, "@"), emitIRType(e.lambdaRetTy),
            newTree(nnkExprEqExpr, ident"mutCaptures",
                    newCall(bindSym"@", mutCapsLit)))
    # RFC-0005 S8bh: the effect summary.
    var pairsLit = newTree(nnkBracket)
    for pr in e.lambdaAliasPairs:
      pairsLit.add newTree(nnkTupleConstr,
        newColonExpr(ident"keep", newLit(pr.keep)),
        newColonExpr(ident"gone", newLit(pr.gone)))
    var bodiesLit = newTree(nnkBracket)
    for b in e.lambdaAliasBodies: bodiesLit.add emitStmt(b)
    var plLit = newTree(nnkBracket)
    for b in e.lambdaPtrLocal: plLit.add newLit(b)
    var outerLit = newTree(nnkBracket)
    for o in e.lambdaOuter: outerLit.add newLit(o)
    newCall(bindSym"withLambdaEffects", lam,
            newCall(bindSym"@", pairsLit), newCall(bindSym"@", bodiesLit),
            newCall(bindSym"@", plLit), newCall(bindSym"@", outerLit))
  of iekClosureCall:      ## Phase 15 C1
    var argsLit = newTree(nnkBracket)
    for a in e.ccArgs: argsLit.add emitExpr(a)
    # RFC-0005 S8bh: the call's `var`/`addr` effects.
    var vtLit = newTree(nnkBracket)
    for t in e.ccVarTys:
      vtLit.add(if t.isNil: newCall(bindSym"IRType", newNilLit())
                else: emitIRType(t))
    var alLit = newTree(nnkBracket)
    for a in e.ccAlias: alLit.add newLit(a)
    var adLit = newTree(nnkBracket)
    for a in e.ccAddrArgs: adLit.add newLit(a)
    var tcLit = newTree(nnkBracket)
    for t in e.ccTouch: tcLit.add newLit(t)
    var vpLit = newTree(nnkBracket)        ## RFC-0005 S8bn
    for v in e.ccVarPtrSafe: vpLit.add newLit(v)
    # RFC-0005 S8bu: and `ccVarLocs`.
    newCall(bindSym"mkClosureCall", newLit(e.ccCallee), prefix(argsLit, "@"),
            newCall(bindSym"@", vtLit), newCall(bindSym"@", alLit),
            newCall(bindSym"@", adLit), newCall(bindSym"@", tcLit),
            newLit(e.ccVarLocs), newCall(bindSym"@", vpLit))
  of iekSeqLit:           ## Phase 15 C4
    var elemsLit = newTree(nnkBracket)
    for c in e.seqLitElems: elemsLit.add emitExpr(c)
    newCall(bindSym"mkSeqLit", prefix(elemsLit, "@"), emitIRType(e.seqLitElemTy))
  of iekHofCall:          ## Phase 15 C4
    let initArg = if e.hofInit != nil: emitExpr(e.hofInit)
                  else: newNilLit()
    newCall(bindSym"mkHofCall", newLit(e.hofOp), emitExpr(e.hofSeq),
            emitExpr(e.hofClosure), emitIRType(e.hofRetElemTy), initArg)
  of iekNil:              ## Phase 15 R5
    newCall(bindSym"mkNil", emitIRType(e.nilPointee))
  of iekZeroValue:        ## RFC-0005 S8u
    newCall(bindSym"mkZeroValue", emitIRType(e.zvTy))
  of iekSeqNew:           ## RFC-0005 S8bi
    newCall(bindSym"mkSeqNew", emitExpr(e.snArg), emitIRType(e.snElemTy),
            newLit(e.snZeroed), newLit(e.snOfCap))
  of iekBitSet:           ## RFC-0005 S8bq
    var args = newNimNode(nnkBracket)
    for a in e.bsArgs: args.add emitExpr(a)
    newCall(bindSym"mkBitSet", newLit(e.bsOp), prefix(args, "@"),
            emitIRType(e.bsSetTy))

proc emitIRType*(t: IRType): NimNode =
  # #163 review R27: `IRStmt.isAssign.aty` is nil at MOST call sites (the
  # target has no declared range, or isn't `itInt` at all) -- mirror
  # `emitStmt`'s own `s == nil` guard so a nil `aty` round-trips as `nil`
  # instead of crashing on `t.kind` here.
  if t == nil:
    return newNilLit()
  case t.kind
  of itBool:
    newCall(bindSym"tBool")
  of itString:
    newCall(bindSym"tString")
  of itUninterp:
    newCall(bindSym"tUninterp", newLit(t.uninterpName))
  of itFloat32: newCall(bindSym"tFloat32")
  of itFloat64: newCall(bindSym"tFloat64")
  of itDistinct:   ## Phase 15 G4: name + recursive base.
    newCall(bindSym"tDistinct", newLit(t.distinctName), emitIRType(t.distinctBase))
  of itRef:        ## Phase 15 R1a: ref + recursive pointee.
    newCall(bindSym"tRef", emitIRType(t.refPointeeTy))
  of itPtr:        ## Phase 15 R1a: ptr + recursive pointee.
    newCall(bindSym"tPtr", emitIRType(t.ptrPointeeTy))
  of itInt:
    # Issue #162: the declared bounds MUST round-trip through this emitted
    # call tree — exactly the trap `nominalId` documents just below. The
    # walker never sees the macro-time `IRType`, only the value rebuilt here,
    # so bounds left out here default to absent at runtime no matter what
    # `classifyType` computed, and a range-typed field goes unconstrained.
    let base = newCall(bindSym"tInt", newLit(t.width), newLit(t.signed))
    let ranged = if t.hasRange:
      newCall(bindSym"withRange", base, newLit(t.rangeLo), newLit(t.rangeHi))
    else:
      base
    # Issue #163 (rev item 1): `enumName` MUST round-trip the same way
    # `hasRange`/`rangeLo`/`rangeHi` do just above -- see this arm's own
    # comment. Left out here, an enum-typed slot's runtime-reconstructed
    # `IRType` would silently default `enumName = ""` regardless of what
    # `classifyType` computed, no matter what `symex.emitTyAndReader`
    # (which reads the macro-time `IRType` directly and needs no round trip
    # of its own) does with the name at witness-codegen time.
    if t.enumName.len > 0:
      newCall(bindSym"withEnumName", ranged, newLit(t.enumName))
    else:
      ranged
  of itTuple:
    var fieldsLit = newTree(nnkBracket)
    for f in t.fields:
      fieldsLit.add emitIRType(f)
    var namesLit = newTree(nnkBracket)
    for n in t.fieldNames:
      namesLit.add newLit(n)
    # Cluster H Step C fix: `nominalId` MUST round-trip through the runtime
    # reconstruction call — `refPointeeTypeId` (runtime_heap.nim) reads
    # `IRType.nominalId` at WALK time, and the walker only ever sees IRTypes
    # rebuilt via THIS emitted call tree (never the macro-time originals
    # directly). Before this fix `nominalId` silently defaulted to "" at
    # runtime regardless of what the macro-time classify computed, so
    # `refPointeeTypeId` ALWAYS fell back to the structural `$pointeeTy`
    # rendering — which differs between a bare ref's FULL-fielded pointee and
    # a recursive field's EMPTY-fielded placeholder (`namedRefPlaceholder`),
    # minting two DIFFERENT `Ref_<id>`/`nil_<id>` sorts for the same nominal
    # type (a same-type nil-comparison silently comparing against the WRONG
    # sort's nil const — the bug this fix closes).
    #
    # Cluster H H_witness fix: `isPlaceholder` NOW ALSO round-trips. The
    # comment here used to say `isPlaceholder`/`nameIsRefAlias` are consumed
    # ONLY by witness CODEGEN (`symex.nim`'s `emitTyAndReader`), which reads
    # the macro-time IRType directly and never needs the runtime
    # reconstruction — true for every consumer BEFORE H_witness.
    # `buildHeapSnapshot`'s recursive descent (`renderCell`, runtime.nim;
    # `resolveObjectFields` until RFC-0005 S8h) is the FIRST consumer that inspects `isPlaceholder` on a
    # WALK-TIME (runtime-reconstructed) `IRType` — a ref-typed FIELD's
    # pointee, reached via `heapSelect`/`liftHeapValue` at witness-extraction
    # time, is exactly one of these reconstructed nodes. Without this fix
    # every runtime-reconstructed `itTuple` silently defaulted
    # `isPlaceholder = false` (Nim's zero-value), so the snapshot
    # could never tell a genuine empty-fielded placeholder apart from a
    # PROVEN-EMPTY value type — it always took the "already full, don't
    # substitute" branch, permanently rendering a placeholder's `{}` empty
    # body instead of resolving the real nominal type. `nameIsRefAlias` stays
    # NOT threaded — still genuinely codegen-only, no walk-time reader needs it.
    var call = newCall(bindSym"tTuple", prefix(fieldsLit, "@"),
            prefix(namesLit, "@"), newLit(t.objectName), newLit(t.nominalId),
            newLit(t.isPlaceholder))
    # RFC-0005 S8bh (item 3): the hierarchy chain and the field owners key
    # the walker's sort and field heaps (`refPointeeTypeId`,
    # `fieldHeapKey`), so they round-trip -- passed only when present, so a
    # type declared without `of` emits the same call as before.
    proc strSeqLit(xs: seq[string]): NimNode =
      var b = newTree(nnkBracket)
      for x in xs: b.add newLit(x)
      prefix(b, "@")
    if t.inheritChain.len > 0:
      call.add newTree(nnkExprEqExpr, ident"inheritChain",
                         strSeqLit(t.inheritChain))
    if t.ownedFieldNames.len > 0:
      call.add newTree(nnkExprEqExpr, ident"ownedFieldNames",
                         strSeqLit(t.ownedFieldNames))
      call.add newTree(nnkExprEqExpr, ident"ownedFieldIds",
                         strSeqLit(t.ownedFieldIds))
    call
  of itArray:
    newCall(bindSym"tArray", emitIRType(t.elemTy), newLit(t.size))
  of itSeq:
    # Round-6 Bug #2 (B5 lesson: an unserialized field silently reverts to
    # its default across the macro round trip). `t.seqUnsupportedFieldReason`
    # must be threaded through explicitly, or every scoped-decline
    # placeholder built at classify time reverts to a plain (eagerly
    # unallocatable) `itSeq` the moment it reaches the RUNTIME-reconstructed
    # `IRType` — reintroducing Bug #2's crash at `allocateSym`.
    #
    # Round-6 re-review (item 3, walker v114): `t.seqUnsupportedFieldKind`
    # was NOT threaded — every round-tripped placeholder silently reverted
    # to `tUnsupportedFieldSeq`'s default `kind` (`seNestedSeqUnsupported`),
    # discarding an OPERATION-level origin's real classification (e.g.
    # `iekSeqAdd`'s own kind, N47-followup/walker-v110) the moment the IR
    # crossed the macro round trip — the exact "unserialized field silently
    # reverts to its default" class this arm's own comment warns about,
    # just for the sibling field. RFC-0005 S8e: emitted through `newLit`,
    # which writes an enum value as a conversion of its ordinal through the
    # enum type's SYMBOL (`SymexErrorKind(n)`); the bare member identifier it
    # replaced resolved by ordinary lookup at the CALLER's call site, where
    # the member may be undeclared or another symbol may hold its spelling.
    if t.seqUnsupportedFieldReason.len > 0:
      newCall(bindSym"tUnsupportedFieldSeq", emitIRType(t.seqElemTy),
              newLit(t.seqUnsupportedFieldReason),
              newLit(t.seqUnsupportedFieldKind))
    else:
      newCall(bindSym"tSeq", emitIRType(t.seqElemTy))
  of itTable:
    newCall(bindSym"tTable", emitIRType(t.tabKeyTy), emitIRType(t.tabValTy))
  of itSet:
    newCall(bindSym"tSet", emitIRType(t.setElemTy))
  of itBitSet:     ## RFC-0005 S8bq
    newCall(bindSym"tBitSet", emitIRType(t.bsElemTy))
  of itVariant:
    # Phase 11 cycle 3 + plain-field sharing — emit a runtime-
    # reconstructible IR literal for itVariant. Discriminator,
    # every arm's (tag ordinal + name + arm-specific fields),
    # plus the always-present plain field prefix.
    var armsLit = newTree(nnkBracket)
    for arm in t.vArms:
      var fieldNamesLit = newTree(nnkBracket)
      for n in arm.fieldNames: fieldNamesLit.add newLit(n)
      var fieldTypesLit = newTree(nnkBracket)
      for ft in arm.fieldTypes: fieldTypesLit.add emitIRType(ft)
      let armCons = nnkObjConstr.newTree(
        bindSym"VariantArm",
        nnkExprColonExpr.newTree(ident"tagOrdinal", newLit(arm.tagOrdinal)),
        nnkExprColonExpr.newTree(ident"tagName",    newLit(arm.tagName)),
        nnkExprColonExpr.newTree(ident"fieldNames", prefix(fieldNamesLit, "@")),
        nnkExprColonExpr.newTree(ident"fieldTypes", prefix(fieldTypesLit, "@")),
        nnkExprColonExpr.newTree(ident"branchIx",   newLit(arm.branchIx)),
        nnkExprColonExpr.newTree(ident"isElse",     newLit(arm.isElse)))
      armsLit.add armCons
    var plainNamesLit = newTree(nnkBracket)
    for n in t.vPlainFieldNames: plainNamesLit.add newLit(n)
    var plainTypesLit = newTree(nnkBracket)
    for ft in t.vPlainFieldTypes: plainTypesLit.add emitIRType(ft)
    var discTagsLit = newTree(nnkBracket)
    for dt in t.vDiscTags:
      discTagsLit.add nnkTupleConstr.newTree(
        nnkExprColonExpr.newTree(ident"name", newLit(dt.name)),
        nnkExprColonExpr.newTree(ident"ord",  newLit(dt.ord)))
    newCall(bindSym"tVariant",
      newLit(t.vObjectName), newLit(t.vDiscName),
      emitIRType(t.vDiscTy),
      prefix(armsLit, "@"),
      prefix(plainNamesLit, "@"),
      prefix(plainTypesLit, "@"),
      prefix(discTagsLit, "@"),
      newLit(t.vNominalId),   # RFC-0005 S8j: keys the `Ref_<id>` sort
      # RFC-0005 S8bn (item 8): a case-object hierarchy's chain and owners.
      newLit(t.vInheritChain), newLit(t.vOwnedFieldNames),
      newLit(t.vOwnedFieldIds))
  of itMultiVariant:
    # Phase 14 cycle A1a stub. Re-emit a runtime-reconstructible
    # `mkMultiVariant(…)` call. Full A1b (parser-side classification)
    # is what produces these IR values from Nim source; here we just
    # need round-trip emission of an already-built IR.
    var axesLit = newTree(nnkBracket)
    for ax in t.mvAxes:
      var armsLit = newTree(nnkBracket)
      for arm in ax.arms:
        var fieldNamesLit = newTree(nnkBracket)
        for n in arm.fieldNames: fieldNamesLit.add newLit(n)
        var fieldTypesLit = newTree(nnkBracket)
        for ft in arm.fieldTypes: fieldTypesLit.add emitIRType(ft)
        armsLit.add nnkObjConstr.newTree(
          bindSym"VariantArm",
          nnkExprColonExpr.newTree(ident"tagOrdinal", newLit(arm.tagOrdinal)),
          nnkExprColonExpr.newTree(ident"tagName",    newLit(arm.tagName)),
          nnkExprColonExpr.newTree(ident"fieldNames", prefix(fieldNamesLit, "@")),
          nnkExprColonExpr.newTree(ident"fieldTypes", prefix(fieldTypesLit, "@")),
          nnkExprColonExpr.newTree(ident"branchIx",   newLit(arm.branchIx)),
          nnkExprColonExpr.newTree(ident"isElse",     newLit(arm.isElse)))
      var discTagsLit = newTree(nnkBracket)
      for dt in ax.discTags:
        discTagsLit.add nnkTupleConstr.newTree(
          nnkExprColonExpr.newTree(ident"name", newLit(dt.name)),
          nnkExprColonExpr.newTree(ident"ord",  newLit(dt.ord)))
      axesLit.add nnkObjConstr.newTree(
        bindSym"VariantAxis",
        nnkExprColonExpr.newTree(ident"discName", newLit(ax.discName)),
        nnkExprColonExpr.newTree(ident"discTy",   emitIRType(ax.discTy)),
        nnkExprColonExpr.newTree(ident"arms",     prefix(armsLit, "@")),
        nnkExprColonExpr.newTree(ident"discTags", prefix(discTagsLit, "@")))
    var plainNamesLit = newTree(nnkBracket)
    for n in t.mvPlainFieldNames: plainNamesLit.add newLit(n)
    var plainTypesLit = newTree(nnkBracket)
    for ft in t.mvPlainFieldTypes: plainTypesLit.add emitIRType(ft)
    newCall(bindSym"mkMultiVariant",
      newLit(t.mvObjectName),
      prefix(axesLit, "@"),
      prefix(plainNamesLit, "@"),
      prefix(plainTypesLit, "@"),
      newLit(t.mvNominalId))   # RFC-0005 S8l: keys the `Ref_<id>` sort

proc emitBranch(br: IRBranch): NimNode =
  newCall(bindSym"mkBranch", emitExpr(br.cond), emitStmt(br.body))

proc emitExprSeq(xs: seq[IRExpr]): NimNode =
  var lit = newTree(nnkBracket)
  for x in xs:
    lit.add emitExpr(x)
  prefix(lit, "@")

proc emitIRTypeSeq(ts: seq[IRType]): NimNode =
  ## RFC-0005 S8ax. `emitExprSeq` for types (`IRStmt.opaqueHeapTys`).
  var lit = newTree(nnkBracket)
  for t in ts:
    lit.add emitIRType(t)
  prefix(lit, "@")

proc emitStmt*(s: IRStmt): NimNode =
  if s == nil:
    return newNilLit()
  case s.kind
  of isBlock:
    var seqLit = newTree(nnkBracket)
    for st in s.stmts:
      seqLit.add emitStmt(st)
    if s.blkLabel.len > 0:   # RFC-0005 S8m: a break target
      newCall(bindSym"mkLabelledBlock", newLit(s.blkLabel), prefix(seqLit, "@"))
    else:
      newCall(bindSym"mkBlock", prefix(seqLit, "@"))
  of isIf:
    var seqLit = newTree(nnkBracket)
    for br in s.branches:
      seqLit.add emitBranch(br)
    newCall(bindSym"mkIf", prefix(seqLit, "@"), emitStmt(s.elseBody),
            newLit(s.ifJoin))   ## RFC-0005 S8w
  of isLet:
    newCall(bindSym"mkLet", newLit(s.lname), emitIRType(s.lty), emitExpr(s.lvalue),
            newLit(s.lIsIntOffsetLocal))
  of isAssign:
    newCall(bindSym"mkAssign", newLit(s.aname), emitExpr(s.avalue),
            emitIRType(s.aty))
  of isWhile:
    newCall(bindSym"mkWhile", emitExpr(s.wcond), emitStmt(s.wbody),
            newLit(s.wHasAssumedBound))
  of isBreak:
    newCall(bindSym"mkBreak", newLit(s.brkLabel))
  of isContinue:
    newCall(bindSym"mkContinue")
  of isReturn:
    if s.retExpr == nil:
      newCall(bindSym"mkReturn")
    else:
      newCall(bindSym"mkReturnVal", emitExpr(s.retExpr))
  of isCall:
    if s.opaque:
      # #163 slice 4: `opaqueInert` MUST round-trip through this NimNode-
      # literal reconstruction — same trap `retIntOffsetPositions` documents
      # just below. The walker never sees this macro-time `IRStmt`, only the
      # value rebuilt from these `newCall` nodes at compile time; a field
      # omitted here silently reverts to `mkOpaqueCall`'s `inert = false`
      # default at runtime, and a test built on this arm stays red identically
      # to before the fix.
      newCall(bindSym"mkOpaqueCall",
              newLit(s.callee), newLit(s.retName),
              emitExprSeq(s.cargs), emitIRType(s.retTy),
              newLit(s.opaqueInert),
              newLit(s.opaqueHavoc),   ## RFC-0005 S8as, same trap
              emitIRTypeSeq(s.opaqueHeapTys),   ## RFC-0005 S8ax, same trap
              newLit(s.opaqueHeapAll),
              newLit(s.opaqueRaises),
              newLit(s.opaqueDefects),   ## RFC-0005 S8be
              newLit(s.opaqueWhy))
    else:
      # Round-6 B5: `retIntOffsetPositions` MUST round-trip through this
      # NimNode-literal reconstruction (the generated proc rebuilds the IR
      # from these `newCall` nodes at compile time — an IRStmt field the
      # emit arm doesn't serialize here is silently dropped, reverting to
      # `mkCall`'s `@[]` default regardless of what the parser computed).
      var posLit = newTree(nnkBracket)
      for pos in s.retIntOffsetPositions: posLit.add newLit(pos)
      # RFC-0005 S8an: `cGuardRoots` round-trips the same way; RFC-0005
      # S8bs: and `cVarLocs`.
      newCall(bindSym"mkCall",
              newLit(s.callee), newLit(s.retName),
              emitExprSeq(s.cargs), emitIRType(s.retTy),
              prefix(posLit, "@"), newLit(s.cGuardRoots),
              newLit(s.cVarLocs), newLit(s.cVarPtrSafe))   ## RFC-0005 S8bs, S8bn
  of isIndex:
    newCall(bindSym"mkIndexStmt",
            newLit(s.ixRetName), emitExpr(s.ixArr),
            emitExpr(s.ixIdx), emitIRType(s.ixElemTy), newLit(s.ixLoc),
            newLit(s.ixLo),   # RFC-0005 S8z
            newLit(s.ixCheckOnly))   # RFC-0005 S8bw
  of isIndexAssign:
    newCall(bindSym"mkIndexAssignStmt",
            newLit(s.iaRecvName), emitExpr(s.iaIdx),
            emitExpr(s.iaVal), newLit(s.iaLoc), newLit(s.iaLo))   # RFC-0005 S8z
  of isSeqPop:
    newCall(bindSym"mkSeqPopStmt",
            newLit(s.spRecvName), newLit(s.spRetName), newLit(s.spLoc),
            (if s.spElemTy.isNil: newNilLit() else: emitIRType(s.spElemTy)))
  of isTabKeys:   # RFC-0005 S8bc (item 6)
    newCall(bindSym"mkTabKeysStmt",
            newLit(s.tkRetName), emitExpr(s.tkRecv), emitIRType(s.tkKeyTy),
            newLit(s.tkLoc))
  of isSetLen:    # RFC-0005 S8bl (item 1)
    newCall(bindSym"mkSetLenStmt",
            newLit(s.slRetName), emitExpr(s.slBase), emitExpr(s.slLen),
            emitIRType(s.slTy), newLit(s.slLoc))
  of isVariantField:
    var tagsLit = newTree(nnkBracket)
    for t in s.vfMatchingTags: tagsLit.add newLit(t)
    newCall(bindSym"mkVariantFieldStmt",
            newLit(s.vfRetName), emitExpr(s.vfRecv),
            newLit(s.vfFieldName), emitIRType(s.vfFieldTy),
            prefix(tagsLit, "@"))
  of isVariantReassign:
    newCall(bindSym"mkVariantReassign",
            newLit(s.vrObjName), newLit(s.vrNewTag), newLit(s.vrTagName),
            newLit(s.vrBranches))
  of isVariantReassignSymbolic:
    newCall(bindSym"mkVariantReassignSymbolic",
            newLit(s.vrsObjName), newLit(s.vrsDiscName),
            emitExpr(s.vrsRhs), newLit(s.vrsBranches))
  of isVariantConstructSym:
    var tagsLit = newTree(nnkBracket)
    for t in s.vcsTagSet: tagsLit.add newLit(t)
    newCall(bindSym"mkVariantConstructSym",
            newLit(s.vcsResultVar), emitIRType(s.vcsVariantTy),
            emitExpr(s.vcsDiscExpr), prefix(tagsLit, "@"),
            emitExprSeq(s.vcsPlainFields), newLit(s.vcsLoc))
  of isAssert:
    newCall(bindSym"mkAssert", emitExpr(s.acond))
  of isAssume:
    newCall(bindSym"mkAssume", emitExpr(s.acond))
  of isTargetLabel:
    newCall(bindSym"mkTargetLabel", newLit(s.tname))
  of isRaise:
    if s.raiseIsReraise:
      newCall(bindSym"mkReraise")
    else:
      let msgNode = if s.raiseMsg == nil: newNilLit()
                    else: emitExpr(s.raiseMsg)
      newCall(bindSym"mkRaise", newLit(s.raiseTypeId), msgNode)
  of isTry:
    # Reconstruct the `seq[ExceptHandler]` literal, then the finally (nil-safe).
    var handlersLit = newTree(nnkBracket)
    for h in s.tryHandlers:
      var idsLit = newTree(nnkBracket)
      for tid in h.typeIds: idsLit.add newLit(tid)
      handlersLit.add nnkObjConstr.newTree(
        bindSym"ExceptHandler",
        nnkExprColonExpr.newTree(ident"typeIds", prefix(idsLit, "@")),
        nnkExprColonExpr.newTree(ident"body", emitStmt(h.body)))
    newCall(bindSym"mkTry", emitStmt(s.tryBody),
            prefix(handlersLit, "@"), emitStmt(s.tryFinally))
  of isDeref:   ## Phase 15 R1a: ref/ptr deref (ptr-family picks the ctor).
    if s.dField.len > 0:        ## Phase 15 R6: `p.field` field deref.
      newCall(bindSym"mkFieldDeref", newLit(s.dRetName), emitExpr(s.dPtr),
              emitIRType(s.dElemTy), emitIRType(s.dObjTy), newLit(s.dField),
              newLit(s.dPtrFamily))
    else:
      if s.dPtrFamily:
        newCall(bindSym"mkPtrDeref", newLit(s.dRetName), emitExpr(s.dPtr),
                emitIRType(s.dElemTy), newLit(s.dCell))   # RFC-0005 S8an
      else:
        newCall(bindSym"mkDeref", newLit(s.dRetName), emitExpr(s.dPtr),
                emitIRType(s.dElemTy))
  of isNew:     ## Phase 15 R1a: allocation.
    if s.nAddrIdx != nil:   # RFC-0005 S8be: an element cell
      newCall(bindSym"mkNewT", newLit(s.nRetName), emitIRType(s.nRefTy),
              newLit(s.nAddrOf), emitExpr(s.nAddrIdx))
    else:
      newCall(bindSym"mkNewT", newLit(s.nRetName), emitIRType(s.nRefTy),
              newLit(s.nAddrOf))   # RFC-0005 S8ax
  of isDerefWrite:   ## Phase 15 R3: heap write `p[] = v` (walker no-ops at R3).
    if s.dwField.len > 0:       ## Phase 15 R6: `p.field = v` field write.
      newCall(bindSym"mkFieldDerefWrite", emitExpr(s.dwPtr), emitExpr(s.dwValue),
              emitIRType(s.dwElemTy), emitIRType(s.dwObjTy), newLit(s.dwField),
              newLit(s.dwPtrFamily), newLit(s.dwInit))
    else:
      newCall(bindSym"mkDerefWrite", emitExpr(s.dwPtr), emitExpr(s.dwValue),
              emitIRType(s.dwElemTy), newLit(s.dwPtrFamily),
              newLit(s.dwCell))   # RFC-0005 S8an
  of isUnsupported:
    newCall(bindSym"mkUnsupported", newLit(s.unKind), newLit(s.reason),
            newLit(s.unMarker))
  of isUnsafeCast:
    newCall(bindSym"mkUnsafeCast", newLit(s.ucReason), newLit(s.ucMarker))

# ---- ParseCtx ----------------------------------------------------------------
#
# Threaded through the entire parse so that call discovery accumulates
# into a single `procs` table and synthesised temporaries get unique
# names.

type
  JumpTarget* = object
    ## RFC-0005 S8m. One construct a source `break` / `continue` can leave,
    ## on `ProcScopedCollectors.jumpTargets` (a lexical stack, innermost
    ## last) while its body is parsed.
    isLoop*: bool
    blockSym*: NimNode   ## a source block's label symbol (nil: unnamed / a loop)
    brkViaBlock*: bool
      ## A `break` leaves a labelled block: always for a block, and for a
      ## statically UNROLLED loop (no `isWhile` to leave). False: a plain
      ## `mkBreak()` leaves the walker's innermost `isWhile`.
    contViaBlock*: bool
      ## A `continue` leaves the per-iteration body block: a `for` loop,
      ## whose desugared increment follows the body, or an unrolled loop.
      ## False: the walker's own `continue`, back to the guard.
    brkLabel*: string    ## minted when a jump first names it; "" = unused
    contLabel*: string   ## likewise

  ProcScopedCollectors* = object
    ## D4 (design finding, accepted). Every field below is proc-scoped parse
    ## state: populated (via a pre-pass collector, or via ordinary push/pop
    ## during the body walk — `caseNarrow`'s own idiom) for whichever ONE
    ## proc body is currently being walked — the top-level entry via
    ## `parseProc*`, or a callee via `parseCalleeImpl` — and consulted only
    ## during THAT proc's own body walk. `ensureProcRegistered` saves this
    ## whole record, resets it to `ProcScopedCollectors()` (the zero value —
    ## every field's own `@[]`), and restores it in ONE assignment around a
    ## callee's recursive parse, so an ambient value from an enclosing proc
    ## can never leak into an unrelated callee's body (round-6 R4's W1
    ## cross-proc-leak finding, and ADR-0029's "does not cross proc
    ## boundaries" invariant for `caseNarrow`). Consolidated (pre-D4, each
    ## field got its own hand-written save/clear/restore triplet in
    ## `ensureProcRegistered`, on top of its own field decl, default init,
    ## entry-parse population site, and callee-parse recompute site — five
    ## touchpoints nothing enforced staying in sync) so a NEW proc-scoped
    ## collector joins the save/restore the moment it becomes a field HERE:
    ## there is no separate save/restore line for it to omit.
    jumpTargets*: seq[JumpTarget]
                                   ## RFC-0005 S8m. LEXICAL stack of the
                                   ## loops and blocks enclosing the
                                   ## statement being parsed (innermost
                                   ## last). `resolveBreak` /
                                   ## `resolveContinue` name the construct
                                   ## Nim leaves. Proc-scoped: a `break`
                                   ## never crosses a routine boundary.
    caseNarrow*: seq[tuple[subjectRepr: string, tags: seq[int]]]
                                   ## Round-6 A3 (ADR-0029). LEXICAL stack of
                                   ## `case`-branch tag-set narrowings, pushed
                                   ## by the `nnkCaseStmt` arm for each
                                   ## `nnkOfBranch` before parsing that arm's
                                   ## body statements and popped immediately
                                   ## after — a plain-`seq` stack, mirroring
                                   ## `parsing`'s push/pop-around-recursion
                                   ## idiom. `subjectRepr` is the scrutinee's
                                   ## `scopedRepr` (structural identity, each
                                   ## symbol by its scoped name -- RFC-0005
                                   ## S8e: `.repr` conflated a shadowing
                                   ## local with the outer scrutinee);
                                   ## `tags` is that branch's literal label
                                   ## ordinals. A symbolic-discriminant variant
                                   ## constructor consults the INNERMOST
                                   ## (last-pushed) entry whose `subjectRepr`
                                   ## matches its own discriminant expression's
                                   ## key. `ensureProcRegistered` SAVES,
                                   ## CLEARS, and RESTORES this stack (as part
                                   ## of the whole `ProcScopedCollectors`
                                   ## record) around a callee's recursive body
                                   ## parse — narrowing is parse-time/per-
                                   ## PROC-BODY only and must NEVER leak into a
                                   ## callee parsed mid-walk from inside a
                                   ## narrowed branch (ADR-0029's recorded
                                   ## "does not cross proc boundaries"
                                   ## boundary).
    stringBackedParams*: seq[NimNode]
                                   ## Round-6 B1 (ADR-0028 Leg 1); RE-KEYED
                                   ## round-6 R4 (findings W1/N8/N2). The
                                   ## Sym NODES (not name strings — see
                                   ## `containsSym`'s doc comment for why) of
                                   ## the TOP-LEVEL SUT's `seq[byte]` params
                                   ## the B1a scan-shape predicate recognized
                                   ## (minus any with a mutation site) —
                                   ## populated ONCE by
                                   ## `collectStringBackedByteSeqParams` in
                                   ## `parseProc*`, immediately after param
                                   ## classification and BEFORE the body walk
                                   ## (Leg 1's round-2 correction: the
                                   ## `iekStrSubstr`-vs-`iekSeqSlice` dispatch
                                   ## choice is baked into the IR the instant
                                   ## `parseExpr`'s bracket arm returns, so the
                                   ## deciding fact must exist BEFORE that
                                   ## call, not after). Computed FRESH for
                                   ## EVERY proc body about to be walked —
                                   ## the top-level entry via `parseProc*`,
                                   ## and (R4's W1 fix) each recursively-
                                   ## parsed CALLEE via `parseCalleeImpl`,
                                   ## scoped to that callee's own
                                   ## (monomorphized) body — but CONSULTED
                                   ## throughout that ONE proc's own body
                                   ## walk only. `ensureProcRegistered`
                                   ## SAVES and RESTORES this field (as part
                                   ## of the whole `ProcScopedCollectors`
                                   ## record) around a callee's recursive
                                   ## body parse, mirroring `caseNarrow`'s own
                                   ## proc-boundary discipline (a callee's
                                   ## own receivers must never inherit the
                                   ## CALLER's classification by accident);
                                   ## `parseCalleeImpl` then OVERWRITES it
                                   ## with the callee's own honest
                                   ## classification before walking that
                                   ## callee's body — simply clearing to
                                   ## `@[]` (caseNarrow's own idiom) is
                                   ## NOT sufficient here, since (unlike
                                   ## caseNarrow) nothing else repopulates
                                   ## this field during the ordinary
                                   ## recursive walk; TDD RED caught the
                                   ## regression a clear-only fix causes —
                                   ## a callee's OWN genuinely-qualifying
                                   ## scan/pair-loop receiver would silently
                                   ## lose the closed-form treatment
                                   ## (degrading to the k-unroll fallback)
                                   ## the moment it stopped being able to
                                   ## freeload off the entry's ambient leak.
                                   ## B7r's deliberate ONE-LEVEL CALL TRACE
                                   ## promotion is unaffected by any of
                                   ## this: it composes into the ENTRY
                                   ## proc's own computed value via a
                                   ## separate, purely-static NimNode-shape
                                   ## analysis (`collectStringBackedByteSeqParamsImpl`'s
                                   ## own recursion, gated by `visiting`),
                                   ## entirely independent of the ambient
                                   ## `ctx` field this scoping/recompute
                                   ## governs. Consulted via `containsSym`
                                   ## wherever a bracket/`.len`/`[]`-call
                                   ## receiver is a bare symbol.
    intOffsetLiteralLocals*: seq[NimNode]
                                   ## Round-6 B7r2 (walker v88); RE-KEYED
                                   ## round-6 R4 (findings W1/N8/N2). The
                                   ## Sym NODES (not name strings) of the
                                   ## TOP-LEVEL SUT's LOCAL `var`/`let`
                                   ## bindings whose initializer is a bare
                                   ## int literal AND which
                                   ## `collectIntOffsetLiteralLocals` traced
                                   ## to a recognized scan/pair-loop
                                   ## counter — the companion `collectIntOffsetParams`
                                   ## cannot cover (its own `findRootParam`
                                   ## only traces THROUGH a bare-symbol
                                   ## rebind of a formal param; a literal
                                   ## has no param to trace to). Populated
                                   ## ONCE by `collectIntOffsetLiteralLocals`
                                   ## in `parseProc*`, same site/scope as
                                   ## `stringBackedParams`, and scoped around
                                   ## callee recursion the SAME way (R4's
                                   ## W1 fix). Consulted via `containsSym` by
                                   ## the general `nnkVarSection`/`nnkLetSection`
                                   ## statement-parse arm to set
                                   ## `IRStmt.isLet.lIsIntOffsetLocal`. The
                                   ## re-keying closes N2's confirmed narrow
                                   ## variant: pre-R4, a same-proc, same-name
                                   ## COLLIDING local binding (a different
                                   ## scope's own `pos`/`i`/etc, never itself
                                   ## traced to a qualifying loop) inherited
                                   ## the classification via bare `strVal`
                                   ## membership; `containsSym` compares true
                                   ## symbol identity (R6's `sameSym`), so an
                                   ## unrelated same-named binding can never
                                   ## match.
    pairLoopCounterConsumedAfter*: seq[NimNode]
                                   ## Round-6 R5 (finding S4, walker v93). The
                                   ## Sym NODES (`containsSym` convention, same
                                   ## as `stringBackedParams`/
                                   ## `intOffsetLiteralLocals` above) of every
                                   ## B6 pair-loop's counter (`tryMatchPairLoopIdiomShape`'s
                                   ## own `iNode`) that `collectPairLoopCounterConsumedAfter`
                                   ## found referenced SOMEWHERE AFTER the loop
                                   ## in the SUT's own source. `tryRecognizePairLoopIdiom`'s
                                   ## member-branch replacement is an EMPTY
                                   ## block — the counter is never advanced —
                                   ## and NO single closed-form binding is
                                   ## faithful across every witness satisfying
                                   ## region membership (the canonical
                                   ## double-NUL-terminated shape exits via
                                   ## `break` with the counter at `bound - 1`;
                                   ## a region with no embedded empty-key
                                   ## segment exits with the counter at
                                   ## `bound` — genuinely data-dependent, no
                                   ## single formula covers both; see
                                   ## `collectPairLoopCounterConsumedAfter`'s
                                   ## own doc comment for the concrete
                                   ## counter-example). So the sound fix is
                                   ## NOT a binding — it is skipping the
                                   ## region-membership fast-path fork
                                   ## outright whenever the counter's
                                   ## post-loop value could be observed,
                                   ## using the SAME fold-omitted
                                   ## `mkShortCircuitWhile` k-unroll the
                                   ## non-member arm already builds as the
                                   ## loop's WHOLE replacement (genuinely
                                   ## per-iteration-correct, unlike falling
                                   ## through to the generic unrecognized-
                                   ## loop path, which would re-include the
                                   ## unwalkable fold statement — see
                                   ## `tryRecognizePairLoopIdiom`'s own R5
                                   ## comment for why that distinction
                                   ## matters). Populated ONCE by
                                   ## `collectPairLoopCounterConsumedAfter` in
                                   ## `parseProc*`, same site/scope/callee-
                                   ## recursion discipline as `stringBackedParams`
                                   ## (R4's W1 fix, applied here from the
                                   ## start rather than retrofitted) — a
                                   ## pair-loop can appear in a callee's own
                                   ## body too, not just the top-level entry.
    assumedBoundVars*: HashSet[string]
                                   ## N20 (RFC-chapulin-hardening bucket-2).
                                   ## Every variable name referenced by ANY
                                   ## `symexAssume(cond)` call anywhere in the
                                   ## proc currently being walked — populated
                                   ## ONCE by `collectAssumedBoundVars`, same
                                   ## population sites/scope as
                                   ## `stringBackedParams`. Consulted by
                                   ## `collectAssumedLoopBound` (via
                                   ## `mkShortCircuitWhile`) to mark a plain
                                   ## while-loop's `wHasAssumedBound` field —
                                   ## see `beBudgetExhaustedAssumedBound`'s
                                   ## own doc comment (types.nim) for the full
                                   ## mechanism. A HashSet[string] (name-keyed,
                                   ## not symbol-keyed like its siblings): this
                                   ## consumer is a deliberately coarse,
                                   ## purely-diagnostic heuristic (never a
                                   ## verdict lever), so the W1 cross-proc-leak
                                   ## precision `containsSym` exists for does
                                   ## not apply here — worst case a false-
                                   ## positive name match reports the softer
                                   ## classification one loop too often, never
                                   ## a wrong sat/unsat/raised verdict.

  ParseCtx* = ref object
    seqIndexRets*: HashSet[string]
                                   ## RFC-0005 S8be. The result names of the
                                   ## `isIndex` statements that read a `seq`
                                   ## element (not an array's or a table's):
                                   ## `orderOperands` checks such an index
                                   ## where Nim does and reads it late.
    indexConvPending*: bool
                                   ## RFC-0005 S8i. Set by the array-index
                                   ## parse for the one hidden conversion Nim
                                   ## wraps the index in (to the array's index
                                   ## type); consumed by the hidden-conversion
                                   ## arm, which then skips the RangeDefect
                                   ## range check -- Nim checks an index as an
                                   ## index (`IndexDefect`), which `isIndex`
                                   ## already forks.
    procs*:      Table[string, ProcSig]
    parsing*:    HashSet[string]   ## currently-being-parsed callees
                                   ## (cycle break for mutual recursion)
    keySyms*:    Table[string, NimNode]
                                   ## RFC-0005 S8an. The routine symbol each
                                   ## non-generic callee key was first
                                   ## registered for (`ensureProcRegistered`
                                   ## gives a different symbol of the same
                                   ## spelling -- an overload -- its own key).
    synthCounter*: int
    userExnHierarchy*: Table[string, string]
                                   ## Phase 15 E4a. child -> direct-parent
                                   ## links for USER-defined exception types,
                                   ## accumulated as raise/except type symbols
                                   ## are parsed. Threaded to WalkerStatics at
                                   ## parse completion.
    maxInstantiationsPerProc*: int
                                   ## Phase 15 G1c. Per-base-proc instantiation
                                   ## cap, threaded from the active
                                   ## `SymexSettings` at macro time. `0` =
                                   ## unlimited. Default 0 here; the macros set
                                   ## it from `settings.maxInstantiationsPerProc`.
    instCounts*: Table[string, int]
                                   ## Phase 15 G1c. Count of DISTINCT
                                   ## instantiations registered per BASE proc
                                   ## (keyed by the base identity — proc name +
                                   ## bodyHash — NOT the full instKey). Drives
                                   ## the per-proc cap check.
    parseErrors*: seq[SymexErrorInfo]
                                   ## Phase 15 G1c. Errors discovered during
                                   ## parse-time monomorphization (cap overflow
                                   ## → `geInstantiationCapped`). Emitted via
                                   ## `ParseResult` into `SymexProgram.parseErrors`
                                   ## and drained into the run's `errors`.
                                   ## RFC-0005 S8: written ONLY by the
                                   ## decline funnels (`declineAtSite`,
                                   ## `declineCallee`) -- each entry carries
                                   ## its `DeclineScope` (grep-pinned by
                                   ## `tests/tsymex_rfc0005_s8_scope.nim`).
    markerCounter*: int
                                   ## RFC-0005 S8 (§2.5 point 1). The last
                                   ## marker id minted (`nextMarker`); ids
                                   ## start at 1 and are unique per parse.
    annotationViolations*: seq[AnnotationViolation]
                                   ## RFC-0005 S8 (§13.3, i3). False user
                                   ## annotation claims found at call sites
                                   ## (`annotationViolation`) -- NOT declines,
                                   ## so never in `parseErrors`. Emitted via
                                   ## `ParseResult` onto
                                   ## `SymexProgram.annotationViolations`.
    lambdaCounter*: int
                                   ## Phase 15 Cluster C (C1, ADR-0009 D3). Monotone
                                   ## index of lambda declarations encountered
                                   ## during parse — the `declOrder` half of the
                                   ## lambda-site key, disambiguating two lambdas
                                   ## with identical bodies.
    activeIterators*: HashSet[string]
                                   ## A3 (ADR-0014 D2-0d). Iterator sym names
                                   ## currently being inlined. Guards against
                                   ## recursive/mutually-recursive iterators that
                                   ## would otherwise cause infinite compile-time
                                   ## recursion via getImpl re-entrancy (CRIT-3).
    inGuardCond*: bool
                                   ## RFC-parser-normalization A2a (D2, #146/
                                   ## #149). True for the duration of parsing a
                                   ## `while`-guard condition tree (set by
                                   ## `mkShortCircuitWhile`, shared by both
                                   ## `nnkWhileStmt` arms). Mechanism constraint
                                   ## 4's carve-out: `parseAtomicOperand` reads
                                   ## this and no-ops (plain `parseExpr`, no
                                   ## hoist) whenever it is set — a manufactured
                                   ## guard-cond preamble would flip R14's
                                   ## preamble-emptiness routing
                                   ## (`mkShortCircuitWhile`) and degrade
                                   ## `continue`-bearing loops that prove today.
    regexLetLiterals*: seq[tuple[sym: NimNode, flag, pattern: string]]
                                   ## RFC-0005 S8bq (item 3). Each `let r =
                                   ## re"..."` (or `rex`) whose pattern PCRE
                                   ## accepts: the symbol and its literal. A
                                   ## regex call given `r` reads the literal
                                   ## (`regexLiteralOfCtx`), exactly as if it
                                   ## had been written there: the constructor
                                   ## already ran, and a `let` cannot change.
    procScoped*: ProcScopedCollectors
                                   ## D4 (design finding, accepted). The four
                                   ## former individually-scoped collector
                                   ## fields (`caseNarrow`, `stringBackedParams`,
                                   ## `intOffsetLiteralLocals`,
                                   ## `pairLoopCounterConsumedAfter`), now
                                   ## grouped into one sub-record — see
                                   ## `ProcScopedCollectors`'s own doc comment
                                   ## (above, beside its type declaration) for
                                   ## the full rationale and the per-field doc
                                   ## comments preserved there.

proc newParseCtx*(maxInstantiationsPerProc = 0): ParseCtx =
  ## `procScoped`'s fields (`ProcScopedCollectors`, round-6 R4: `seq[NimNode]`
  ## members) default to `@[]` — no explicit init needed below (the record's
  ## own zero value, `ProcScopedCollectors()`, is exactly what a default
  ## `object` field on a `ref object` already gets).
  ParseCtx(procs: initTable[string, ProcSig](),
           parsing: initHashSet[string](),
           synthCounter: 0,
           userExnHierarchy: initTable[string, string](),
           maxInstantiationsPerProc: maxInstantiationsPerProc,
           instCounts: initTable[string, int](),
           activeIterators: initHashSet[string]())

# ---- RFC-0005 S8: the parse-time decline funnels ------------------------------
#
# §2.5: "Every site-anchored decline mints a marker node" -- and records its
# error in the SAME act, so the two cannot drift apart. Before S8 the 39
# `ctx.parseErrors.add` sites wrote the record and (mostly) a marker as two
# independent statements, which is how a site could record a decline with no
# marker at all (`geConceptViolation`, below) or mint a marker the record
# could not name. Now:
#   * `declineAtSite` -- a Class-A site: records `dskSiteAnchored(m)` AND
#     returns the `isUnsupported` marker `m` for the caller to place where
#     the substitution happens (a preamble, or as the statement itself);
#   * `declineMarker` -- a Class-B site: the marker alone (its reach record
#     is the walker's, under the same anchor, and is its only record; S8 kept
#     it that way because a parse-time error would have tripped the blanket
#     veto. RFC-0005 S9 deleted the veto; the verdict still needs no parse
#     record here -- reach taint decides it, and `reachJoinParseErrors`
#     would only ever keep such a record as a diagnostic);
#   * `declineUnsafeCast` -- the `isUnsafeCast` sibling of `declineAtSite`;
#   * `declineCallee` -- an unregistered-callee decline: records
#     `dskCalleeKey(key)` and returns the never-registered key for `mkCall`.
# Nothing else writes `ctx.parseErrors` (pinned). `parseProc` then checks
# every anchor against the EMITTED program (`placeDeclineScopes`): an anchor
# that did not survive into the IR the walker will walk is rescoped
# `dskUnplaced` (§2.5 point 4), where the S8 totality pin sees it.

proc nextMarker(ctx: ParseCtx): int =
  ## RFC-0005 S8. Mints the next marker id (1-based; 0 is never a parser id).
  inc ctx.markerCounter
  ctx.markerCounter

proc declineAtSite(ctx: ParseCtx; kind: SymexErrorKind; msg, reason: string):
    IRStmt =
  ## RFC-0005 S8 (§2.5 point 1). A Class-A decline: records the classified
  ## `sevError` (`msg`, the diagnostic) anchored at a fresh marker, and
  ## returns that marker (`isUnsupported(kind, reason)`) -- the caller MUST
  ## place it in the IR at the point of substitution (the walker taints and
  ## records every path that reaches it).
  let m = ctx.nextMarker()
  ctx.parseErrors.add SymexErrorInfo(kind: kind, severity: sevError, msg: msg,
                                     scope: siteAnchored(m))
  mkUnsupported(kind, reason, m)

proc declineMarker(ctx: ParseCtx; kind: SymexErrorKind; reason: string): IRStmt =
  ## RFC-0005 S8. A Class-B decline: a marker with no parse-time record (the
  ## walker's reach record, anchored at the same id, is its only record).
  ## Like every decline, it is reached only on a path an execution can take
  ## (S8bc's `pathInfeasible` drop in the walker's `isUnsupported` arm).
  mkUnsupported(kind, reason, ctx.nextMarker())

proc declineUnsafeCast(ctx: ParseCtx; msg, reason: string): IRStmt =
  ## RFC-0005 S8. `heUnsafeCast`'s `declineAtSite`: the marker is the
  ## `isUnsafeCast` node the walker halts on.
  let m = ctx.nextMarker()
  ctx.parseErrors.add SymexErrorInfo(kind: heUnsafeCast, severity: sevError,
                                     msg: msg, scope: siteAnchored(m))
  mkUnsafeCast(reason, m)

proc declineCallee(ctx: ParseCtx; kind: SymexErrorKind; msg,
                   key: string): string =
  ## RFC-0005 S8 (§2.5 point 3). An unregistered-callee decline: records the
  ## classified `sevError` anchored at the never-registered key and returns
  ## that key (`unregisteredCalleeKey(kind, key)`), which the caller hands to
  ## `mkCall`; the walker's missing-callee arm records its reach under the
  ## same key.
  let k = unregisteredCalleeKey(kind, key)
  ctx.parseErrors.add SymexErrorInfo(kind: kind, severity: sevError, msg: msg,
                                     scope: calleeKeyed(k))
  k

proc annotationViolation(ctx: ParseCtx; n: NimNode;
                         kind: AnnotationViolationKind; callee, msg: string) =
  ## RFC-0005 S8 (§13.3, i3). Records a false `{.symexTransparent.}` claim at
  ## call site `n`. Not a decline (see `AnnotationViolation`): the call's
  ## opaque fallback taints on its own at walk time.
  let li = n.lineInfoObj
  ctx.annotationViolations.add AnnotationViolation(
    pragma: saSymexTransparent, kind: kind, callee: callee,
    site: li.filename & ":" & $li.line & ":" & $li.column, msg: msg)

proc canonicalExnTypeSym(typeNode: NimNode): NimNode =
  ## RFC-0005 S8b. Resolve a type ALIAS to the type it names --
  ## `type MyErr = ArithmeticDefect`, or system's deprecated
  ## `DivByZeroError* = DivByZeroDefect` -- so an `except`/`raise` naming the
  ## alias gets the real type's id. Before S8b the alias's own name was the
  ## type id: known to neither table, and `isSubtypeOf` matched nothing, so
  ## `except MyErr` silently never caught the `DivByZeroDefect` it catches in
  ## Nim (a false `sxRaised`, no error recorded).
  ##
  ## In typed AST an `except` type is an `nnkType` node (verified: its
  ## `repr` is the written name, `typeKind` is `ntyAlias` for an alias, and
  ## `getTypeInst` is the written name's symbol); a `raise` names a symbol.
  ## An alias symbol's `getImpl` is a `TypeDef` whose body is the aliased
  ## type's bare symbol; a real object type's body is an `ObjectTy`/`RefTy`,
  ## where resolution stops. A node with no alias hop is returned unchanged,
  ## so every non-alias type id is exactly what it was.
  var cur = typeNode
  if cur.kind == nnkType:
    let inst =
      try: cur.getTypeInst
      except CatchableError: return typeNode
    if inst.kind != nnkSym: return typeNode
    cur = inst
  var hopped = false
  var guard = 0
  while cur.kind == nnkSym and guard < 64:
    inc guard
    let impl =
      try: cur.getImpl
      except CatchableError: break
    if impl.kind != nnkTypeDef or impl.len < 3 or impl[2].kind != nnkSym:
      break
    cur = impl[2]
    hopped = true
  if hopped: cur else: typeNode

proc collectUserExnAncestors(typeSym: NimNode, ctx: ParseCtx) =
  ## Phase 15 E4a. Walk `typeSym`'s inheritance chain via `getImpl`, recording
  ## each `child -> direct-parent` link into `ctx.userExnHierarchy`, until the
  ## chain reaches a type already in the static `exnTypeTable` (ValueError /
  ## IOError / Defect / …) or has no inherit clause (RootObj / non-object).
  ##
  ## Shape of `getImpl` for `type Child = object of Parent`:
  ##   TypeDef[ Sym "Child", Empty, ObjectTy[ Empty, OfInherit[ Sym "Parent" ],
  ##            <recList> ] ]  (RefTy/PtrTy may wrap the ObjectTy for `ref`).
  ##
  ## Only USER types are walked: a `typeSym` already known to the static table
  ## (a stdlib exn) needs no dynamic links. Cycles are guarded by a depth cap
  ## plus a "already recorded" check.
  if typeSym.kind notin {nnkSym, nnkIdent}:
    return
  var cur = typeSym
  var guard = 0
  while guard < 64:
    inc guard
    let childName = cur.strVal
    # A standard stdlib type terminates the walk (its static chain is known).
    if childName in exnTypeTable:
      return
    # Already captured this child: its chain is recorded — stop (cycle guard).
    if childName in ctx.userExnHierarchy:
      return
    let impl =
      try: cur.getImpl
      except CatchableError: return
    if impl.kind != nnkTypeDef or impl.len < 3:
      return
    # Locate the ObjectTy (possibly wrapped in Ref/PtrTy for `ref object`).
    var objTy = impl[2]
    while objTy.kind in {nnkRefTy, nnkPtrTy} and objTy.len > 0:
      objTy = objTy[0]
    if objTy.kind != nnkObjectTy or objTy.len < 1:
      return
    # The inherit clause is an `nnkOfInherit[ <parentSym> ]` child of the
    # ObjectTy (`ObjectTy[ <pragma|Empty>, OfInherit[Sym Parent], <recList> ]`).
    # A plain `nnkEmpty` in its place means no base (effectively `of RootObj`) —
    # end of chain. We scan the children for the OfInherit rather than assuming
    # a fixed index (the pragma slot shifts positions).
    var inheritNode: NimNode = nil
    for child in objTy:
      if child.kind == nnkOfInherit:
        inheritNode = child
        break
    if inheritNode == nil or inheritNode.len < 1:
      return
    var parent = inheritNode[0]
    while parent.kind in {nnkRefTy, nnkPtrTy, nnkBracketExpr} and parent.len > 0:
      parent = parent[0]
    if parent.kind notin {nnkSym, nnkIdent}:
      return
    let parentName = parent.strVal
    ctx.userExnHierarchy[childName] = parentName
    # If the parent is a known stdlib base, the static chain takes over.
    if parentName in exnTypeTable:
      return
    cur = parent

proc freshSynth(ctx: ParseCtx, prefixWord: string): string =
  inc ctx.synthCounter
  "__sym_" & prefixWord & "_" & $ctx.synthCounter

proc wholeObjectPointee(pointeeTy: IRType): bool =
  ## RFC-0005 S8ar. A `ref`/`ptr` pointee that is an object or named tuple
  ## with fields: `p[]` reads and `p[] = v` writes it field by field, the
  ## field heaps `p.f` uses. A placeholder (a recursive field's pointee) has
  ## no field list here, and an anonymous tuple no field names.
  ## RFC-0005 S8bs: the walker's address cells share the rule
  ## (`fieldSplitPointee`).
  fieldSplitPointee(pointeeTy)

# ---- RFC-0005 S8m: break / continue targets -----------------------------------
#
# Nim's `break` leaves the innermost enclosing `block` or loop, `break L`
# the block labelled `L`, and `continue` jumps to the innermost loop's next
# iteration, leaving every block in between (probed: `break inner` of a
# `block inner:` in a `while` leaves only the block; `break outer` out of two
# nested `for`s leaves both). Before S8m the parser flattened every `block`
# into its body and emitted a bare `break` / `continue` for every source
# one, which the walker applied to the innermost `isWhile`: `break outer`
# left only the inner loop (a false `sxSat` on the code after it), a
# `block`'s `break` left the enclosing loop, a `break` out of a top-level
# `block` or an unrolled array loop halted (`weBreakOutsideLoop`), and a
# `continue` in a `for` loop skipped the desugared increment, replaying the
# same iteration to the unroll bound. The parser now resolves each jump to
# the construct Nim leaves; a labelled `isBlock` is emitted only for a block
# some jump actually names, so the IR of every other program is unchanged.

proc pushJumpTarget(ctx: ParseCtx; isLoop: bool; blockSym: NimNode = nil;
                    brkViaBlock = false; contViaBlock = false) =
  ## `brkViaBlock` (a block, or an unrolled loop) / `contViaBlock` (a `for`
  ## loop or an unrolled one): the jump leaves a labelled block, minted on
  ## first use (`brkLabel` / `contLabel`), rather than the walker's loop.
  ctx.procScoped.jumpTargets.add JumpTarget(
    isLoop: isLoop, blockSym: blockSym,
    brkViaBlock: brkViaBlock or not isLoop, contViaBlock: contViaBlock)

proc popJumpTarget(ctx: ParseCtx): JumpTarget =
  ctx.procScoped.jumpTargets.pop()

proc wrapJumpBlock(label: string; body: IRStmt): IRStmt =
  ## The labelled block a jump named, or `body` unchanged when none did.
  if label.len == 0: body else: mkLabelledBlock(label, @[body])

proc sameBlockLabel(a, b: NimNode): bool =
  ## A `break L`'s label names its block by symbol (the typed AST), by
  ## spelling when either side is untyped.
  if a.kind == nnkSym and b.kind == nnkSym: a == b
  elif a.kind in {nnkSym, nnkIdent} and b.kind in {nnkSym, nnkIdent}:
    eqIdent(a, b)
  else: false

proc breakVia(ctx: ParseCtx; i: int): IRStmt =
  ## A `break` that leaves jump target `i`.
  template t: untyped = ctx.procScoped.jumpTargets[i]
  if not t.brkViaBlock: return mkBreak()      # the walker's innermost loop
  if t.brkLabel.len == 0: t.brkLabel = freshSynth(ctx, "brk")
  mkBreak(t.brkLabel)

proc resolveBreak(n: NimNode; ctx: ParseCtx): IRStmt =
  let label = if n.len > 0: n[0] else: newEmptyNode()
  if label.kind == nnkEmpty:
    if ctx.procScoped.jumpTargets.len == 0:
      return mkBreak()   # no enclosing loop: the walker's weBreakOutsideLoop
    return breakVia(ctx, ctx.procScoped.jumpTargets.high)
  for i in countdown(ctx.procScoped.jumpTargets.high, 0):
    # RFC-0005 S8x: read through the index, as `breakVia` and
    # `resolveContinue` do. In the compile-time VM a `let` of the element
    # aliases it, and `breakVia` mints `brkLabel` in that element in place.
    template t: untyped = ctx.procScoped.jumpTargets[i]
    if not t.isLoop and t.blockSym != nil and sameBlockLabel(t.blockSym, label):
      return breakVia(ctx, i)
  ctx.declineMarker(feUnsupportedStmtKind,
    "`break " & label.repr & "`: its block is not a modelled break target")

proc resolveContinue(ctx: ParseCtx): IRStmt =
  for i in countdown(ctx.procScoped.jumpTargets.high, 0):
    template t: untyped = ctx.procScoped.jumpTargets[i]
    if t.isLoop:
      if not t.contViaBlock: return mkContinue()
      if t.contLabel.len == 0: t.contLabel = freshSynth(ctx, "cont")
      return mkBreak(t.contLabel)
  mkContinue()   # no enclosing loop: the walker's weBreakOutsideLoop

# ---- RFC-0005 S8ay: `std/re` call recognition -------------------------------

const regexEntryNames = ["match", "find", "contains", "replace", "matchLen",
                         "findBounds", "findAll", "startsWith", "endsWith",
                         "split", "replacef", "multiReplace"]
  ## The `std/re` procs taking a `Regex` (the `=~` template expands to a
  ## `match` with a captures array).

proc isRegexTyped(a: NimNode): bool =
  ## `a` is a `std/re` `Regex` value (`ref RegexDesc`).
  if a.typeKind == ntyNone: return false
  let t = a.getTypeInst
  t.kind == nnkSym and t.strVal == "Regex"

proc regexLiteralOf(a: NimNode): (string, string) =
  ## RFC-0005 S8ay. `(flag, pattern)` of a `Regex` argument: flag `re` or
  ## `rex` for `re"..."` / `rex"..."` / `re("...")` / `rex("...")` whose
  ## flags are the defaults or `reStudy` / `reExtended` alone (PCRE_EXTENDED
  ## is the only one of them that changes what matches), else `?` -- a
  ## Regex value, a non-literal pattern, or a flag (`reIgnoreCase`,
  ## `reMultiLine`, `reDotAll`) the walker does not model.
  var x = a
  while x.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and x.len > 0:
    x = x[^1]
  if x.kind notin {nnkCallStrLit, nnkCall} or x.len < 2 or
     x[0].kind notin {nnkSym, nnkIdent} or x[0].strVal notin ["re", "rex"]:
    return ("?", "")
  var lit = x[1]
  while lit.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and lit.len > 0:
    lit = lit[^1]
  if lit.kind notin {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
    return ("?", "")
  var extended = x[0].strVal == "rex"   # the defaults: {reStudy} / +reExtended
  if x.len >= 3:
    var fl = x[2]
    while fl.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and fl.len > 0:
      fl = fl[^1]
    if fl.kind != nnkCurly: return ("?", "")
    extended = false
    for f in fl:
      if f.kind notin {nnkSym, nnkIdent}: return ("?", "")
      case f.strVal
      of "reStudy": discard
      of "reExtended": extended = true
      else: return ("?", "")
  ((if extended: "rex" else: "re"), lit.strVal)

proc regexCtorCall(n: NimNode): NimNode =
  ## RFC-0005 S8bq (item 3). `n` (under hidden conversions) when it is a
  ## call of `std/re`'s `re` / `rex` constructor -- `re"..."`
  ## (`nnkCallStrLit`), `re("...")`, `re(p)`, `rex(p, flags)` -- else nil.
  var x = n
  while x.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and x.len > 0:
    x = x[^1]
  if x.kind notin {nnkCallStrLit, nnkCall} or x.len < 2 or
     x[0].kind != nnkSym or x[0].strVal notin ["re", "rex"] or
     not isStdlibDecl(x[0]) or not isRegexTyped(x):
    return nil
  x

proc regexLiteralOfCtx(a: NimNode; ctx: ParseCtx): (string, string) =
  ## RFC-0005 S8bq (item 3). `regexLiteralOf`, and for a `let` symbol bound
  ## to an accepted literal (`ParseCtx.regexLetLiterals`), that literal.
  result = regexLiteralOf(a)
  if result[0] != "?": return
  var x = a
  while x.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and x.len > 0:
    x = x[^1]
  if x.kind == nnkSym and symKind(x) == nskLet:
    for e in ctx.regexLetLiterals:
      if e.sym == x: return (e.flag, e.pattern)

proc regexCapturesLvalue(n: NimNode): bool =
  ## RFC-0005 S8bb. A captures overload's `matches` lvalue whose location
  ## nothing in it can move: variables, fields, dereferences and indexes by
  ## a variable or literal. The call reads it into a copy and writes the
  ## copy back after the match (`parseAsgn`), which re-evaluates the lvalue;
  ## with no call or side effect in it, that is the location Nim wrote.
  case n.kind
  of nnkSym:
    symKind(n) in {nskVar, nskParam, nskTemp, nskForVar, nskResult}
  of nnkDotExpr:
    n.len == 2 and regexCapturesLvalue(n[0])
  of nnkHiddenDeref, nnkDerefExpr:
    n.len == 1 and regexCapturesLvalue(n[0])
  of nnkBracketExpr:
    n.len == 2 and regexCapturesLvalue(n[0]) and
      (n[1].kind in nnkCharLit..nnkUInt64Lit or
       (n[1].kind == nnkSym and symKind(n[1]) in {nskVar, nskLet, nskParam,
                                                  nskConst, nskForVar}))
  else: false

proc regexCallForks(e: IRExpr): bool =
  ## RFC-0005 S8ay. A regex call forks a raise of its own: `RegexError` for
  ## a pattern PCRE rejects, `RangeDefect` for a `start` outside int32 (Nim
  ## passes `start.cint`).
  ## RFC-0005 S8bi: every regex call is a raise site, not only the ones
  ## the reader has already found raising. A `Regex` value that is not a
  ## literal (`re(p)`) is built by the call's own evaluation and may raise
  ## `RegexError`, as may a pattern the reader leaves undecided
  ## (`psUnknown`); those lower to the `seUnsupportedRegex` decline, which
  ## taints the path. Counted as a carrier, the call took D1c's flat fast
  ## path and lowered whether or not the short circuit reached it, so a
  ## path on which Nim never runs it (`s.len > 3 and
  ## s.match(re"(*UTF8)a")` with a short `s`) was tainted too: `sxUnknown`
  ## for a reachable target. Which patterns raise is the lowering's to
  ## decide; the guard costs a valid one nothing but the guarded form.
  # RFC-0005 S8bb: a captures overload's group (`iekStrCaptureRe`) forks
  # nothing: it reads the call's own operands after the call.
  if e.kind notin {iekStrMatch, iekStrFindRe, iekStrReplaceRe,
                   iekStrUnsupported}:
    return false
  var op = e.strOp
  if op.startsWith("regex:"): op = op[6 .. ^1]
  elif e.kind == iekStrUnsupported: return false
  not decodeRegexSpec(op).entry.startsWith("capture")   # RFC-0005 S8bb

# ---- R16-2b: detect inline float→int conversions in RHS IR trees ------------

proc rhsHasInlineDefectFork(e: IRExpr): bool =
  ## Returns true iff `e` contains any node that produces an inline raise-fork
  ## when lowered, requiring the short-circuit guard even when rhsPreamble is empty.
  ## Covers:
  ##   iekConvFloatToInt — float→int conversion forks (R16-2b): an
  ##     out-of-range operand's continuation on a fresh value, and a `range`
  ##     target's RangeDefect (RFC-0005 S8g; a plain int target never raises).
  ##   iekBinop with op in {bDiv, bMod} — division/modulo may raise DivByZeroDefect
  ##     (R16-3). Only applies to the RHS of an `and`/`or` — a div in the LHS is
  ##     evaluated unconditionally, so its raise IS reachable without guarding.
  if e == nil: return false
  case e.kind
  of iekConvFloatToInt:
    result = true
  of iekConvIntToFloat:
    result = rhsHasInlineDefectFork(e.convOperand)
  of iekConvIntWidth:
    ## Round-6 B2: a pure widening extend has no inline raise fork of its
    ## own (unlike iekConvFloatToInt's RangeDefect bound) — only its operand
    ## can carry one. RFC-0005 S8i: a `range` target's check forks
    ## `RangeDefect`, as iekConvFloatToInt's does.
    result = e.ciwHasRange or rhsHasInlineDefectFork(e.ciwOperand)
  of iekConvIntReinterpret:
    ## A1 adjudication: a same-width tag flip has no inline raise fork of
    ## its own either — only its operand can carry one.
    result = rhsHasInlineDefectFork(e.cirOperand)
  of iekMathCall:
    for a in e.mathArgs:
      if rhsHasInlineDefectFork(a): return true
  of iekBinop:
    if e.bop in {bAdd, bSub, bMul, bDiv, bMod}: return true  ## R16-3/R16-4: arith → DivByZeroDefect/OverflowDefect guard
    result = rhsHasInlineDefectFork(e.lhs) or rhsHasInlineDefectFork(e.rhs)
  of iekUnop:
    # RFC-0005 S8g: a unary minus carries an overflow obligation
    # (`-low(T)` raises OverflowDefect), like the binary arithmetic ops.
    if e.uop == uNeg: return true
    result = rhsHasInlineDefectFork(e.operand)
  of iekField:
    result = rhsHasInlineDefectFork(e.obj)
  of iekIndex:
    result = rhsHasInlineDefectFork(e.arr) or rhsHasInlineDefectFork(e.idx)
  of iekArrayLit:
    for a in e.lelems:
      if rhsHasInlineDefectFork(a): return true
  of iekTupleLit:
    for a in e.telems:
      if rhsHasInlineDefectFork(a): return true
  of iekVariantLit:
    for a in e.vlArmFields:
      if rhsHasInlineDefectFork(a): return true
    for a in e.vlPlainFields:
      if rhsHasInlineDefectFork(a): return true
  of iekMultiVariantLit:
    for fs in e.mvlAxisFields:
      for a in fs:
        if rhsHasInlineDefectFork(a): return true
    for a in e.mvlPlainFields:
      if rhsHasInlineDefectFork(a): return true
  of iekVariantFieldSet:   ## RFC-0005 S8s
    result = rhsHasInlineDefectFork(e.vfsRecv) or
             rhsHasInlineDefectFork(e.vfsVal)
  of iekSeqLen:
    result = rhsHasInlineDefectFork(e.lenObj)
  of iekSeqSlice:
    # v67: a seq slice carries its own IndexDefect fork (the SND-4 OOB
    # deposit in its lowering; RFC-0005 S8g: and its RangeDefect) — always
    # guard-worthy on an and/or RHS.
    result = true
  of iekSeqSplice:   ## RFC-0005 S8bu: forks nothing of its own
    result = rhsHasInlineDefectFork(e.spBase) or
             rhsHasInlineDefectFork(e.spAt) or rhsHasInlineDefectFork(e.spPart)
  of iekContains:
    result = rhsHasInlineDefectFork(e.container) or rhsHasInlineDefectFork(e.key)
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    result = rhsHasInlineDefectFork(e.mutRecv) or rhsHasInlineDefectFork(e.mutArg)
  of iekSeqDel:
    # RFC-0005 S8g: `del` forks its own IndexDefect / RangeDefect.
    result = true
  of iekSeqInsert:
    # RFC-0005 S8ar: each phase of `insert` forks its own defect (the
    # grow phase RangeDefect, the place phase IndexDefect).
    result = true
  of iekSeqPop:
    result = rhsHasInlineDefectFork(e.popSeq)
  of iekTableSet:
    result = rhsHasInlineDefectFork(e.tabRecv) or
             rhsHasInlineDefectFork(e.tabKey) or
             rhsHasInlineDefectFork(e.tabVal)
  of iekStrAt, iekStrToInt:
    ## R1B (short-circuit OOB-guard fix): `iekStrAt` (SND-4, ADR-0024) deposits
    ## an inline OOB-defect fork into `strIndexOobConds` EVERY time it lowers
    ## (runtime_strings.nim `iekStrAt` arm), and `iekStrToInt` (S10b) likewise
    ## deposits an inline `ValueError` raise fork into `parseIntRaiseConds`
    ## (runtime_strings.nim `iekStrToInt` arm) every time it lowers. Both must
    ## SELF-REPORT true unconditionally — unlike the pure string ops below,
    ## these two nodes are themselves inline defect forks, not just carriers
    ## of forks in their sub-expressions. Without this, `A and s[i]==c` took
    ## D1c's FAST path (flat `mkBinop`), so the OOB fork fired UNGUARDED even
    ## when `A` (e.g. `i < s.len`) was false — a false `sxRaised(IndexDefect)`
    ## that real Nim's short-circuit evaluation never produces.
    result = true
  of iekStrSubstr:
    ## RFC-0005 S8g: a string SLICE (`s[a .. b]`, strOp "[]") forks its
    ## IndexDefect / RangeDefect like a seq slice; `substr` clamps and
    ## never raises, so it only carries its operands' forks.
    if e.strOp == "[]": return true
    for a in e.strArgs:
      if rhsHasInlineDefectFork(a): return true
  of iekStrLen, iekStrFind, iekStrRfind, iekStrContains,
     iekStrStartsWith, iekStrEndsWith, iekStrReplaceAll,
     iekStrSplit, iekStrJoin, iekStrMatch, iekStrFindRe, iekStrReplaceRe,
     iekStrCaptureRe,
     iekStrConcat, iekIntToStr, iekRadixFmt,
     iekStrUnsupported, iekStrToLower, iekStrToUpper, iekRuneToStr,
     iekStrStrip, iekStrInOptionRegion:
    if regexCallForks(e): return true   # RFC-0005 S8ay
    ## Round-6 B6: `iekStrInOptionRegion` is never reachable from ordinary
    ## and/or RHS surface syntax (it is synthesized only by
    ## `tryRecognizePairLoopIdiom`'s closed-form replacement, never parsed
    ## from a user expression) — grouped here with the other pure string
    ## ops for the same sound default: no self-fork, recurse into operands.
    for a in e.strArgs:
      if rhsHasInlineDefectFork(a): return true
  of iekBorrowOp:
    # RFC-0005 S8bi: a borrowed arithmetic operator is the base operator
    # (`lowerArith`), with its DivByZeroDefect / OverflowDefect forks.
    if e.borrowOp in {bAdd, bSub, bMul, bDiv, bMod}: return true
    result = rhsHasInlineDefectFork(e.borrowLhs) or
             rhsHasInlineDefectFork(e.borrowRhs)
  of iekClosureCall:
    # RFC-0005 S8as: a closure call is an effect of its own -- its body may
    # raise, and may write a capture or a global (`closureEnvWrites`). On
    # the right of `and`/`or` it runs only under the guard; evaluated
    # unconditionally, a raise or a write the short circuit skips happened
    # anyway.
    result = true
  of iekSeqLit:
    for a in e.seqLitElems:
      if rhsHasInlineDefectFork(a): return true
  of iekHofCall:
    # RFC-0005 S8as: it applies a closure (see `iekClosureCall`).
    result = true
  of iekSeqNew:
    # RFC-0005 S8bc, S8bi: its length guard forks in the preamble
    # (`parseNewSeqLen`), not here.
    result = rhsHasInlineDefectFork(e.snArg)
  of iekBitSet:
    # RFC-0005 S8bq: a set operation never raises; an element's range
    # check is its own (conversion) node.
    for a in e.bsArgs:
      if rhsHasInlineDefectFork(a): return true
  of iekLambda:
    discard  # lambdaBody is IRStmt; don't recurse into lambdas
  of iekIntLit, iekFloatLit, iekBoolLit, iekVar, iekStrLit,
     iekGetCurrentExn, iekGetCurrentExnMsg, iekNil, iekZeroValue:
    discard  # no sub-exprs

# ---- RFC-0005 S8ax: an operand and a later operand's call -------------------
#
# Nim (2.2.10, c and cpp alike) evaluates a routine call, and an overflow-
# checked `+`/`-`/`*`, where it stands, into a temporary; every other operand
# shape -- a variable, a field, an element, a dereference, a conversion, a
# comparison, a bit operation, `-x`, `x div y`, `len` -- is an inline C
# expression, read when its enclosing operation is, after the calls of every
# later operand. Its checks (an index's bound, `-x`'s and `div`'s overflow
# and zero divisor) are statements emitted where it stands. A constructor
# (`[..]`, `@[..]`, `(..)`, `T(..)`) fills its elements in order. Probed:
#
#   var x = 1; proc g(): int = (x = 10; 0)
#   x + g() == 10        x.a + g() == 10 (value field)   int(y) + g() == 10
#   (x * 1) + g() == 1   succ(x) + g() == 2              (x and 7) + g(): late
#   [x, g()][0] == 1     (x, g())[0] == 1   @[x, g()][0] == 1   T(a: x, ..) 1
#   -x + g() == -10, but with x == low(int) before g() it raises
#   s[i] + g() with g() moving i out of bounds reads past the end, no raise
#   k(x + 0, g()) == 100 (k(a, b) = a * 100 + b), k(x, g()) == 1000
#
# The parser hoists a compound operator operand into a `let` where it stands
# (`parseAtomicOperand`) and leaves a call argument inline (read at the
# call), so each disagreed with Nim somewhere: a lazy operand hoisted early,
# an eager call argument read late, a constructor element read late. The
# walk reads a value where `orderOperands` places it.

proc irKids(e: IRExpr): seq[IRExpr] =
  ## RFC-0005 S8ax. The sub-expressions of `e`.
  if e == nil: return @[]
  case e.kind
  of iekConvIntToFloat, iekConvFloatToInt: @[e.convOperand]
  of iekConvIntWidth: @[e.ciwOperand]
  of iekConvIntReinterpret: @[e.cirOperand]
  of iekMathCall: e.mathArgs
  of iekBinop: @[e.lhs, e.rhs]
  of iekUnop: @[e.operand]
  of iekField: @[e.obj]
  of iekIndex: @[e.arr, e.idx]
  of iekArrayLit: e.lelems
  of iekTupleLit: e.telems
  of iekVariantLit: e.vlArmFields & e.vlPlainFields
  of iekMultiVariantLit:
    var r: seq[IRExpr]
    for fs in e.mvlAxisFields: r.add fs
    r & e.mvlPlainFields
  of iekVariantFieldSet: @[e.vfsRecv, e.vfsVal]
  of iekSeqLen: @[e.lenObj]
  of iekSeqSlice: @[e.ssBase, e.ssLo, e.ssHi]
  of iekSeqSplice: @[e.spBase, e.spAt, e.spPart]   ## RFC-0005 S8bu
  of iekContains: @[e.container, e.key]
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel: @[e.mutRecv, e.mutArg]
  of iekSeqDel: @[e.delSeq, e.delIdx]
  of iekSeqInsert: @[e.insSeq, e.insVal, e.insIdx]
  of iekSeqPop: @[e.popSeq]
  of iekTableSet: @[e.tabRecv, e.tabKey, e.tabVal]
  of iekStrLen, iekStrAt, iekStrSubstr, iekStrFind, iekStrRfind,
     iekStrContains, iekStrStartsWith, iekStrEndsWith, iekStrReplaceAll,
     iekStrSplit, iekStrJoin, iekStrMatch, iekStrFindRe, iekStrReplaceRe,
     iekStrConcat, iekIntToStr, iekStrToInt, iekRadixFmt, iekStrUnsupported,
     iekStrToLower, iekStrToUpper, iekRuneToStr, iekStrStrip,
     iekStrInOptionRegion, iekStrCaptureRe:
    e.strArgs
  of iekBorrowOp: @[e.borrowLhs, e.borrowRhs]
  of iekClosureCall: e.ccArgs
  of iekSeqLit: e.seqLitElems
  of iekHofCall: @[e.hofSeq, e.hofClosure, e.hofInit]
  of iekSeqNew: @[e.snArg]   # RFC-0005 S8bc, S8bi (batch 5: one kind)
  of iekBitSet: e.bsArgs     # RFC-0005 S8bq (batch 6)
  of iekLambda, iekIntLit, iekFloatLit, iekBoolLit, iekVar, iekStrLit,
     iekGetCurrentExn, iekGetCurrentExnMsg, iekNil, iekZeroValue:
    @[]

proc irHasCall(e: IRExpr): bool =
  ## RFC-0005 S8ax. `e` applies a closure somewhere (`iekClosureCall`,
  ## `iekHofCall`): lowering it may write a capture or a global.
  if e == nil: return false
  if e.kind in {iekClosureCall, iekHofCall}: return true
  for k in irKids(e):
    if irHasCall(k): return true
  false

proc irVars(e: IRExpr; acc: var seq[string]) =
  ## RFC-0005 S8ax. The variables `e` reads, added to `acc`.
  if e == nil: return
  if e.kind == iekVar:
    if e.vname notin acc: acc.add e.vname
    return
  for k in irKids(e): irVars(k, acc)

func isSynthName(nm: string): bool = nm.startsWith("__sym_")
  ## RFC-0005 S8ax. A parser temporary (`freshSynth`): bound once, written
  ## by no call.

proc stmtMayWrite(s: IRStmt): bool =
  ## RFC-0005 S8ax. Running `s` may change a value an earlier operand of the
  ## same expression reads: it calls a routine or a closure, or assigns
  ## something other than a parser temporary. A read, a check, an
  ## allocation or a decline marker does not.
  if s == nil: return false
  case s.kind
  of isLet: irHasCall(s.lvalue)
  of isAssign: not isSynthName(s.aname) or irHasCall(s.avalue)
  of isDeref: irHasCall(s.dPtr)
  of isIndex: irHasCall(s.ixArr) or irHasCall(s.ixIdx)
  of isVariantField: irHasCall(s.vfRecv)
  of isNew, isUnsupported: false
  of isBlock:
    for c in s.stmts:
      if stmtMayWrite(c): return true
    false
  of isIf:
    for b in s.branches:
      if irHasCall(b.cond) or stmtMayWrite(b.body): return true
    stmtMayWrite(s.elseBody)
  else: true

func isEagerIR(e: IRExpr): bool =
  ## RFC-0005 S8ax. Nim evaluates `e` where it stands, into a temporary: a
  ## closure application, or an overflow-checked `+`/`-`/`*` (`succ`/`pred`
  ## are parsed as one), or a string operation (a routine call in Nim). Any
  ## other shape is an inline expression Nim reads with its enclosing
  ## operation.
  if e == nil: return false
  case e.kind
  of iekClosureCall, iekHofCall, iekMathCall: true
  of iekBinop: e.bop in {bAdd, bSub, bMul}
  of iekStrSubstr, iekStrFind, iekStrRfind, iekStrContains, iekStrStartsWith,
     iekStrEndsWith, iekStrReplaceAll, iekStrSplit, iekStrJoin, iekStrMatch,
     iekStrFindRe, iekStrReplaceRe, iekStrCaptureRe, iekStrConcat,
     iekIntToStr, iekStrToInt, iekRadixFmt, iekStrUnsupported,
     iekStrToLower, iekStrToUpper, iekRuneToStr, iekStrStrip, iekStrInOptionRegion, iekSeqSlice,
     iekSeqSplice,   # RFC-0005 S8bu
     iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel, iekSeqDel,
     iekSeqInsert, iekSeqPop, iekTableSet, iekContains, iekBorrowOp,
     iekSeqNew:   # RFC-0005 S8bc, S8bi: `newSeq[T](n)` and kin, a call
    true
  else: false

func isLiteralIR(e: IRExpr): bool =
  e == nil or e.kind in {iekIntLit, iekFloatLit, iekBoolLit, iekStrLit,
                         iekNil, iekZeroValue, iekLambda}

proc lazyStmt(s: IRStmt): bool =
  ## RFC-0005 S8ax. `s` is part of an inline (lazy) operand: a read
  ## (`isDeref`, `isIndex`, `isVariantField`) or a temporary bound to a
  ## lazy expression.
  case s.kind
  of isDeref, isIndex, isVariantField: not stmtMayWrite(s)
  of isLet: isSynthName(s.lname) and not isEagerIR(s.lvalue) and
            not irHasCall(s.lvalue)
  else: false

proc lazyChecked(s: IRStmt): bool =
  ## RFC-0005 S8ax. Running the lazy statement `s` checks something Nim
  ## checks where the operand stands (a bound, a field's arm, an overflow,
  ## a zero divisor): it cannot simply be moved after a later call.
  case s.kind
  of isIndex, isVariantField: true
  of isLet: rhsHasInlineDefectFork(s.lvalue)
  else: false

type OrderMode = enum
  omOperands      ## an operator's operands or a call's arguments
  omElements      ## a constructor's elements, filled in order

func plainIR(e: IRExpr): bool =
  ## RFC-0005 S8be. A variable or a literal: reading it checks nothing.
  e != nil and (e.kind == iekVar or isLiteralIR(e))

proc collectStrAts(e: IRExpr; acc: var seq[IRExpr]): bool =
  ## RFC-0005 S8be. True when every check `e` makes inline is a string
  ## index (`s[i]` of a plain string and index), collected into `acc`.
  if e == nil: return true
  case e.kind
  of iekStrAt:
    if e.strArgs.len != 2 or not plainIR(e.strArgs[0]) or
       not plainIR(e.strArgs[1]):
      return false
    acc.add e
    true
  of iekConvIntWidth:
    not e.ciwHasRange and collectStrAts(e.ciwOperand, acc)
  of iekConvIntReinterpret: collectStrAts(e.cirOperand, acc)
  else: not rhsHasInlineDefectFork(e)

proc splitIndexChecks(seg: seq[IRStmt]; cut: int; ir: IRExpr;
                      ctx: ParseCtx; early, tail: var seq[IRStmt]): bool =
  ## RFC-0005 S8be. Nim checks a `seq` or string index where the operand
  ## stands and reads the element with the enclosing operation, after a
  ## later operand's call (probed on c and cpp: `int(s[i]) + f()` where `f`
  ## replaces `s` reads the new string's element, and raises `IndexDefect`
  ## against the old one). When the only checks among the trailing lazy
  ## statements `seg[cut ..]` and the inline operand `ir` are such indices,
  ## each is checked into `early` (a read into a temporary the walk
  ## discards), and the reads move to `tail`. A read the check no longer
  ## covers -- its index variable changed, or the element is past the
  ## container's new end -- is undefined in Nim (an unchecked read), and
  ## declines (`feEvalOrderUnmodelled`). Before S8be every such operand
  ## declined when a later call wrote anything it read.
  var strAts: seq[IRExpr]
  var defined: seq[string]
  for i in cut ..< seg.len:
    let st = seg[i]
    case st.kind
    of isIndex:
      if st.ixRetName notin ctx.seqIndexRets or not plainIR(st.ixArr) or
         not plainIR(st.ixIdx):
        return false
      defined.add st.ixRetName
    of isLet:
      # A temporary bound to the operand's inline read (`int(s[i])`).
      if not collectStrAts(st.lvalue, strAts): return false
      defined.add st.lname
    else: return false
  if ir.kind != iekVar and not collectStrAts(ir, strAts): return false
  # The checks run before the trailing statements, so they may read none
  # of their results.
  var reads: seq[string]
  for i in cut ..< seg.len:
    if seg[i].kind == isIndex:
      irVars(seg[i].ixArr, reads)
      irVars(seg[i].ixIdx, reads)
  for e in strAts:
    for a in e.strArgs: irVars(a, reads)
  for nm in reads:
    if nm in defined: return false
  var sites: seq[tuple[idx, len: IRExpr]]
  var checks: seq[IRStmt]
  for i in cut ..< seg.len:
    let st = seg[i]
    if st.kind != isIndex: continue
    checks.add mkIndexStmt(freshSynth(ctx, "ordchk"), st.ixArr, st.ixIdx,
                          st.ixElemTy, st.ixLoc, st.ixLo)
    sites.add (st.ixIdx, mkSeqLen(st.ixArr))
  for e in strAts:
    checks.add mkLet(freshSynth(ctx, "ordchk"), nil, e)
    sites.add (e.strArgs[1], mkStrOp(iekStrLen, "len", @[e.strArgs[0]]))
  if sites.len == 0: return false
  var unchecked: IRExpr = nil
  template orIn(d: IRExpr) =
    unchecked = if unchecked == nil: d else: mkBinop(bOr, unchecked, d)
  for (idx, ln) in sites:
    if idx.kind == iekVar and not isSynthName(idx.vname):
      let snap = freshSynth(ctx, "ordsnap")
      early.add mkLet(snap, nil, mkVar(idx.vname))
      orIn mkBinop(bNe, mkVar(idx.vname), mkVar(snap))
    orIn mkBinop(bGe, idx, ln)
  early.add checks
  tail.add mkIf(@[mkBranch(unchecked, mkBlock(@[ctx.declineMarker(
    feEvalOrderUnmodelled,
    "an index Nim checked where the operand stands is read after a later " &
    "operand's call that moved it past the container's end or changed it: " &
    "an unchecked read, undefined in Nim (feEvalOrderUnmodelled)")]))])
  for i in cut ..< seg.len: tail.add seg[i]
  true
type LateAddr = object
  ## RFC-0005 S8bk. Where a by-address argument's lvalue was lowered
  ## (`userCallStmt`): its address and value reads are
  ## `preamble[lo ..< hi]`, and the statements that bind them for the call
  ## (a copy-in temporary, S8an's cell) `preamble[hi ..< bindEnd]`.
  ## `growable[j]` is true when the container of the `j`-th index on the
  ## lvalue's path (root first) is not an array, so that its length may
  ## change (`lvalueIndexGrowable`). `ok` is false for an argument without
  ## one (a variable, a cell shared with an earlier `addr`).
  ok: bool
  lo, hi, bindEnd: int
  growable: seq[bool]

proc lvalueIndexGrowable(lv: NimNode): seq[bool] =
  ## RFC-0005 S8bk. For each index on the lvalue path `lv`, root first:
  ## whether its container is anything but an array (a seq, a string),
  ## whose length a later call may change.
  var t = lv
  var rev: seq[bool]
  while true:
    if t.kind != nnkSym and t.len == 0 and byRefName(t).len > 0: break
    case t.kind
    of nnkBracketExpr:
      if t.len == 0: break
      rev.add(t[0].typeKind != ntyArray)
      t = t[0]
    of nnkDotExpr, nnkCheckedFieldExpr, nnkHiddenAddr, nnkAddr,
       nnkDerefExpr, nnkHiddenDeref:
      if t.len == 0: break
      t = t[0]
    of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv:
      if t.len == 0: break
      t = t[^1]
    else: break
  for k in countdown(rev.high, 0): result.add rev[k]

proc stmtDefines(s: IRStmt): string =
  ## RFC-0005 S8bk. The name a lazy read statement binds.
  case s.kind
  of isLet: s.lname
  of isIndex: s.ixRetName
  of isVariantField: s.vfRetName
  of isDeref: s.dRetName
  else: ""

proc placeLateAddr(seg: seq[IRStmt]; la: LateAddr; base: int;
                   outPre, tail: var seq[IRStmt]; ctx: ParseCtx) =
  ## RFC-0005 S8bk. A by-address argument (`var` / `addr` / by reference)
  ## that a later argument's call may write past. Nim takes its address AT
  ## THE CALL, after every later argument (`T1_ = moveP(); touch(&(*gP).x,
  ## T1_)`): the callee reads and writes the cell the lvalue names then.
  ## Only the address's checks -- an index's bound -- run where the
  ## argument stands. So the lvalue's trailing lazy reads (`lazyStmt`), and
  ## what binds them for the call, move after the last argument; its eager
  ## part (a call it makes, `getB().x`'s `getB()`) stays, evaluated once.
  ## Each moved index check is exact only while the values it reads are
  ## those it read where it stood: its index, and the length of a container
  ## that may change (`growable`) are snapshotted there, and a path on which
  ## a later call changed either declines before the access
  ## (`feEvalOrderUnmodelled`: Nim accesses through a value it never
  ## checked, undefined behaviour). A check this cannot snapshot (one that
  ## reads a moved read, a variant arm's discriminant, a checked
  ## arithmetic) keeps the lvalue where it stands and the call declines
  ## whenever a later argument may write.
  let lo = la.lo - base
  let hi = la.hi - base
  let be = la.bindEnd - base
  outPre.add seg[0 ..< lo]
  var cut = hi
  while cut > lo and lazyStmt(seg[cut - 1]): dec cut
  outPre.add seg[lo ..< cut]
  var defined: seq[string]
  for i in cut ..< hi: defined.add stmtDefines(seg[i])
  var nIndex = 0
  for i in lo ..< hi:
    if seg[i].kind == isIndex: inc nIndex
  proc readsMoved(e: IRExpr): bool =
    var vs: seq[string]
    irVars(e, vs)
    for v in vs:
      if v in defined: return true
    false
  var guards = newSeq[IRExpr](hi - cut)
  var snaps: seq[IRStmt]
  var exact = true
  var ord = 0
  for i in lo ..< hi:
    let s = seg[i]
    let j = ord
    if s.kind == isIndex: inc ord
    if i < cut or not lazyChecked(s): continue
    if s.kind != isIndex or nIndex != la.growable.len or
       readsMoved(s.ixIdx) or (la.growable[j] and readsMoved(s.ixArr)):
      exact = false
      break
    var differs: IRExpr = nil
    if not isLiteralIR(s.ixIdx):
      let snap = freshSynth(ctx, "addrsnap")
      snaps.add mkLet(snap, nil, s.ixIdx)
      differs = mkBinop(bNe, s.ixIdx, mkVar(snap))
    if la.growable[j]:
      let snap = freshSynth(ctx, "addrsnap")
      snaps.add mkLet(snap, nil, mkSeqLen(s.ixArr))
      let d = mkBinop(bNe, mkSeqLen(s.ixArr), mkVar(snap))
      differs = if differs == nil: d else: mkBinop(bOr, differs, d)
    guards[i - cut] = differs
  if not exact:
    outPre.add seg[cut ..< seg.len]
    tail.add ctx.declineMarker(feEvalOrderUnmodelled,
      "a by-address argument whose address Nim checks where it stands " &
      "and takes at the call, after a later argument's call that may " &
      "change what the check read (feEvalOrderUnmodelled)")
    return
  outPre.add snaps
  let why = "a by-address argument's address is checked where it stands " &
            "and taken at the call, after a later argument's call changed " &
            "what the check read: Nim accesses through a value it never " &
            "checked (feEvalOrderUnmodelled)"
  for i in cut ..< hi:
    if guards[i - cut] != nil:
      tail.add mkIf(@[mkBranch(guards[i - cut],
                      mkBlock(@[ctx.declineMarker(feEvalOrderUnmodelled, why)]))])
    tail.add seg[i]
  tail.add seg[hi ..< be]
  tail.add seg[be ..< seg.len]

proc orderOperands(preamble: var seq[IRStmt]; marks: seq[int];
                   irs: var seq[IRExpr]; tys: seq[IRType]; mode: OrderMode;
                   ctx: ParseCtx; fixed: seq[bool] = @[];
                   late: seq[LateAddr] = @[]) =
  ## RFC-0005 S8ax. Operand `k` of an expression was parsed into
  ## `irs[k]`, its statements into `preamble[marks[k] ..< marks[k+1]]` (the
  ## last up to the end). Where a later operand's statements may write
  ## (`stmtMayWrite`), place each operand's read where Nim makes it:
  ##
  ## * an element of a constructor (`omElements`), or an argument Nim
  ##   evaluates into a temporary (`isEagerIR`) left inline, is bound to a
  ##   temporary at the end of its own statements;
  ## * the trailing lazy statements of an operand (`lazyStmt`), when none
  ##   checks anything, move after the last operand's statements, where Nim
  ##   reads them;
  ## * when one checks something (`lazyChecked`), they stay, and the
  ##   variables they read are snapshotted before them; after the last
  ##   operand's statements a path on which any differs declines
  ##   (`feEvalOrderUnmodelled`). A read through the heap (`isDeref`), an
  ##   index or a variant-arm field among them declines whenever a later
  ##   operand may write: its container has no comparison to snapshot.
  ##
  ## An operand `fixed[k]` marks (a `var` or `addr` argument, passed by
  ## address) is left as it is, unless `late[k]` says where its lvalue was
  ## lowered: RFC-0005 S8bk, its address is taken at the call
  ## (`placeLateAddr`).
  let n = irs.len
  if n < 2: return
  var segs = newSeq[seq[IRStmt]](n)
  for k in 0 ..< n:
    let hi = if k + 1 < n: marks[k + 1] else: preamble.len
    segs[k] = preamble[marks[k] ..< hi]
  var writes = newSeq[bool](n)
  for k in 0 ..< n:
    for s in segs[k]:
      if stmtMayWrite(s): writes[k] = true
    if irHasCall(irs[k]): writes[k] = true
  var later = newSeq[bool](n)
  var any = false
  for k in countdown(n - 2, 0):
    later[k] = writes[k + 1] or later[k + 1]
    any = any or later[k]
  if not any: return
  var outPre = preamble[0 ..< marks[0]]
  var tail: seq[IRStmt]
  for k in 0 ..< n:
    if not later[k] or (k < fixed.len and fixed[k]):
      # RFC-0005 S8bk: a by-address argument a later argument's call may
      # write past has its address taken at the call (`placeLateAddr`).
      # Only `fixed` operands carry a `late` entry, so this never meets
      # S8be's `splitIndexChecks` below, which handles the by-value ones.
      if later[k] and k < late.len and late[k].ok:
        placeLateAddr(segs[k], late[k], marks[k], outPre, tail, ctx)
      else:
        outPre.add segs[k]
      # RFC-0005 S8be: a call left inline in a later operand (a closure
      # call in a `while` guard, which hoists nothing, or in a call's
      # argument) runs where it stands, before the earlier operands' inline
      # reads: bind it here, ahead of the reads the tail and the
      # expression make. Before S8be the walk lowered it after them and
      # declined the clash (`ceCaptureByRefUnmodelled`).
      if k > 0 and irHasCall(irs[k]) and irs[k].kind != iekVar and
         not (k < fixed.len and fixed[k]):
        var earlierRead = false
        for j in 0 ..< k:
          if not isLiteralIR(irs[j]): earlierRead = true
        if earlierRead:
          let tmp = freshSynth(ctx, "ord")
          outPre.add mkLet(tmp, tys[k], irs[k])
          irs[k] = mkVar(tmp)
      continue
    var seg = segs[k]   # a copy: a VM `let` of an element aliases it (S8ab)
    if mode == omElements or isEagerIR(irs[k]) or irHasCall(irs[k]):
      outPre.add seg
      if mode == omElements and not isLiteralIR(irs[k]) or
         irs[k].kind != iekVar and not isLiteralIR(irs[k]):
        let tmp = freshSynth(ctx, "ord")
        outPre.add mkLet(tmp, tys[k], irs[k])
        irs[k] = mkVar(tmp)
      continue
    # The trailing lazy statements, and whether any checks something.
    var cut = seg.len
    while cut > 0 and lazyStmt(seg[cut - 1]): dec cut
    var checked = false
    var viaHeap = false
    for i in cut ..< seg.len:
      if lazyChecked(seg[i]): checked = true
      if seg[i].kind == isDeref: viaHeap = true
    if irs[k].kind != iekVar and rhsHasInlineDefectFork(irs[k]):
      checked = true
    outPre.add seg[0 ..< cut]
    if not checked:
      for i in cut ..< seg.len: tail.add seg[i]
      continue
    # RFC-0005 S8be: an index check only: checked here, read late.
    if not viaHeap and splitIndexChecks(seg, cut, irs[k], ctx, outPre, tail):
      continue
    # Checked: read where it stands, and decline where a later call
    # changed what it read.
    var reads: seq[string]
    var defined: seq[string]
    for i in cut ..< seg.len:
      let s = seg[i]
      case s.kind
      of isLet:
        irVars(s.lvalue, reads)
        defined.add s.lname
      of isIndex:
        irVars(s.ixArr, reads)
        irVars(s.ixIdx, reads)
        defined.add s.ixRetName
      of isVariantField:
        irVars(s.vfRecv, reads)
        defined.add s.vfRetName
      of isDeref:
        irVars(s.dPtr, reads)
        defined.add s.dRetName
      else: discard
    if irs[k].kind != iekVar: irVars(irs[k], reads)
    var cmp: seq[(string, string)]
    # A seq, array or object read by an index or a variant-arm field read
    # has no `!=` the walker lowers; the comparisons are on the scalars a
    # checked `let` reads (`rhsHasInlineDefectFork`'s operations).
    var comparable = not viaHeap
    for i in cut ..< seg.len:
      if seg[i].kind in {isIndex, isVariantField}: comparable = false
    for nm in reads:
      if nm in defined or isSynthName(nm): continue
      cmp.add (nm, freshSynth(ctx, "ordsnap"))
    if irs[k].kind != iekVar:
      # An inline checked argument: evaluate it here, as Nim checks it.
      for (nm, snap) in cmp:
        outPre.add mkLet(snap, nil, mkVar(nm))
      outPre.add seg[cut ..< seg.len]
      let tmp = freshSynth(ctx, "ord")
      outPre.add mkLet(tmp, tys[k], irs[k])
      irs[k] = mkVar(tmp)
    else:
      for (nm, snap) in cmp:
        outPre.add mkLet(snap, nil, mkVar(nm))
      outPre.add seg[cut ..< seg.len]
    let why = "an operand Nim checks where it stands but reads after a " &
              "later operand's call, which may change what it reads " &
              "(feEvalOrderUnmodelled)"
    if not comparable or cmp.len == 0 and viaHeap:
      tail.add ctx.declineMarker(feEvalOrderUnmodelled, why)
      continue
    if cmp.len == 0: continue
    var differs: IRExpr = nil
    for (nm, snap) in cmp:
      let d = mkBinop(bNe, mkVar(nm), mkVar(snap))
      differs = if differs == nil: d else: mkBinop(bOr, differs, d)
    tail.add mkIf(@[mkBranch(differs,
                    mkBlock(@[ctx.declineMarker(feEvalOrderUnmodelled, why)]))])
  outPre.add tail
  # In place: `preamble` may be a caller's sequence another expression is
  # appending to.
  preamble.setLen(0)
  for s in outPre: preamble.add s

# ---- Forward decls -----------------------------------------------------------

proc parseExpr*(n: NimNode, preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr
proc parseStmt*(n: NimNode, ctx: ParseCtx): IRStmt
proc parseStmtBare(n: NimNode, ctx: ParseCtx): IRStmt
proc parseAsgn(n: NimNode, rhsOverride: IRExpr,
               preamble: var seq[IRStmt], ctx: ParseCtx): IRStmt
  ## RFC-0005 S8ac fwd decl (defined beside `parseStmtInner`).
proc parseStmtInner(n: NimNode,
                    preamble: var seq[IRStmt],
                    ctx: ParseCtx): IRStmt
proc parseMoveExpr(n, calleeSym: NimNode; preamble: var seq[IRStmt];
                   ctx: ParseCtx): IRExpr
  ## RFC-0005 S8bl fwd decl (defined beside `parseVarMagicStmt`).

proc parseLoopBody(bodyNode: NimNode; ctx: ParseCtx; unrolled = false):
    tuple[body: IRStmt, brkLabel: string] =
  ## RFC-0005 S8m. Parse a desugared `for` loop's body as a jump target. A
  ## `continue` leaves the body (its labelled block), so the increment that
  ## follows it still runs; in an `unrolled` loop (one body copy per
  ## element, no `isWhile`) a `break` leaves the block `brkLabel` the caller
  ## wraps the whole unrolled sequence in.
  ctx.pushJumpTarget(isLoop = true, brkViaBlock = unrolled, contViaBlock = true)
  let body = parseStmt(bodyNode, ctx)
  let jt = ctx.popJumpTarget()
  (wrapJumpBlock(jt.contLabel, body), jt.brkLabel)
proc zeroValueForType(ty: IRType): IRExpr  ## CR-2a fwd decl (defined below):
                                            ## parseExpr's expression-kind
                                            ## catch-all needs this to build a
                                            ## type-correct dummy.
proc unsupportedFieldPlaceholder(ty: IRType): IRExpr  ## R8 fwd decl (defined
                                            ## below, beside `zeroValueForType`):
                                            ## P2a's `nnkObjConstr` arm needs
                                            ## this to build a KIND-correct
                                            ## placeholder for an omitted field
                                            ## whose type has no clean zero.
proc refExprClassify(n: NimNode): ClassifiedType  ## P2b fwd decl (defined
                                            ## below): classify whether a VALUE
                                            ## expression genuinely carries a
                                            ## ref/ptr ADDRESS (itRef/itPtr) as
                                            ## opposed to a bare NAMED
                                            ## ref-object-alias symbol, which
                                            ## D1a value-models as itTuple.
type ByRefSub = object
  ## RFC-0005 S8ba. One formal of a call specialised to pass a heap lvalue
  ## by reference (`userCallStmt`): the formal at `idx` (a `var T`, or a
  ## `ptr T` when `isPtr`) is replaced in the callee's body by `tail`, the
  ## caller's lvalue with its last ref spelled as the parameter `name`
  ## (`markByRef`), and that parameter takes the formal's place.
  idx: int
  isPtr: bool
  tail: NimNode
  addrNode: NimNode   ## `addr tail`, for a bare use of a `ptr` formal
  name: string
  baseTy: IRType
  keyPart: string
  base: NimNode       ## the caller's ref, evaluated at the call

proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode,
                          callSite: NimNode = nil;
                          byRef: seq[ByRefSub] = @[]): string
proc hasGenericParams(impl: NimNode): bool  ## RFC-0005 S8ba (fwd)
proc bodyHashPart(calleeSym, impl: NimNode): string  ## C3 site key (fwd)
proc calleeIntOffsetReturnPositions(calleeSym: NimNode): seq[int]
  ## Round-6 B5 fwd decl (ADR-0028 Leg 1, chained composition; defined below,
  ## beside `collectIntOffsetParams`, since it shares `tryMatchScanPairIdiomShape`/
  ## `tryMatchAccumulatingScanIdiomShape`): the "user-proc call in expression
  ## position" `mkCall` site needs this BEFORE those recognizer shape-match
  ## procs are defined further down the file.
proc isVarIndirection(n: NimNode): bool =
  ## RFC-0005 S8ac. True when `n` is the compiler's `nnkHiddenDeref` over an
  ## lvalue of `var T` type (a `var` formal, a `var`-returning call): the
  ## by-reference indirection that makes the formal alias the caller's
  ## variable, NOT a ref/ptr dereference. Reading it yields the variable's
  ## value, and assigning it rebinds the variable. For `T = ref U` the two
  ## are different operations: `cur = b` on `cur: var Box` rebinds the
  ## caller's `Box`, whereas the ref-deref reading (before S8ac) stored `b`
  ## INTO the old cell (`cur[] = b`, an ill-sorted heap store and
  ## `weInternalWalkerFault`). A plain `ref` value is never wrapped this way
  ## (its deref is an `nnkDerefExpr`, or the hidden deref under a
  ## `nnkDotExpr`, whose operand type is the `ref` itself).
  if n.kind != nnkHiddenDeref or n.len != 1: return false
  let t = n[0].getTypeInst
  (not t.isNil and t.kind == nnkVarTy) or n[0].typeKind == ntyVar

proc unwrapHidden(n: NimNode): NimNode  ## Round-6 B1 fwd decl (defined
                                         ## below, beside `sameSym`):
                                         ## `parseExpr`'s itSeq bracket/`.len`
                                         ## dispatch needs this to test a
                                         ## receiver against
                                         ## `ctx.procScoped.stringBackedParams`.
proc containsSym(syms: seq[NimNode], n: NimNode): bool  ## Round-6 R4 fwd
                                         ## decl (defined below, beside
                                         ## `sameSym`, which it wraps):
                                         ## `receiverIsStringBacked` (just
                                         ## below) needs symbol-identity
                                         ## membership before `sameSym`
                                         ## itself is defined this far up
                                         ## the file.
proc siteLoc*(n: NimNode): string  ## Round-6 A3/B1 fwd decl (defined below,
                                    ## beside `siteMsg`): the shared seq
                                    ## bracket/len helpers stamp `IRStmt.
                                    ## isIndex`/`IRExpr.iekSeqLen`'s new
                                    ## `loc` field with this.
proc isBuiltinNamed(head: NimNode, names: openArray[string]): bool
  ## RFC-0005 S8c fwd decl (defined below, beside `isUserCallee`): the seq
  ## bracket/slice helper just below matches `..`/`^` heads by name.

proc receiverIsStringBacked(recvRawNode: NimNode, ctx: ParseCtx): bool =
  ## Round-6 B1 (ADR-0028 Leg 1). True iff `recvRawNode` (unwrapped of
  ## compiler-inserted passthrough wrappers) is a BARE symbol reference to
  ## one of `ctx.procScoped.stringBackedParams` — the ONE fact `parseSeqBracketAccess`/
  ## `parseSeqLenAccess` consult to choose the string-op IR kinds
  ## (`iekStrSubstr`/`iekStrAt`/`iekStrLen`) over the ordinary array `itSeq`
  ## IR (`mkSeqSlice`/`mkIndexStmt`/`mkSeqLen`) for a `seq[byte]` receiver.
  let core = unwrapHidden(recvRawNode)
  core.kind == nnkSym and containsSym(ctx.procScoped.stringBackedParams, core)

proc scanReceiverOk(sNode: NimNode, ctx: ParseCtx): tuple[ok, byteBacked: bool] =
  ## Round-6 B7-rider (ADR-0028 Leg 1, closes BLOCKER A). The scan-idiom
  ## recognizer family's SHARED receiver gate: true iff `sNode` is either a
  ## genuine itString-typed receiver (Q1/B0's original gate, `byteBacked =
  ## false`) or a string-backed `seq[byte]` receiver per B1's shared
  ## classifier (`ctx.procScoped.stringBackedParams`, consulted via
  ## `receiverIsStringBacked` — the SAME fact `parseSeqBracketAccess`/
  ## `parseSeqLenAccess` already use to choose string-op IR over array IR
  ## for the elemental read, applied HERE so the closed-form recognizers and
  ## the elemental parse can never diverge on which receivers get string
  ## treatment). The mutation-fallback veto is inherited for free: a
  ## mutated `seq[byte]` param is never added to `ctx.procScoped.stringBackedParams` in
  ## the first place (`collectStringBackedByteSeqParams` already excludes
  ## it via `scanShapeReceiverMutated`), so `byteBacked` comes back false
  ## for it and the whole family correctly leaves it unrecognized (falls
  ## through to the pre-existing array-model k-unroll path) — no separate
  ## check needed at any of the four call sites.
  if sNode.typeKind != ntyNone and classifyType(sNode).ty.kind == itString:
    (true, false)
  else:
    let byteBacked = receiverIsStringBacked(sNode, ctx)
    (byteBacked, byteBacked)

proc scanDelimiterChar(litNodeRaw: NimNode, byteBacked: bool): Option[char] =
  ## Round-6 B7-rider companion to `scanReceiverOk`: maps a scan idiom's
  ## delimiter literal to its char value. An itString receiver's delimiter
  ## stays gated to a genuine char literal (Q1/B0/B3/B4's original gate,
  ## UNCHANGED — a real `string` element can only syntactically compare
  ## against a char literal in source Nim). A string-backed `seq[byte]`
  ## receiver's delimiter is a BYTE literal — `s[i] == 0'u8`, `s[i] ==
  ## byte(0)`/`uint8(0)`, or a plain in-range int literal (`0x00`) — mapped
  ## to the same char value. The literal-KIND acceptance set (char literal,
  ## or any sized-int-literal kind with `intVal` in `[0, 255]`) mirrors
  ## `collectStringBackedByteSeqParams`'s own `litOk` check VERBATIM,
  ## keeping classifier and recognizer in lockstep on which delimiter
  ## literals qualify a byte-seq receiver in the first place. An explicit
  ## `byte(<lit>)`/`uint8(<lit>)` conversion call is unwrapped defensively
  ## (mirrors B4's own `char(<s>[<i>])` unwrap for the accumulator arg) —
  ## Nim's typed AST commonly const-folds these to a bare sized-int-literal
  ## node already, but the unwrap costs nothing and guards against a
  ## compiler-version difference.
  var lit = litNodeRaw
  # A `byte(<lit>)`/`uint8(<lit>)` explicit conversion of a literal does NOT
  # const-fold in Nim's typed AST (confirmed empirically while landing this
  # rider — `treeRepr` dump: `byte(0)` is `Conv(Sym "byte", IntLit 0)`,
  # untouched) — unlike `char(<s>[<i>])`'s call-syntax spelling (B4's own
  # accumulator-arg unwrap), an explicit TYPE conversion of a value arrives
  # as `nnkConv`, not `nnkCall`/`nnkCommand`.
  # RFC-0005 S8d: `isBuiltinTypeHead` -- the SYSTEM `byte`/`uint8`, not a
  # user type of that name (whose conversion need not keep the value).
  if byteBacked and lit.kind == nnkConv and lit.len == 2 and
     isBuiltinTypeHead(lit[0], ["byte", "uint8"]):
    lit = unwrapHidden(lit[1])
  elif byteBacked and lit.kind in {nnkCall, nnkCommand} and lit.len == 2 and
       isBuiltinTypeHead(lit[0], ["byte", "uint8"]):
    lit = unwrapHidden(lit[1])
  case lit.kind
  of nnkCharLit:
    some(char(lit.intVal and 0xFF))
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit,
     nnkUIntLit, nnkUInt8Lit, nnkUInt16Lit, nnkUInt32Lit, nnkUInt64Lit:
    if byteBacked and lit.intVal >= 0 and lit.intVal <= 255:
      some(char(lit.intVal))
    else:
      none(char)
  else: none(char)

proc parseStrSliceBound(boundNode: NimNode, recvIR: IRExpr,
                        preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8g. One bound of a string slice `s[a .. b]`. A `^k` bound is
  ## `BackwardsIndex(k)` in the typed AST, meaning `s.len - k`; parsed as a
  ## plain expression it was `k` itself, so `s[1 .. ^1]` of "abc" was "b"
  ## (a false `sxUnsat` for `== "bc"`). The seq slice path already rewrote
  ## it (`parseSeqBracketAccess`); the two string slice paths did not.
  var b = boundNode
  while b.kind in {nnkHiddenStdConv, nnkStmtListExpr} and b.len >= 1:
    b = b[b.len - 1]
  if b.kind in {nnkCall, nnkConv, nnkCommand, nnkPrefix} and b.len == 2 and
     b[0].kind in {nnkSym, nnkIdent} and
     isBuiltinNamed(b[0], ["BackwardsIndex", "^"]):
    mkBinop(bSub, mkStrOp(iekStrLen, "len", @[recvIR]),
            parseExpr(b[1], preamble, ctx))
  else:
    parseExpr(boundNode, preamble, ctx)

func isPureContainer(e: IRExpr): bool =
  ## RFC-0005 S8p. The container shapes `isIndex` lowers without a
  ## seed/drain (`lowerLeafInExpr`): a variable, or a field chain over one.
  e.kind == iekVar or (e.kind == iekField and isPureContainer(e.obj))

proc liftIndexContainer(objIR: IRExpr, ty: IRType,
                        preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8p. An `isIndex` container that is not a variable or a field
  ## chain over one (`f(x)[0]`, a closure call) is bound to a synthetic
  ## `let` first, so it is lowered as any `let` value is (with its effects
  ## drained) and the index statement reads the variable. It hit
  ## `lowerLeafInExpr`'s assertion (`weInternalWalkerFault`) before.
  ## Called before the index is parsed: Nim evaluates the container first.
  if isPureContainer(objIR): return objIR
  let synth = freshSynth(ctx, "ixrecv")
  preamble.add mkLet(synth, ty, objIR)
  mkVar(synth)

proc parseSeqBracketAccess(n, recvRawNode: NimNode, objIR: IRExpr,
                            rawIdxNode: NimNode, elemTy: IRType,
                            preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  ## Round-6 B1. Shared `data[a..b]` (slice) / `data[i]` (index read)
  ## dispatch for an `itSeq` receiver, collapsing the two previously-
  ## DUPLICATE sites (`nnkBracketExpr`'s `of itSeq:` arm and the call-form
  ## `` `[]`(data, idx) `` arm — the RFC's explicit "cannot diverge"
  ## requirement) into one helper. `n` is the WHOLE index/slice node (for
  ## diagnostic messages, matching the pre-B1 text verbatim); `recvRawNode`
  ## is the receiver's raw (not-yet-parsed) NimNode; `objIR` is the
  ## ALREADY-parsed receiver IR (parsed once by the caller — this helper
  ## must not re-parse it, which would double any preamble side effects);
  ## `rawIdxNode` is the raw (not-yet-unwrapped) index/range node.
  ##
  ## When `recvRawNode` is string-backed (B1a), dispatch routes through the
  ## SAME `iekStrSubstr`/`iekStrAt` IR kinds a declared-`string` receiver
  ## uses (Leg 1: the array-lambda `iekSeqSlice` hard-requires `svSeq`, so
  ## the choice must be made HERE, at parse time — there is no walk-time
  ## dispatch left once the IR is frozen).
  let stringBacked = receiverIsStringBacked(recvRawNode, ctx)
  var idxNode = rawIdxNode
  while idxNode.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv,
                         nnkStmtListExpr} and idxNode.len >= 1:
    idxNode = idxNode[idxNode.len - 1]
  if idxNode.kind == nnkInfix and idxNode.len == 3 and
     idxNode[0].kind in {nnkSym, nnkIdent} and
     isBuiltinNamed(idxNode[0], ["..", "..<"]):
    # RFC-0005 S8g: a `^k` LOW bound (`data[^3 .. ^1]`) is `len - k` too;
    # only the high bound was rewritten, so the low one read as `k`.
    var loNode = idxNode[1]
    while loNode.kind in {nnkHiddenStdConv, nnkStmtListExpr} and
          loNode.len >= 1:
      loNode = loNode[loNode.len - 1]
    let loIR =
      if loNode.kind in {nnkCall, nnkConv, nnkCommand, nnkPrefix} and
         loNode.len == 2 and loNode[0].kind in {nnkSym, nnkIdent} and
         isBuiltinNamed(loNode[0], ["BackwardsIndex", "^"]):
        mkBinop(bSub, mkSeqLen(objIR), parseExpr(loNode[1], preamble, ctx))
      else:
        parseExpr(idxNode[1], preamble, ctx)
    # `^k` stays a `BackwardsIndex(k)` conversion for seqs (a string-backed
    # receiver's DECLARED type is still `seq[byte]`, so this pre-expansion
    # never applies to it either) — rewrite to `len(base) - k`.
    var hiNode = idxNode[2]
    while hiNode.kind in {nnkHiddenStdConv, nnkStmtListExpr} and
          hiNode.len >= 1:
      hiNode = hiNode[hiNode.len - 1]
    var hiIR: IRExpr
    if hiNode.kind in {nnkCall, nnkConv, nnkCommand, nnkPrefix} and
       hiNode.len == 2 and hiNode[0].kind in {nnkSym, nnkIdent} and
       isBuiltinNamed(hiNode[0], ["BackwardsIndex", "^"]):
      hiIR = mkBinop(bSub, mkSeqLen(objIR), parseExpr(hiNode[1], preamble, ctx))
    else:
      hiIR = parseExpr(idxNode[2], preamble, ctx)
    if idxNode[0].strVal == "..<":
      hiIR = mkBinop(bSub, hiIR, mkIntLit(1))
    if stringBacked:
      return mkStrOp(iekStrSubstr, "[]", @[objIR, loIR, hiIR])
    else:
      return mkSeqSlice(objIR, loIR, hiIR)
  elif idxNode.typeKind != ntyNone and classifyType(idxNode).ty.kind == itInt:
    let recvIR =
      if stringBacked: objIR
      else: liftIndexContainer(objIR, classifyType(recvRawNode).ty, preamble, ctx)
    let idxIR = parseExpr(idxNode, preamble, ctx)
    if stringBacked:
      return mkStrOp(iekStrAt, "[]", @[objIR, idxIR])
    else:
      let synth = freshSynth(ctx, "idx")
      preamble.add mkIndexStmt(synth, recvIR, idxIR, elemTy, siteLoc(n))
      ctx.seqIndexRets.incl synth   # RFC-0005 S8be
      return mkVar(synth)
  else:
    preamble.add ctx.declineAtSite(
      feUnsupportedExprKind,
      "seq `[]` index is neither int-typed nor a recognizable " &
             "range literal (kind " & $idxNode.kind & ") in `" & n.repr &
             "` — degraded to sxUnknown (feUnsupportedExprKind)",
      "seq `[]` with unrecognized index (feUnsupportedExprKind)")
    let dummy = zeroValueForType(classifyType(n).ty)
    return (if dummy != nil: dummy else: mkIntLit(0))

proc parseSeqLenAccess(recvRawNode: NimNode, objIR: IRExpr,
                        ctx: ParseCtx): IRExpr =
  ## Round-6 B1. Shared `data.len` / `len(data)` dispatch, collapsing the
  ## two previously-DUPLICATE sites (`nnkDotExpr`'s `of itSeq:` arm and the
  ## call-form `len`/`card` arm) into one helper. `objIR` is the
  ## ALREADY-parsed receiver IR. `ctx.procScoped.stringBackedParams` membership is
  ## harmless to consult even for an `itTable`/`itSet` receiver — the B1a
  ## collector only ever adds `itSeq[byte]` param names, so a Table/Set
  ## receiver's name (even if textually coincident) can never be a member.
  if receiverIsStringBacked(recvRawNode, ctx):
    mkStrOp(iekStrLen, "len", @[objIR])
  else:
    mkSeqLen(objIR)

# ---- Phase 15 Cluster C (C1): closure / lambda parsing ----------------------

proc collectBoundLocals(n: NimNode, into: var HashSet[string]) =
  ## Phase 15 C1. Collect names DEFINED inside a lambda body (the LHS of any
  ## `let`/`var`/`for`/nested-proc binding). These are NOT free variables —
  ## a reference to one is a body-local, not a capture from the enclosing scope.
  if n == nil: return
  case n.kind
  of nnkLetSection, nnkVarSection, nnkConstSection:
    for d in n:
      if d.kind == nnkIdentDefs or d.kind == nnkVarTuple:
        for i in 0 ..< d.len - 2:
          let nm = d[i]
          if nm.kind in {nnkSym, nnkIdent}: into.incl nm.strVal
  of nnkForStmt:
    for i in 0 ..< n.len - 2:
      if n[i].kind in {nnkSym, nnkIdent}: into.incl n[i].strVal
  else: discard
  for c in n: collectBoundLocals(c, into)

proc isNestedRoutine(sym: NimNode): bool  ## RFC-0005 S8an fwd decl
proc nestedCaptureSyms(impl: NimNode): seq[NimNode]  ## RFC-0005 S8an fwd decl

proc collectFreeVarRefs(n: NimNode, bound: HashSet[string],
                        order: var seq[string], seen: var HashSet[string],
                        mutable: var seq[string]) =
  ## Phase 15 C1. Enumerate the FREE VARIABLES of a lambda body: every `nnkSym`
  ## reference whose symbol is a runtime VALUE binding (`nskParam`/`nskLet`/
  ## `nskVar`/`nskForVar`) and that is NOT bound inside the lambda (`bound`
  ## holds the lambda's own params ++ its body-locals). This excludes top-level
  ## procs/types/consts/enums (different `symKind`) — those are not captured.
  ## First-seen source order is preserved (deterministic capture list / key).
  ## RFC-0005 S9: `mutable` receives the captures whose symbol is a mutable
  ## local (`nskVar`/`nskForVar`) -- Nim captures those by reference, so their
  ## value at a call can differ from their value at construction. A `let` or
  ## a (non-`var`, the only capturable kind) param cannot change.
  ## RFC-0005 S8an: a nested routine the body names (calls, or uses as a
  ## value) reaches ITS captures through the lambda: they are the lambda's
  ## captures too, so a write to one through the routine is seen as the
  ## by-reference capture write it is.
  if n == nil: return
  if n.kind == nnkSym:
    if symKind(n) in {nskParam, nskLet, nskVar, nskForVar}:
      let nm = n.strVal
      if nm notin bound and nm notin seen:
        seen.incl nm
        order.add nm
        if symKind(n) in {nskVar, nskForVar}: mutable.add nm
    elif isNestedRoutine(n):
      let ni = resolveRoutineImpl(n)
      if ni != nil:
        for s in nestedCaptureSyms(ni):
          let nm = s.strVal
          if nm notin bound and nm notin seen:
            seen.incl nm
            order.add nm
            if symKind(s) in {nskVar, nskForVar}: mutable.add nm
    return
  for c in n: collectFreeVarRefs(c, bound, order, seen, mutable)

# ---- RFC-0005 S8an: a routine declared inside another -----------------------

proc namesRoutineDef(sym: NimNode): bool =
  ## RFC-0005 S8an. True when `sym`'s impl is a routine DEFINITION, decided
  ## by the impl's node kind (`routineShapedForClosureDetect`), never by a
  ## symbol-kind gate (RFC-parser-normalization Cluster N).
  if sym.kind != nnkSym: return false
  let impl = getImpl(sym)
  impl != nil and impl.kind in routineShapedForClosureDetect

proc isNestedRoutine(sym: NimNode): bool =
  ## RFC-0005 S8an. True when `sym` names a routine declared inside another
  ## routine (its owner is a routine, not a module).
  if sym.kind != nnkSym or symKind(sym) in {nskVar, nskLet, nskParam,
                                            nskForVar, nskConst, nskType,
                                            nskField, nskEnumField}:
    return false
  namesRoutineDef(sym) and namesRoutineDef(owner(sym))

proc collectDeclaredSyms(n: NimNode; into: var seq[NimNode]) =
  ## RFC-0005 S8an. Every value symbol DECLARED anywhere in `n`: `let`/`var`
  ## names (tuple unpacking included), for-variables, and the formal
  ## parameters of `n` and of every routine or lambda nested in it.
  if n == nil: return
  case n.kind
  of nnkIdentDefs, nnkVarTuple:
    for i in 0 ..< n.len - 2:
      var s = n[i]
      if s.kind == nnkPragmaExpr and s.len > 0: s = s[0]
      if s.kind == nnkSym: into.add s
      elif s.kind == nnkVarTuple: collectDeclaredSyms(s, into)
  of nnkForStmt:
    for i in 0 ..< n.len - 2:
      if n[i].kind == nnkSym: into.add n[i]
      elif n[i].kind == nnkVarTuple: collectDeclaredSyms(n[i], into)
  else: discard
  for c in n: collectDeclaredSyms(c, into)

proc collectOuterRefs(n: NimNode; refs, nested: var seq[NimNode]) =
  ## RFC-0005 S8an. The local value symbols `n` reads or writes (`refs`:
  ## `var`/`let`/param/for-variable, module-level globals excluded -- the
  ## walker threads those separately), and the nested routines it names
  ## (`nested`).
  if n == nil: return
  if n.kind == nnkSym:
    if symKind(n) in {nskVar, nskLet, nskParam, nskForVar}:
      if not isModuleGlobal(n) and not containsSym(refs, n): refs.add n
    elif isNestedRoutine(n) and not containsSym(nested, n):
      nested.add n
    return
  for c in n: collectOuterRefs(c, refs, nested)

proc nestedCaptureSyms(impl: NimNode): seq[NimNode] =
  ## RFC-0005 S8an. The enclosing routines' variables and parameters that
  ## the nested routine `impl` reaches: those its body names without
  ## declaring them, and those reached through each nested routine it names
  ## (transitively -- `b` calling `a`, which captures `c`, reaches `c`).
  ## Nim captures them by reference. Symbol identity throughout: two
  ## variables of one spelling are two captures.
  var work = @[impl]
  var seen: seq[NimNode]
  if impl.len > 0 and impl[0].kind == nnkSym: seen.add impl[0]
  var ownDecls: seq[NimNode]
  collectDeclaredSyms(impl, ownDecls)
  var i = 0
  while i < work.len:
    let r = work[i]
    inc i
    var decls, refs, nested: seq[NimNode]
    collectDeclaredSyms(r, decls)
    collectOuterRefs(r, refs, nested)
    for s in refs:
      if not containsSym(decls, s) and not containsSym(ownDecls, s) and
         not containsSym(result, s):
        result.add s
    for ns in nested:
      if containsSym(seen, ns): continue
      seen.add ns
      let ni = resolveRoutineImpl(ns)
      if ni != nil: work.add ni

proc nestedSiteKey(sym, impl: NimNode): string =
  ## RFC-0005 S8an. A nested routine's identity: its body hash and its
  ## declaration's position (two nested routines may share a body and a
  ## spelling while capturing different variables).
  let li = impl.lineInfoObj
  (if sym.kind == nnkSym: symBodyHash(sym) else: "") & "@" & $li.line &
    ":" & $li.column & "#nested"

proc nestedCaptureNames(calleeSym, impl: NimNode): seq[string] =
  ## RFC-0005 S8an. `nestedCaptureSyms` as IR names (spelled in the
  ## enclosing scope, which a callee's scope inherits). Empty for a
  ## module-level routine.
  if not isNestedRoutine(calleeSym): return
  for s in nestedCaptureSyms(impl):
    let nm = s.strVal
    if nm notin result: result.add nm

proc lambdaBodyHash(lam: NimNode): string =
  ## Phase 15 C1 (ADR-0009 D3, reconciliation §F-C). `symBodyHash` is a
  ## `std/macros` builtin that hashes the SEMANTIC body of a *proc SYMBOL*; a
  ## lambda in expression position is an `nnkLambda`/`nnkProcDef` NODE with no
  ## name symbol, so `symBodyHash` does NOT apply to it directly (verified C1).
  ## We therefore use the ADR-0008 D2 lineInfo-style fallback: the body node's
  ## `file:line:col`, which is formatting-tolerant ENOUGH for C1's structural
  ## keying (declOrder disambiguates identical-position lambdas; D8's concrete
  ## param types disambiguate instantiations via the canonical key). C2a may
  ## refine if a stronger semantic hash proves necessary.
  let li = lam.lineInfoObj
  li.filename & ":" & $li.line & ":" & $li.column

proc lambdaEffects(n: NimNode; ctx: ParseCtx; lam: IRExpr): IRExpr
  ## RFC-0005 S8bh fwd decl

proc parseRoutineToLambda(n: NimNode, ctx: ParseCtx,
                          site: tuple[siteHash: int64, declOrder: int],
                          forceNoCaptures = false): IRExpr =
  ## Phase 15 Cluster C. Shared core: turn a routine-def node (`nnkLambda` /
  ## expression-position `nnkProcDef`/`nnkFuncDef`, OR a top-level proc's
  ## `getImpl`) into an `iekLambda` under the supplied site key. Params/return
  ## come from the monomorphized formal-params (D8 — the typed AST is already at
  ## concrete types here). Free variables are enumerated by scope-stack diff
  ## (params ++ body-locals subtracted from the body's value-symbol references);
  ## `forceNoCaptures` short-circuits that to `@[]` for the C3 top-level-proc
  ## case (a module-scope proc has no enclosing runtime scope to capture from).
  ## PRAGMAS (`{.raises, gcsafe.}` etc.) are dropped — semchecker metadata only.
  # RFC-0005 S8e: claim the routine's names in the current naming scope
  # before reading any. A no-op for a lambda its enclosing routine already
  # claimed; for an expression-position `nnkProcDef` it is the claim.
  claimRoutine(n)
  let formal = n[3]
  formal.expectKind nnkFormalParams
  var params: seq[IRParam]
  var bound: HashSet[string]
  for i in 1 ..< formal.len:
    let id = formal[i]
    if id.kind != nnkIdentDefs: continue
    let tyNode = id[id.len - 2]
    let cls = classifyType(tyNode)
    let isVar = tyNode.kind == nnkVarTy
    for j in 0 ..< id.len - 2:
      params.add IRParam(name: id[j].strVal, ty: cls.ty,
                         rangeLo: cls.range.lo, rangeHi: cls.range.hi,
                         hasRange: cls.range.hasRange, isVar: isVar)
      bound.incl id[j].strVal
  var retTy = tBool()
  if formal[0].kind != nnkEmpty:
    retTy = classifyType(formal[0]).ty
  # The body of a routine def (lambda/proc/func) is at the fixed routine-body
  # index (`body(n)`); n.len-1 can be a trailing synthetic `result` symbol.
  let bodyNode = body(n)
  # Free variables = value-symbol refs not bound by the lambda. A top-level proc
  # (C3) has none by construction; skip the scan.
  var captures, mutCaptures: seq[string]
  if not forceNoCaptures:
    # Body-local definitions are also bound (not captured).
    collectBoundLocals(bodyNode, bound)
    var seen: HashSet[string]
    collectFreeVarRefs(bodyNode, bound, captures, seen, mutCaptures)
  let bodyIR = parseStmt(bodyNode, ctx)
  # RFC-0005 S8bh: with the summary a call through it needs to apply its
  # `var`/`addr` effects (`lambdaEffects`).
  lambdaEffects(n, ctx,
    mkLambda(site.siteHash, site.declOrder, params, bodyIR, captures, retTy,
             mutCaptures))

proc parseLambda(n: NimNode, ctx: ParseCtx): IRExpr =
  ## Phase 15 Cluster C (C1, ADR-0009). Parse an `nnkLambda` / expression-
  ## position `nnkProcDef` into an `iekLambda` keyed by `(lineInfo-hash,
  ## declOrder)` (D3 — a nameless lambda has no symbol for `symBodyHash`).
  let site = (siteHash: int64(hash(lambdaBodyHash(n))), declOrder: ctx.lambdaCounter)
  inc ctx.lambdaCounter
  parseRoutineToLambda(n, ctx, site)

proc parseProcAsValue(procSym, impl: NimNode, ctx: ParseCtx): IRExpr =
  ## Phase 15 C3 (ADR-0009, reconciliation §F-C). A TOP-LEVEL proc referenced in
  ## VALUE position (`let g = double`) → an `iekLambda` with `lambdaCaptures =
  ## @[]` (a unit-env closure: a module-scope proc has no free variables). The
  ## body comes from the proc's `getImpl` (`impl`, an `nnkProcDef`). The site key
  ## uses `symBodyHash` of the proc SYMBOL (which — unlike C1's nameless lambda —
  ## DOES apply: a top-level proc has a symbol), with the ADR-0008 D2 lineInfo
  ## fallback (`bodyHashPart`); `declOrder = 0` for a stable top-level name (D3).
  ## Calling it dispatches through the existing C2b `iekClosureCall` path; the
  ## walker materializes the zero-field unit-env via the C2a empty-capture path.
  # RFC-0005 S8an: a nested routine's site is its declaration
  # (`nestedSiteKey`), not its spelling and body alone.
  let site = (siteHash: int64(hash(
                if isNestedRoutine(procSym): nestedSiteKey(procSym, impl)
                else: bodyHashPart(procSym, impl))), declOrder: 0)
  # RFC-0005 S8e: the proc's body runs in a unit-env closure of its own --
  # its own naming scope, as a callee's is.
  let savedNames = enterNameScope()
  # RFC-0005 S8an: a routine declared inside another is a CLOSURE over the
  # enclosing variables it names -- its captures are enumerated as a
  # lambda's are, and its own locals keep clear of their names. Before,
  # every one was a unit-env closure, and a capture read as an unbound name
  # (`feGlobalReadUnmodelled`).
  let nested = isNestedRoutine(procSym)
  if nested: reserveScopedNames(nestedCaptureNames(procSym, impl))
  result = parseRoutineToLambda(impl, ctx, site, forceNoCaptures = not nested)
  leaveNameScope(savedNames)

# ---- Binop / unop helpers ----------------------------------------------------

proc binopForInfix(op: string): IRBinop =
  case op
  of "+":   bAdd
  of "-":   bSub
  of "*":   bMul
  of "div": bDiv
  of "/":   bDiv   ## Phase 15 F3: float division (operands are float in typed AST)
  of "mod": bMod
  of "==":  bEq
  of "!=":  bNe
  of "<":   bLt
  of "<=":  bLe
  of ">":   bGt
  of ">=":  bGe
  of "and": bAnd
  of "or":  bOr
  of "xor": bXor
  of "shl": bShl
  of "shr": bShr
  else:
    error("symex: unsupported infix operator `" & op & "`")

proc hasSymexPragma(calleeSym: NimNode, pragmaName: string): bool =
  ## True when `calleeSym`'s routine impl carries a pragma spelled
  ## `pragmaName`. Matched purely BY NAME — which module DECLARED the pragma
  ## template is deliberately not checked, so a leaf module can declare its
  ## own private copy rather than importing `nelli/symex` (and with it Z3);
  ## `coverage.nim` does exactly that. See `hasSymexOpaquePragma` /
  ## `hasSymexTransparentPragma` below for the two recognised names.
  if calleeSym.kind != nnkSym: return false
  let impl = resolveRoutineImpl(calleeSym)  ## RFC-parser-normalization N2
  if impl == nil: return false
  let prag = impl.pragma
  if prag.kind != nnkPragma: return false
  for p in prag:
    let name =
      case p.kind
      of nnkIdent, nnkSym: p.strVal
      of nnkExprColonExpr, nnkCall:
        if p[0].kind in {nnkIdent, nnkSym}: p[0].strVal else: ""
      else: ""
    if name == pragmaName:
      return true
  false

proc hasSymexOpaquePragma(calleeSym: NimNode): bool =
  ## Phase 9 — the user-facing extension hook. A proc marked with
  ## `{.symexOpaque.}` is treated by symex as a black box: the
  ## walker does not enter its body, the return value becomes a
  ## fresh symbolic of the proc's return type, and the surviving
  ## path is marked uncertain (same machinery as the built-in
  ## OpaqueEffectfulProcs catalog for `echo`/`writeFile`/etc.).
  ##
  ## Use this to bring user-defined IO procs, FFI wrappers, or
  ## intentionally-uninterpreted primitives under symex without
  ## hand-extending the registry.
  hasSymexPragma(calleeSym, "symexOpaque")

proc hasSymexTransparentPragma(calleeSym: NimNode): bool =
  ## Issue #163 — the STRONGER sibling of `{.symexOpaque.}`. A proc marked
  ## `{.symexTransparent.}` is not a black box the walker must be careful
  ## around; it is a call symex can DELETE. The author asserts the call is
  ## void and cannot change anything the SUT observes — no result to bind, no
  ## argument written through, no state the SUT reads back.
  ##
  ## `{.symexOpaque.}` also keeps the walker out of the body, but pays for it
  ## with a path taint (`forkPathTainted` + `w.sawUnknown`), which is the
  ## right price for `readLine()` and the wrong price for `recordEdge(id)`.
  ## Paying it for instrumentation cost the whole answer: `{.cover.}` puts a
  ## `recordEdge` at the top of every branch arm, so every path through an
  ## instrumented proc was tainted and `symexFind` returned `sxUnknown`.
  ##
  ## Scope of the promise, and what happens if it is overstated: the parser
  ## only ever DELETES the call in STATEMENT position, and even there only
  ## when every argument is provably inert (`isInertOpaqueCall` — the exact
  ## predicate the `{.symexOpaque.}` sibling arm applies to the same
  ## argument shapes; #163 review R7 closed a gap where the statement arm
  ## deleted unconditionally, before ever consulting it). A
  ## `{.symexTransparent.}` proc whose result IS used (expression position),
  ## or whose statement-position arguments include a writable `var`/`ref`/
  ## `ptr`/possibly-ref-carrying-object, falls back to `{.symexOpaque.}`
  ## handling instead, and the broken promise is recorded as an
  ## `AnnotationViolation` (RFC-0005 S8, verdict-neutral) — an over-claimed
  ## pragma costs precision (the opaque call's `dcSubstituted` gap), never
  ## soundness (never a false witness), on EITHER route.
  hasSymexPragma(calleeSym, "symexTransparent")

const inertArgTypeKinds = {
  ntyBool, ntyChar, ntyString, ntyEnum, ntyRange,
  ntyInt, ntyInt8, ntyInt16, ntyInt32, ntyInt64,
  ntyUInt, ntyUInt8, ntyUInt16, ntyUInt32, ntyUInt64,
  ntyFloat, ntyFloat32, ntyFloat64, ntyFloat128
}
  ## Issue #163 slice 4 — plainly value-typed. Deliberately EXCLUDES
  ## `ntyObject`/`ntyTuple` (a copied object can carry a `ref` field whose
  ## pointee the callee can still write), `ntySeq`/`ntyRef`/`ntyPtr`/
  ## `ntyPointer` (all writable through), `ntyProc` (an opaque callback),
  ## `ntyCString` (a writable pointer in disguise), `ntyVar` (should never
  ## appear here — see `nnkHiddenAddr` below, but excluded for defense in
  ## depth), and everything else this allowlist doesn't name. Conservative
  ## by construction: an unrecognised `typeKind` is NOT inert.

proc isInertArg(a: NimNode): bool =
  ## Issue #163 slice 4. One argument node qualifies as plainly value-typed
  ## iff it is not the `nnkHiddenAddr` Nim inserts to pass a `var` formal
  ## (that node IS how a `var` argument is spelled in typed AST — there is
  ## no other reliable signal) and its `typeKind` is in `inertArgTypeKinds`.
  ##
  ## One unwrapping rule: `echo`-shaped varargs. Nim lowers `echo a, b` to a
  ## single `nnkHiddenStdConv`/`ntyVarargs` argument wrapping an `nnkBracket`
  ## of the actual elements — so recurse into the bracket and require every
  ## element to qualify, rather than rejecting the vararg wrapper itself
  ## (which is not one of the listed scalar kinds and would otherwise always
  ## read as non-inert).
  if a.kind == nnkHiddenAddr: return false
  if a.kind == nnkHiddenStdConv and a.typeKind == ntyVarargs:
    if a.len < 2 or a[1].kind != nnkBracket: return false
    for elem in a[1]:
      if not isInertArg(elem): return false
    return true
  a.typeKind in inertArgTypeKinds

proc isInertOpaqueCall(n: NimNode): bool =
  ## Issue #163 slice 4. `n` is a call node (`nnkCall`/`nnkCommand`-shaped,
  ## typed) reaching the opaque-call arm in STATEMENT position (the caller
  ## already knows the result is unused — see the two call sites in
  ## `parseStmt`/`parseExpr`). An opaque call is inert — safe for the walker
  ## to treat as a no-op, no taint, no `w.sawUnknown` — iff every actual
  ## argument is plainly value-typed per `isInertArg`. (The "no bound
  ## result" half of the predicate is enforced structurally: this proc is
  ## only ever consulted from the statement-position call site, where
  ## `retName == ""` by construction; the expression-position site never
  ## calls it — see the comment there.)
  ##
  ## Soundness: with no bound result and nothing writable passed in, the
  ## only channel left for such a callee to influence the SUT is a
  ## module-level global. The walker does not model globals AT ALL — a SUT
  ## branching on a module-level `var` already answers `sxUnknown` with an
  ## unclassified `KeyError` at its OWN read site, independently of any
  ## opaque call ahead of it. So a SUT that could observe a global mutation
  ## from an "inert" call has already degraded before this predicate ever
  ## runs, and dropping the taint here cannot introduce a false verdict.
  ## What this DOES forgo is a callee that never returns or that raises
  ## (`echo` can raise `IOError`) — a pre-existing, symmetric gap: an opaque
  ## call AFTER the target branch was already invisible to it before this
  ## change. So this trades away call-ORDERING precision, never soundness.
  for i in 1 ..< n.len:
    if not isInertArg(n[i]): return false
  true

proc hasBorrowPragma(impl: NimNode): bool =
  ## Phase 15 G5. True when `impl` (an `nnkProcDef`) carries a `{.borrow.}`
  ## pragma — an `nnkPragma` child containing `ident"borrow"`. The borrow
  ## pragma's typed form is a bare `nnkIdent "borrow"` (confirmed by AST dump).
  ## RFC-parser-normalization N2: `impl` here is always ALREADY resolved by
  ## the caller (`borrowInfoFor`/the rune-compare intercept/
  ## `ensureProcRegistered`'s `geDistinctBarrier` check) — a membership-only
  ## check, so it routes onto `walkableRoutineKinds` directly (no
  ## `resolveRoutineImpl` call here; there is no fresh `getImpl` to guard).
  if impl.kind notin walkableRoutineKinds: return false
  let prag = impl.pragma
  if prag.kind != nnkPragma: return false
  for p in prag:
    let name =
      case p.kind
      of nnkIdent, nnkSym: p.strVal
      of nnkExprColonExpr, nnkCall:
        if p[0].kind in {nnkIdent, nnkSym}: p[0].strVal else: ""
      else: ""
    if name == "borrow":
      return true
  false

proc distinctParamOf(impl: NimNode): string =
  ## Phase 15 G5. The name of the first `distinct T` formal of `impl`, or ""
  ## when it has none. Shared by `ensureProcRegistered`'s `geDistinctBarrier`
  ## check and `isBodilessForeign` (which defers to that check).
  let formal = impl[3]
  if formal.kind == nnkFormalParams:
    for i in 1 ..< formal.len:
      let id = formal[i]
      if id.kind == nnkIdentDefs:
        let pc = classifyType(id[id.len - 2])
        if pc.ty.kind == itDistinct:
          return pc.ty.distinctName
  ""

const havocAllGlobals* = "*"
  ## RFC-0005 S8as. In an `IRStmt.opaqueHavoc` summary: every writable
  ## module-level variable the program reaches (`SymexProgram.globals`).

type OpaqueEffects = object
  ## RFC-0005 S8as. What an inert opaque call may write
  ## (`opaqueWriteSummary`).
  inert: bool          ## false: the summary cannot be bounded by rebinding
  havoc: seq[string]   ## IR names, or `havocAllGlobals`
  heapTys: seq[NimNode]
    ## RFC-0005 S8ax: the `ref`/`ptr` types whose cells the call may write
    ## (`IRStmt.opaqueHeapTys`)
  heapAll: bool        ## RFC-0005 S8ax: every heap cell (`opaqueHeapAll`)
  why: string          ## RFC-0005 S8ax: why the call is not inert

proc isBodilessForeign(calleeSym: NimNode): bool  ## RFC-0005 S8as fwd decl
proc objectInherits(t: NimNode): bool  ## RFC-0005 S8ax fwd decl

proc reachRecFields(rec: NimNode; acc: var OpaqueEffects;
                    seen: var seq[string])

proc reachPointees(t: NimNode; acc: var OpaqueEffects;
                   seen: var seq[string]) =
  ## RFC-0005 S8ax. Every `ref`/`ptr` type a value of type `t` can hold,
  ## through object and tuple fields (variant arms included), container
  ## elements, distinct bases and pointees: the heaps a write through such
  ## a value may land in (`OpaqueEffects.heapTys`). A pointee that takes
  ## part in inheritance (a ref of a base addresses a subtype's cells, keyed
  ## by the subtype), an untyped `pointer` or `cstring`, a routine type (a
  ## closure's environment), or a shape not recognised reaches every heap
  ## (`heapAll`).
  if t.isNil:
    acc.heapAll = true
    return
  var impl = t.getTypeImpl
  if impl.kind == nnkVarTy and impl.len == 1: impl = impl[0].getTypeImpl
  let key = t.repr & "|" & impl.repr
  if key in seen: return
  seen.add key
  case impl.kind
  of nnkSym:
    if macros.strVal(impl) in ["pointer", "cstring"]: acc.heapAll = true
  of nnkRefTy, nnkPtrTy:
    if impl.len < 1:
      acc.heapAll = true
      return
    let pointee = impl[0]
    if objectInherits(pointee):
      acc.heapAll = true
      return
    acc.heapTys.add t
    reachPointees(pointee, acc, seen)
  of nnkObjectTy:
    if impl.len >= 3 and impl[2].kind != nnkEmpty:
      reachRecFields(impl[2], acc, seen)
  of nnkTupleTy, nnkTupleConstr:
    for f in impl:
      let ft = if f.kind == nnkIdentDefs: f[^2] else: f
      reachPointees(ft, acc, seen)
  of nnkBracketExpr:
    for i in 1 ..< impl.len:
      reachPointees(impl[i], acc, seen)
  of nnkDistinctTy:
    reachPointees(impl[0], acc, seen)
  of nnkEnumTy, nnkRange, nnkInfix:
    discard
  else:
    acc.heapAll = true

proc reachRecFields(rec: NimNode; acc: var OpaqueEffects;
                    seen: var seq[string]) =
  ## RFC-0005 S8ax. `reachPointees` over an object's record list, every
  ## arm of a record case included.
  case rec.kind
  of nnkIdentDefs:
    reachPointees(rec[^2], acc, seen)
  of nnkRecList, nnkRecCase, nnkOfBranch, nnkElse:
    for c in rec:
      if c.kind in {nnkIdentDefs, nnkRecList, nnkRecCase, nnkOfBranch,
                    nnkElse}:
        reachRecFields(c, acc, seen)
  else: discard

proc notInert(acc: var OpaqueEffects; why: string) =
  ## RFC-0005 S8ax. The summary cannot be bounded: say why once.
  if acc.inert:
    acc.inert = false
    acc.why = why

proc isNoReturnRoutine(sym: NimNode): bool =
  ## RFC-0005 S8ax. `sym` is a routine declared `{.noreturn.}` (`quit`).
  if sym.kind != nnkSym: return false
  let impl =
    try: sym.getImpl
    except CatchableError: return false
  if impl.kind notin RoutineNodes: return false
  let prag = impl.pragma
  if prag.kind != nnkPragma: return false
  for p in prag:
    let name =
      case p.kind
      of nnkIdent, nnkSym: macros.strVal(p)
      of nnkExprColonExpr, nnkCall:
        if p[0].kind in {nnkIdent, nnkSym}: macros.strVal(p[0]) else: ""
      else: ""
    if name == "noreturn": return true
  false

proc scanOpaqueEffects(n: NimNode; acc: var OpaqueEffects;
                       seen, stack: var seq[NimNode]) =
  ## RFC-0005 S8as. See `opaqueWriteSummary`.
  if n == nil or not acc.inert: return
  case n.kind
  of nnkSym:
    let k = symKind(n)
    if k in {nskVar, nskLet} and isModuleGlobal(n):
      if not irTypeRefFree(classifyType(n.getTypeInst).ty):
        # RFC-0005 S8ax: a global that reaches heap cells (S8as declined
        # it): every cell its type reaches may be written, and a `var` one
        # is rebound below.
        var rs: seq[string]
        reachPointees(n.getTypeInst, acc, rs)
      if k == nskVar:
        let nm = globalIRName(n)
        if nm notin acc.havoc: acc.havoc.add nm
    elif k == nskMethod or isBodilessForeign(n):
      # Dynamic dispatch, or a body outside Nim: it may write any
      # module-level variable (a foreign routine through an exported one,
      # or a callback), and (RFC-0005 S8ax) any cell one of them reaches.
      if havocAllGlobals notin acc.havoc: acc.havoc.add havocAllGlobals
      acc.heapAll = true
    elif isNoReturnRoutine(n):
      # RFC-0005 S8ax: the call may end the process instead of returning.
      acc.notInert("it may call `" & macros.strVal(n) & "`, which never " &
                   "returns")
    elif isUserRoutine(n):
      # Routine membership through the Cluster N vocabulary
      # (`isUserRoutine`'s `userRoutineSymKinds`, then the
      # `resolveRoutineImpl` nil-core), as `tsymex_phase15_N2_kindgate_audit`
      # requires: an iterator or converter has no walkable impl and makes
      # the call non-inert below.
      if containsSym(stack, n):
        # RFC-0005 S8ax: a recursion may not end, and a replay of a witness
        # through it would not either.
        acc.notInert("it may recurse through `" & macros.strVal(n) &
                     "`, which may not terminate")
        return
      if containsSym(seen, n): return
      seen.add n
      block:
        let impl = resolveRoutineImpl(n)
        if impl == nil:
          acc.notInert("`" & macros.strVal(n) & "` has no body to read")
          return
        if isNestedRoutine(n):
          for c in nestedCaptureSyms(impl):
            let ck = symKind(c)
            let writable = ck == nskVar or
              (ck == nskParam and c.getTypeInst.kind == nnkVarTy)
            if not irTypeRefFree(classifyType(c.getTypeInst).ty):
              # RFC-0005 S8ax: a capture that reaches heap cells, a `let`
              # one included: its cells are written through it (S8as
              # declined a writable one and missed a `let` one).
              var rs: seq[string]
              reachPointees(c.getTypeInst, acc, rs)
            if not writable: continue
            let nm = c.strVal
            if nm notin acc.havoc: acc.havoc.add nm
        stack.add n
        scanOpaqueEffects(impl[6], acc, seen, stack)
        stack.setLen(stack.len - 1)
      # A stdlib routine writes no variable of the program except through
      # its arguments and the callbacks it is given, and both are scanned
      # where they are named.
  of nnkCast, nnkAsmStmt:
    # RFC-0005 S8ax: a forged pointer or foreign code inline may write any
    # module-level variable and any heap cell (S8as declined it). A local
    # of the caller is reachable only through an argument, which the call
    # site summarises, or through an address, which is a heap cell.
    if havocAllGlobals notin acc.havoc: acc.havoc.add havocAllGlobals
    acc.heapAll = true
  of nnkWhileStmt:
    # RFC-0005 S8ax: a loop may not end, and a replay of a witness through
    # it would not either.
    acc.notInert("its body holds a `while` loop, which may not terminate")
  else:
    for c in n: scanOpaqueEffects(c, acc, seen, stack)

proc opaqueWriteSummary(calleeSym: NimNode): OpaqueEffects =
  ## RFC-0005 S8as. The effect summary of an inert-shaped opaque call
  ## (statement position): the module-level `var`s its body may write,
  ## transitively through every routine it names, and for a routine
  ## declared inside another, the enclosing variables it captures. Before
  ## S8as such a call was a no-op for the walk, on the argument that "the
  ## walker does not model globals at all"; S8an made it model them, so a
  ## global the call wrote kept its old value: a false `sxUnsat`. The walk
  ## now rebinds every name listed to a fresh value of its type
  ## (`feGlobalHavoc`).
  ##
  ## RFC-0005 S8ax: and the heaps it may write -- every `ref`/`ptr` type a
  ## global or capture it reaches can hold (`reachPointees`), or every heap
  ## after a cast, inline assembly, a method or a foreign routine. S8as
  ## declined each of those. The call's arguments are summarised by
  ## `opaqueArgEffects`, its raises by `opaqueRaiseTypes`.
  ##
  ## Not inert (the walk keeps the call's `feOpaqueCallUnmodelled` taint)
  ## when the call may not return (RFC-0005 S8ax: a `while` loop, a
  ## recursion, a `{.noreturn.}` routine -- a witness through it is
  ## replayed, and the replay would not end), or a routine has no body to
  ## read.
  result.inert = true
  var seen, stack: seq[NimNode]
  scanOpaqueEffects(calleeSym, result, seen, stack)

proc lvalueRoot(lv: NimNode; heapSteps: var seq[NimNode]): NimNode  ## RFC-0005 S8ax fwd decl
proc addrActualLvalue(a: NimNode): NimNode  ## RFC-0005 S8ax fwd decl
proc addrCellLocal(e: NimNode): NimNode  ## RFC-0005 S8bs fwd decl
proc ptrFormalStaysLocal(callee: NimNode; idx: int;
                         seen: var seq[string]): bool  ## RFC-0005 S8ax fwd decl

proc opaqueArgEffects(n, calleeSym: NimNode; acc: var OpaqueEffects) =
  ## RFC-0005 S8ax. The writes an opaque call `n` may make through its
  ## arguments, added to `acc` (S8as kept any call with a non-value
  ## argument opaque). A `var` actual's root variable is rebound when the
  ## actual is the variable or a path into its value; through a
  ## dereference the cells are written instead, and the root keeps its
  ## value. Every heap a ref-carrying actual reaches may be written. An
  ## `addr` actual is a `var` one while the pointer cannot outlive the call
  ## (`ptrFormalStaysLocal`). RFC-0005 S8be: a routine-typed actual reaches
  ## every heap and capture cell (it may run a closure).
  for i in 1 ..< n.len:
    let a = n[i]
    if isInertArg(a): continue
    var lv: NimNode = nil
    if a.kind == nnkHiddenAddr and a.len == 1:
      lv = a[0]
      if isVarIndirection(lv): lv = lv[0]
    else:
      let alv = addrActualLvalue(a)
      if alv != nil:
        var seenP: seq[string]
        if not ptrFormalStaysLocal(calleeSym, i - 1, seenP):
          acc.notInert("the pointer `addr " & alv.repr & "` may outlive " &
                       "the call")
          return
        lv = alv
    if lv != nil:
      var heapSteps: seq[NimNode]
      let root = lvalueRoot(lv, heapSteps)
      if root.isNil or symKind(root) notin {nskVar, nskParam, nskLet,
                                            nskForVar, nskTemp}:
        acc.notInert("the `var` argument `" & lv.repr & "` has no root " &
                     "variable")
        return
      var rs: seq[string]
      reachPointees(root.getTypeInst, acc, rs)
      if heapSteps.len == 0:
        let nm = if isModuleGlobal(root): globalIRName(root) else: root.strVal
        if nm notin acc.havoc: acc.havoc.add nm
      continue
    # RFC-0005 S8be: a routine-typed actual is summarised as any other
    # value: `reachPointees` makes a routine type reach every heap
    # (`heapAll`), and the walk havocs every capture cell for it. S8ax
    # declined the call (`feOpaqueCallUnmodelled`).
    var rs: seq[string]
    reachPointees(a.getTypeInst, acc, rs)

proc opaqueRaiseTypes(calleeSym: NimNode; ctx: ParseCtx): seq[string] =
  ## RFC-0005 S8ax. The catchable exception types `calleeSym` may raise:
  ## its inferred `raises` list (`std/effecttraits`, which follows every
  ## routine it calls; `Defect`s are not tracked, see the walker's inert
  ## arm). Before S8ax an inert opaque call never raised:
  ## `try: boom(v) except ValueError: ...` was a false `sxUnsat`, and a
  ## target after a call that always raises a false `sxSat`.
  let lst =
    try: getRaisesList(calleeSym)
    except CatchableError: newEmptyNode()
  for tn0 in lst:
    let tn = canonicalExnTypeSym(tn0)
    let typeId = if tn.kind in {nnkSym, nnkIdent}: macros.strVal(tn)
                 else: tn.repr
    collectUserExnAncestors(tn, ctx)
    if typeId notin result: result.add typeId

const anyDefect* = "Defect"
  ## RFC-0005 S8be. In `IRStmt.opaqueDefects`: a `Defect` of a type the scan
  ## cannot name (an unscanned routine, a closure, a re-raise). The walk
  ## raises it as `Defect` and splits it over the handlers in scope.

proc implMagic*(impl: NimNode): string =
  ## RFC-0005 S8be / S8bl. The `{.magic: "X".}` name of the routine
  ## declaration `impl`, or "". A magic's semantics are the compiler's: its
  ## body, when it has one, is documentation or a VM fallback, never what
  ## the call does. (Batch 6: S8be's `routineMagic` and S8bl's, which took
  ## the declaration, are this one reader.)
  if impl == nil or impl.kind notin RoutineNodes or impl.len < 5: return ""
  let prag = impl[4]
  if prag.kind != nnkPragma: return ""
  for p in prag:
    if p.kind == nnkExprColonExpr and p.len == 2 and
       p[0].kind in {nnkIdent, nnkSym} and macros.strVal(p[0]) == "magic" and
       p[1].kind in {nnkStrLit .. nnkTripleStrLit, nnkIdent, nnkSym}:
      return macros.strVal(p[1])
  ""

proc routineMagic(sym: NimNode): string =
  ## RFC-0005 S8be. The `{.magic.}` name of the routine `sym` (`"AddI"` for
  ## `system.+` on `int`), or "" when it has none.
  if sym.kind != nnkSym: return ""
  let impl =
    try: sym.getImpl
    except CatchableError: return ""
  implMagic(impl)

const
  overflowMagics = ["AddI", "SubI", "MulI", "DivI", "ModI", "AddI64",
                    "SubI64", "MulI64", "DivI64", "ModI64", "UnaryMinusI",
                    "UnaryMinusI64", "AbsI", "Inc", "Dec", "Succ", "Pred"]
    ## RFC-0005 S8be. Overflow-checked integer magics (`OverflowDefect`).
  divMagics = ["DivI", "ModI", "DivI64", "ModI64", "DivU", "ModU",
               "DivU64", "ModU64"]
    ## RFC-0005 S8be. Integer division magics (`DivByZeroDefect`).
  rangeMagics = ["Chr", "Inc", "Dec", "Succ", "Pred"]
    ## RFC-0005 S8be. Magics that check a range or enum bound
    ## (`RangeDefect`): `chr`, and a step past an enum's or a subrange's end.
  maxDefectScanDepth = 8
    ## RFC-0005 S8be. How many routines deep `scanOpaqueDefects` reads; a
    ## deeper call counts as `anyDefect`.

proc typeIsDefect(t: NimNode; ctx: ParseCtx): string =
  ## RFC-0005 S8be. The exception type id of `t` (`ref T` or `T`) when `T`
  ## is a `Defect` or a subtype of one, else "".
  var s = t
  if s.kind == nnkSym and s.symKind == nskType:
    let impl = s.getTypeImpl
    if impl.kind == nnkRefTy and impl.len == 1: s = impl[0]
  elif s.kind in {nnkRefTy, nnkBracketExpr} and s.len >= 1:
    s = s[^1]
  s = canonicalExnTypeSym(s)
  if s.kind notin {nnkSym, nnkIdent}: return ""
  collectUserExnAncestors(s, ctx)
  let nm = macros.strVal(s)
  if isDefect(exnTypeTable, nm, ctx.userExnHierarchy): nm else: ""

func intConvExact(dst, src: NimTypeKind): bool =
  ## RFC-0005 S8be. A conversion from `src` to `dst` that never checks a
  ## range: the same kind, a widening into a 64-bit integer, or an ordinal
  ## to a float.
  const signedNarrow = {ntyInt8, ntyInt16, ntyInt32, ntyChar, ntyBool,
                        ntyEnum, ntyUInt8, ntyUInt16, ntyUInt32}
  if dst == src: return true
  case dst
  of ntyInt, ntyInt64: src in signedNarrow + {ntyInt, ntyInt64}
  of ntyUInt, ntyUInt64: src in {ntyUInt8, ntyUInt16, ntyUInt32, ntyChar,
                                 ntyBool, ntyUInt, ntyUInt64}
  of ntyFloat, ntyFloat32, ntyFloat64: true
  else: false

func isRoutineDefNode(n: NimNode): bool =
  n.kind in RoutineNodes

proc runRoutineDef(sym: NimNode): NimNode =
  ## RFC-0005 S8be. The definition of the routine a call to `sym` runs (a
  ## proc, func, converter, iterator or method; not a template or macro,
  ## expanded before the scan sees it), or nil for any other symbol -- a
  ## parameter or variable holding a closure.
  if sym.kind != nnkSym or sym.symKind in {nskTemplate, nskMacro}: return nil
  let impl =
    try: sym.getImpl
    except CatchableError: return nil
  if impl.kind in RoutineNodes - {nnkTemplateDef, nnkMacroDef}: impl
  else: nil

proc scanOpaqueDefects(n: NimNode; acc: var seq[string];
                       seen: var seq[NimNode]; depth: int; ctx: ParseCtx) =
  ## RFC-0005 S8be. See `opaqueDefectTypes`.
  template add(t: string) =
    if t notin acc: acc.add t
  if n == nil or anyDefect in acc and acc.len > 12: return
  if isRoutineDefNode(n): return   # a routine declared here is not run here
  case n.kind
  of nnkBracketExpr:
    if n.len == 2:
      let k = n[0].typeKind
      let tk = if k == ntyVar: n[0].getTypeInst[0].typeKind else: k
      var ix = n[1]
      while ix.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and
            ix.len >= 1:
        ix = ix[^1]
      let literal = ix.kind in {nnkCharLit .. nnkUInt64Lit}
      # An array's literal index is checked by the compiler; a tuple's is a
      # field. Any other index of a container is checked at run time.
      if tk in {ntySequence, ntyString, ntyOpenArray, ntyVarargs,
                ntyUncheckedArray} or tk == ntyArray and not literal:
        add "IndexDefect"
      # The index's hidden conversion to the array's range is the index
      # check itself (`IndexDefect`), not a `RangeDefect`.
      scanOpaqueDefects(n[0], acc, seen, depth, ctx)
      scanOpaqueDefects(ix, acc, seen, depth, ctx)
    else:
      for c in n: scanOpaqueDefects(c, acc, seen, depth, ctx)
  of nnkCheckedFieldExpr:
    add "FieldDefect"
    for c in n: scanOpaqueDefects(c, acc, seen, depth, ctx)
  of nnkConv, nnkHiddenStdConv, nnkHiddenSubConv:
    if n.len >= 2:
      let src = n[^1]
      if src.kind notin {nnkCharLit .. nnkFloat128Lit, nnkNilLit} and
         src.typeKind != ntyNone and n.typeKind != ntyNone and
         n.typeKind in {ntyInt .. ntyUInt64, ntyChar, ntyEnum, ntyRange,
                        ntyBool} and
         src.typeKind notin {ntyFloat .. ntyFloat128} and
         not intConvExact(n.typeKind, src.typeKind):
        add "RangeDefect"
      scanOpaqueDefects(src, acc, seen, depth, ctx)
  of nnkRaiseStmt:
    if n.len == 0 or n[0].kind == nnkEmpty:
      add anyDefect   # a re-raise of what the arm caught
    else:
      let d = typeIsDefect(n[0].getTypeInst, ctx)
      if d.len > 0: add d
      scanOpaqueDefects(n[0], acc, seen, depth, ctx)
  of nnkCall, nnkInfix, nnkPrefix, nnkPostfix, nnkCommand, nnkCallStrLit,
     nnkHiddenCallConv:
    let f = n[0]
    let fDef = runRoutineDef(f)
    if fDef != nil:
      let magic = routineMagic(f)
      if magic.len > 0:
        if magic in overflowMagics: add "OverflowDefect"
        if magic in divMagics: add "DivByZeroDefect"
        if magic in rangeMagics:
          if magic == "Chr" or n.len > 1 and
             n[1].typeKind in {ntyEnum, ntyRange, ntyChar, ntyVar}:
            add "RangeDefect"
      elif fDef.kind == nnkMethodDef:
        add anyDefect   # dispatched: any override may run
      elif not containsSym(seen, f):
        seen.add f
        # A converter's or iterator's body is scanned like a proc's.
        if fDef.len > 6 and fDef[6].kind != nnkEmpty:
          if depth >= maxDefectScanDepth: add anyDefect
          else: scanOpaqueDefects(fDef[6], acc, seen, depth + 1, ctx)
        # No body: foreign code, which raises no Nim exception.
    elif f.kind != nnkSym or f.symKind notin {nskTemplate, nskMacro}:
      # A closure or a routine-valued variable: any code at all.
      if f.typeKind in {ntyProc, ntyVar} or f.kind != nnkSym:
        add anyDefect
    for i in 1 ..< n.len: scanOpaqueDefects(n[i], acc, seen, depth, ctx)
  else:
    for c in n: scanOpaqueDefects(c, acc, seen, depth, ctx)

proc opaqueDefectTypes(calleeSym: NimNode; ctx: ParseCtx): seq[string] =
  ## RFC-0005 S8be. The `Defect` types an inert opaque call may raise, which
  ## no `raises` list tracks: an index (`IndexDefect`), a checked integer
  ## operation (`OverflowDefect`, `DivByZeroDefect`), a range-checked
  ## conversion (`RangeDefect`), a variant-arm field (`FieldDefect`), a
  ## `raise` of a `Defect` type -- in its body and, transitively, in every
  ## routine it calls (the stdlib's too, to `maxDefectScanDepth`). A call
  ## the scan cannot read (a closure, a method, a re-raise, too deep) adds
  ## `anyDefect`. Empty: the body raises no `Defect` (a `nil` dereference is
  ## a SIGSEGV in the default build, not a Defect; see the S8be notes).
  ##
  ## Before S8be the walk forked none: `IndexDefect` out of an opaque call
  ## was a false `sxUnsat`, and a `finally` reached only through it was
  ## never walked.
  var seen = @[calleeSym]
  let impl = resolveRoutineImpl(calleeSym)
  if impl == nil or impl.len <= 6 or impl[6].kind == nnkEmpty: return
  scanOpaqueDefects(impl[6], result, seen, 0, ctx)
proc hasVarFormal(impl: NimNode): bool =
  ## RFC-0005 S8bl (item 1). `impl` declares a `var` parameter.
  if impl == nil or impl.kind notin walkableRoutineKinds: return false
  let formal = impl.params
  for i in 1 ..< formal.len:
    let id = formal[i]
    if id.kind == nnkIdentDefs and id.len >= 2 and
       id[id.len - 2].kind == nnkVarTy:
      return true
  false

proc isGeneratedHook(sym: NimNode): bool =
  ## RFC-0005 S8bl (item 1). `sym` is a lifetime hook the compiler
  ## synthesised for a type (`=wasMoved`, `=destroy`, `=copy`, `=sink`,
  ## `=dup`, `=trace`): semcheck rewrites `wasMoved(a)` to a call of one.
  ## Its declaration is not a routine a parse can read -- the formals are an
  ## `nnkArgList` -- and parsing it crashed the compile.
  if sym.kind != nnkSym or sym.strVal.len < 2 or sym.strVal[0] != '=':
    return false
  let impl = resolveRoutineImpl(sym)
  if impl == nil or impl.kind notin walkableRoutineKinds: return false
  for f in impl.params:
    if f.kind == nnkArgList: return true
  false

type VarMagicModel* = enum
  ## RFC-0005 S8bl (item 1). How the parser treats a system magic with a
  ## `var` parameter (`varParamMagics`).
  vmModelled   ## modelled exactly for the argument shapes its arm accepts;
               ## any other shape declines at the call, naming the magic
  vmDeclined   ## every call declines, naming the magic and the reason

const varParamMagics*: seq[tuple[magic: string; model: VarMagicModel;
                                 note: string]] = @[
  ## RFC-0005 S8bl (item 1). Every magic of the system module that takes a
  ## `var` parameter (Nim 2.2), and its treatment. A call of one that no
  ## arm models reaches `ensureProcRegistered`, which declines it naming the
  ## magic (`varMagicDecline`) -- before S8bl it was registered with an
  ## empty body, a silent no-op on its argument. The guard test
  ## (`tsymex_rfc0005_s8bl_magicscan`) scans the stdlib's system sources for
  ## `var`-parameter magics and fails on one missing here.
  ("Swap", vmModelled,
   "`swap(a, b)`: both read, then both written (`parseVarMagicStmt`)"),
  ("WasMoved", vmModelled,
   "`wasMoved(x)` / `=wasMoved(x)`: x becomes its type's zero"),
  ("Move", vmModelled,
   "`move(x)`: x's value, and x becomes its type's zero (`parseMoveExpr`)"),
  ("SetLengthSeq", vmModelled, "`setLen(s, n)` on a seq (`isSetLen`)"),
  ("SetLengthStr", vmModelled, "`setLen(s, n)` on a string (`isSetLen`)"),
  ("SetLengthSeqUninit", vmModelled,
   "`setLenUninit(s, n)`: a shrink is `setLen`'s; a grow declines (the " &
   "new slots are uninitialised memory)"),
  ("AppendStrCh", vmModelled, "`add(s, c)` on a string (the #145 arms)"),
  ("AppendStrStr", vmModelled,
   "`add(s, t)` / `s &= t` on a string (the #145 arms, the `&=` arm)"),
  ("AppendSeqElem", vmModelled, "`add(s, x)` on a seq (the #145 arms)"),
  ("Inc", vmModelled, "`inc(x[, y])` / `x += y` (the R8 and S8bc arms)"),
  ("Dec", vmModelled, "`dec(x[, y])` / `x -= y` (the R8 and S8bc arms)"),
  ("New", vmModelled,
   "`new(x)`: a fresh zeroed cell; `unsafeNew(x, size)` declines (an " &
   "uninitialised allocation of a given size)"),
  ("NewSeq", vmModelled, "`newSeq(s, n)` (S8bc; batch 5's `iekSeqNew`)"),
  ("Asgn", vmModelled, "`=`(d, s) / `=copy` / `=sink`: the assignment `d = s`"),
  ("Incl", vmModelled,
   "`incl(s, k)` on a builtin `set[T]` (S8bq, `parseBitSetInclExcl`)"),
  ("Excl", vmModelled,
   "`excl(s, k)` on a builtin `set[T]` (S8bq, `parseBitSetInclExcl`)"),
  ("Destroy", vmDeclined,
   "an explicit destructor call leaves its argument unspecified"),
  ("Trace", vmDeclined, "a cycle-collector hook over a raw environment pointer"),
  ("ShallowCopy", vmDeclined,
   "declared under the refc memory manager only; it shares the payload")]

proc varMagicDecline(ctx: ParseCtx; name, magic: string; key: string): string =
  ## RFC-0005 S8bl (item 1). The decline of a call to the system magic
  ## `magic` (routine `name`) with a `var` parameter that no parser arm
  ## modelled (`ensureProcRegistered`): a never-registered key, so the
  ## walker's missing-callee arm degrades the path that reaches it.
  var why = "a magic no arm models (not in `varParamMagics`)"
  for m in varParamMagics:
    if m.magic == magic:
      why = if m.model == vmDeclined: m.note
            else: "modelled only for the argument shapes its arm accepts: " &
                  m.note
  ctx.declineCallee(feUnsupportedOp,
    "system magic `" & name & "` (magic \"" & magic & "\") with a `var` " &
    "parameter is not modelled here -- " & why & " -- path degraded to " &
    "sxUnknown (feUnsupportedOp)", key)

const foreignImportPragmas = ["importc", "importcpp", "importobjc",
                              "importjs", "dynlib"]
  ## RFC-0005 S8b. The pragmas that give a routine a FOREIGN definition: its
  ## body is supplied by C/C++/ObjC/JS or a shared library, never by Nim.

proc isBodilessForeign(calleeSym: NimNode): bool =
  ## RFC-0005 S8b (§2.2's silent-substitution class). True when `calleeSym`
  ## is a routine with no Nim body because it is defined outside Nim
  ## (`foreignImportPragmas`) -- e.g. `proc c_abs(x: int32): int32
  ## {.importc: "abs", header: "<stdlib.h>".}`.
  ##
  ## Before S8b such a callee fell through to `ensureProcRegistered`, was
  ## registered, and `parseCalleeImpl` parsed its EMPTY body: the walker
  ## "called" a proc that does nothing and returns the zero default. A target
  ## reachable only through the foreign result was then a false `sxUnsat`
  ## with no error recorded at all. The call is an effect symex cannot see
  ## into, which is exactly what the opaque-call arm models (a fresh result
  ## and a `feOpaqueCallUnmodelled` path taint), so both call-position
  ## dispatches route it there, next to `{.symexOpaque.}`.
  ##
  ## Two exclusions keep existing, more specific treatment first:
  ## `{.borrow.}` (the G5 borrow path) and a bodiless proc over a `distinct`
  ## formal (`ensureProcRegistered`'s `geDistinctBarrier` callee decline).
  if calleeSym.kind != nnkSym: return false
  let impl = resolveRoutineImpl(calleeSym)  ## RFC-parser-normalization N2
  if impl == nil or impl.kind notin walkableRoutineKinds: return false
  if impl[6].kind != nnkEmpty or hasBorrowPragma(impl): return false
  if distinctParamOf(impl).len > 0: return false
  for name in foreignImportPragmas:
    if hasSymexPragma(calleeSym, name): return true
  false

type BorrowInfo = object
  ## Phase 15 G5. Classification of an operator symbol as a `{.borrow.}` shim.
  isBorrow*:        bool
  returnsDistinct*: bool     ## true → arithmetic (re-box result as distinct);
                             ## false → comparison (raw bool result).
  distinctTy*:      IRType   ## the distinct return type to re-box into
                             ## (RFC-0005 S8ad: the type, so the walker can
                             ## allocate its sort; nil for a comparison).

proc borrowInfoFor(calleeSym: NimNode): BorrowInfo =
  ## Phase 15 G5. Classify an operator symbol: is it a `{.borrow.}` proc/func,
  ## and does it return the distinct type (arithmetic) or bool (comparison)? A
  ## borrow proc/func has NO real body — its `getImpl` body is a bare `Sym`
  ## (the base operator) — so it must NOT be body-parsed; the call routes
  ## through the borrow path instead. The return type is `impl[3][0]` (the
  ## FormalParams' return node): an `itDistinct` classification → arithmetic
  ## re-box; else (itBool) → comparison.
  ## RFC-parser-normalization N0: `impl.kind` was bare `!= nnkProcDef`, so a
  ## `func` borrow operator classified `isBorrow: false` and fell to the
  ## ordinary infix path (verdict/witness-inert at the time — the ordinary
  ## arithmetic/comparison arms eject both operands unconditionally and
  ## compute the same base result; only the `reboxDistinct` re-tagging was
  ## skipped). Widened alongside the C3/G8 sites.
  ## RFC-parser-normalization N2: the `getImpl` + kind-check step above is
  ## now `resolveRoutineImpl`; `hasBorrowPragma`'s own kind check (over the
  ## already-resolved `impl`) is a membership-only check on
  ## `walkableRoutineKinds`, unchanged in policy.
  if calleeSym.kind != nnkSym: return BorrowInfo(isBorrow: false)
  let impl = resolveRoutineImpl(calleeSym)
  if impl == nil or not hasBorrowPragma(impl):
    return BorrowInfo(isBorrow: false)
  let formal = impl[3]
  if formal.kind != nnkFormalParams or formal[0].kind == nnkEmpty:
    # A borrow with no return type would be a void operator — not a borrow we
    # model. Treat as non-borrow (falls through to the normal path).
    return BorrowInfo(isBorrow: false)
  let retCls = classifyType(formal[0])
  if retCls.ty.kind == itDistinct:
    BorrowInfo(isBorrow: true, returnsDistinct: true, distinctTy: retCls.ty)
  else:
    BorrowInfo(isBorrow: true, returnsDistinct: false, distinctTy: nil)

proc distinctBaseTypeNode(ty: NimNode): NimNode =
  ## RFC-0005 S8bc (item 2). The base type node of a `distinct` type node
  ## (`DSq` with `DSq = distinct seq[int]` -> the typed `seq[int]`), or nil
  ## when `ty` is not a named distinct type this can read. The node is the
  ## type section's own, so it is typed (`getTypeInst` reads it), unlike any
  ## node a macro could synthesize.
  var t = ty
  if t.kind == nnkVarTy and t.len == 1: t = t[0]
  if t.kind != nnkSym: return nil
  let impl = t.getImpl
  if impl.kind == nnkTypeDef and impl.len >= 3 and
     impl[2].kind == nnkDistinctTy and impl[2].len == 1:
    return impl[2][0]
  nil

proc borrowRoutineRewrite(n: NimNode):
    tuple[rw: NimNode, views: seq[tuple[node, baseTy: NimNode]]] =
  ## RFC-0005 S8bc (item 2). A call of a NON-operator `{.borrow.}` routine
  ## (`d.len`, `abs(m)`, `$m`, `inc(m)`), rewritten as a call of the routine
  ## it borrows. Nim gives a borrowed routine no body: its `getImpl` body is
  ## the base routine's symbol, and `f(a)` means `D(base(T(a)))` for each
  ## `distinct T` formal (the result rewrapped when `f` returns `D`). Before
  ## S8bc the call was walked as a user routine and its "body", that bare
  ## symbol, declined (`feUnsupportedStmtKind`) -- over a scalar base too.
  ##
  ## `rw` is `n` with its head replaced by the base routine's symbol and the
  ## SAME typed argument nodes. `views` (pushed onto `borrowBaseViews` while
  ## `rw` parses) classifies each argument of a distinct formal at the
  ## distinct's base type, and `rw` itself at the base of a distinct return
  ## type, so the base routine's own arms (a builtin model, or a user
  ## routine's walk) see `len(seq[int](d))`. Unwrapping and rewrapping are
  ## value pass-throughs, as a written `T(d)` / `D(x)` is (`nnkConv`).
  ##
  ## `rw` is nil (the call is left alone) for an operator (an infix `+`/`<`
  ## goes through `borrowIntercept`, and an operator called in call form
  ## through the A7 comparison arm), a callee that is not a borrow, an arity
  ## other than the borrow's formal count, or a distinct this cannot read
  ## the base of (`distinctBaseTypeNode`); that keeps the routine-call path's
  ## decline.
  if n.kind notin {nnkCall, nnkCommand, nnkPrefix} or n.len < 2: return
  let head = n[0]
  if head.kind != nnkSym: return
  let name = head.strVal
  if name.len == 0 or
     not (name[0] in {'a'..'z', 'A'..'Z', '_'} or name == "$"):
    return
  let impl = resolveRoutineImpl(head)
  if impl == nil or not hasBorrowPragma(impl) or impl[6].kind != nnkSym:
    return
  let formal = impl[3]
  if formal.kind != nnkFormalParams: return
  var formalTys: seq[NimNode]
  for i in 1 ..< formal.len:
    let id = formal[i]
    if id.kind != nnkIdentDefs: return
    for j in 0 ..< id.len - 2:
      # RFC-0005 S8bl: a formal with only a default (`last = -1`) has an
      # empty type node; its symbol carries the inferred type.
      formalTys.add(if id[id.len - 2].kind == nnkEmpty: id[j].getTypeInst
                    else: id[id.len - 2])
  if formalTys.len != n.len - 1: return
  var views: seq[tuple[node, baseTy: NimNode]]
  for i in 1 ..< n.len:
    if classifyType(formalTys[i - 1]).ty.kind != itDistinct: continue
    let baseTy = distinctBaseTypeNode(formalTys[i - 1])
    if baseTy == nil: return
    views.add (n[i], baseTy)
    # A `var` argument may arrive address-wrapped; the base routine's arm
    # classifies what it unwraps too.
    if n[i].kind in {nnkHiddenAddr, nnkHiddenDeref, nnkAddr} and n[i].len == 1:
      views.add (n[i][0], baseTy)
  var rw = copyNimNode(n)   # keeps `n`'s type (the borrow's return type)
  rw.add impl[6]
  for i in 1 ..< n.len: rw.add n[i]
  # The base routine's arms read its own arity. RFC-0005 S8bl (item 4): a
  # borrow declaring fewer formals than its base (`proc inc(m: var M)
  # {.borrow.}`, the base's `y = 1` defaulted) is the base with those
  # defaults, so each missing argument is the base's default when that is
  # a literal. It was left alone, and the call took the `inc` arm's decline
  # on a distinct receiver. (Nim 2.2.10's code generator crashes on a call
  # of such a borrow -- an `IndexDefect` in the compiler -- so no program
  # that runs one compiles; the parse is still exact for one that is only
  # analysed.)
  let baseImpl = resolveRoutineImpl(impl[6])
  if baseImpl == nil or baseImpl[3].kind != nnkFormalParams: return
  var baseDefaults: seq[NimNode]
  for i in 1 ..< baseImpl[3].len:
    let id = baseImpl[3][i]
    if id.kind != nnkIdentDefs: return
    for j in 0 ..< id.len - 2: baseDefaults.add id[id.len - 1]
  if baseDefaults.len < n.len - 1: return
  for i in n.len - 1 ..< baseDefaults.len:
    let d = baseDefaults[i]
    if d.kind notin {nnkCharLit .. nnkUInt64Lit, nnkFloatLit .. nnkFloat64Lit,
                     nnkStrLit .. nnkTripleStrLit}:
      return
    rw.add d
  if formal[0].kind != nnkEmpty and
     classifyType(formal[0]).ty.kind == itDistinct:
    let retBase = distinctBaseTypeNode(formal[0])
    if retBase == nil: return
    views.add (rw, retBase)
  (rw, views)

proc isUserCallee(sym: NimNode): bool =
  ## RFC-0005 S8c. The gate every builtin-by-name dispatch site consults: a
  ## call whose head resolved to a user routine (`isUserRoutine`) is walked
  ## as a routine call, never modelled as the builtin that shares its name.
  ## A `{.borrow.}` routine is the one exception: it IS the base type's
  ## builtin, by definition, and the borrow arms (`borrowIntercept`,
  ## `runeCompareIntercept`) model it as exactly that.
  if not isUserRoutine(sym): return false
  let impl = resolveRoutineImpl(sym)
  not (impl != nil and hasBorrowPragma(impl))

proc isBuiltinNamed(head: NimNode, names: openArray[string]): bool =
  ## RFC-0005 S8c. A call/operator head that names one of `names` AND is not
  ## a user callee. The structural recognisers (scan idioms, slice bounds,
  ## `new`, the assert expansion) match raw AST by head name; this is the
  ## same name test plus the symbol gate, so a user overload never completes
  ## a builtin shape. An untyped `nnkIdent` head (the isolation entry point)
  ## passes on its name alone, as before.
  head.kind in {nnkSym, nnkIdent} and head.strVal in names and
    not isUserCallee(head)

const markersModuleSuffix = "/nelli/engine/markers.nim"
  ## RFC-0005 S8c: where the three DSL markers are declared.

proc isMarkerCall(n: NimNode, name: string): bool =
  ## RFC-0005 S8c: a resolved (`nnkSym`) head is a marker only when it IS
  ## nelli's marker -- declared in `markers.nim` -- not a same-named user
  ## proc (which is walked as the routine it is). An untyped `nnkIdent`
  ## head matches by name, as before.
  if n.kind != nnkCall:
    return false
  let callee = n[0]
  case callee.kind
  of nnkIdent:
    callee.strVal == name
  of nnkSym:
    if callee.strVal != name: return false
    let impl = callee.getImpl
    impl.kind != nnkNilLit and
      impl.lineInfoObj.filename.replace('\\', '/').endsWith(markersModuleSuffix)
  else:
    false

proc isMarkerCall(n: NimNode): bool =
  isMarkerCall(n, "symexTarget") or
  isMarkerCall(n, "symexAssert") or
  isMarkerCall(n, "symexAssume")

proc isNewCall(n: NimNode): bool =
  ## Phase 15 R2 (ADR-0010). True iff `n` is a `new T` allocation expression —
  ## either the command form `new int` (`nnkCommand[Sym "new", T]`) or the call
  ## form `new(int)` (`nnkCall[Sym "new", T]`). The `new` magic returns a fresh
  ## `ref T`; the let-section parser lowers such an RHS to an `isNew` stmt
  ## (binding the let-name to the fresh `Ref_T` const) rather than `parseExpr`,
  ## which has no expression-context model for allocation.
  if n.isNil: return false
  if n.kind notin {nnkCall, nnkCommand} or n.len < 1: return false
  let head = n[0]
  let nm =
    if head.kind in {nnkOpenSymChoice, nnkClosedSymChoice} and head.len > 0:
      head[0].strVal
    elif head.kind in {nnkSym, nnkIdent}:
      head.strVal
    else: return false
  # RFC-0005 S8c: a user proc named `new` is a routine call, not allocation.
  nm == "new" and not (head.kind == nnkSym and isUserCallee(head))

proc callsFailedAssertImpl(n: NimNode): bool =
  ## Phase 15 E6. A raw `assert cond, msg` / `doAssert cond` lowers (after
  ## semcheck) to a `Call` to the system template `failedAssertImpl` in the
  ## then-body of an `if not (cond): …`. Recursively detect such a call so the
  ## enclosing `if` can be recognised as an assert expansion.
  if n.isNil: return false
  if n.kind in {nnkCall, nnkCommand} and n.len >= 1 and
     n[0].kind in {nnkSym, nnkIdent, nnkOpenSymChoice, nnkClosedSymChoice}:
    let head = n[0]
    let nm =
      if head.kind in {nnkOpenSymChoice, nnkClosedSymChoice} and head.len > 0:
        head[0].strVal
      else: head.strVal
    # RFC-0005 S8c: system's own `failedAssertImpl`, not a same-named user proc.
    if nm == "failedAssertImpl" and
       not (head.kind == nnkSym and isUserCallee(head)): return true
  for c in n:
    if callsFailedAssertImpl(c): return true
  false

proc findAssertFailsCond(n: NimNode): NimNode =
  ## Phase 15 E6. Scan a (typed) sub-AST for a raw-`assert` expansion and return
  ## the Nim node for the condition under which the assert FAILS (i.e. the
  ## `if`-arm condition `not (cond)` that guards the `failedAssertImpl` call) —
  ## or `nil` if `n` contains no assert. The walker lowers this to an implicit
  ## `raise AssertionDefect` guarded by that condition. (A SUT's explicit
  ## `symexAssert(...)` marker is handled separately and never reaches here.)
  if n.isNil: return nil
  if n.kind in {nnkIfStmt, nnkIfExpr}:
    for arm in n:
      if arm.kind in {nnkElifBranch, nnkElifExpr} and arm.len == 2 and
         callsFailedAssertImpl(arm[1]):
        return arm[0]
  for c in n:
    let r = findAssertFailsCond(c)
    if r != nil: return r
  nil

# ---- Expression parser -------------------------------------------------------

const fltTyNames = ["float", "float32", "float64"]
const intTyNames = ["int", "int8", "int16", "int32", "int64",
                    "uint", "uint8", "uint16", "uint32", "uint64"]

proc valueTypeName(node: NimNode): string =
  ## Phase 15 F5: resolved type name of a VALUE node (operand), via getTypeInst.
  ## (A bare `nnkSym` value resolves to its declared name, not its type, so we
  ## must always go through getTypeInst here.)
  ## RFC-0005 S8d: `typeSpelling` -- a user type named `int8`/`float32`/
  ## `bool` is spelled `user:<name>`, so the name-keyed conversion arms
  ## (`intTyNames`, `fltTyNames`, `"bool"`) never read it as the builtin.
  # RFC-0005 S8bc: a borrowed routine's argument is viewed at its base
  # (S8bl: through `dsl_typebridge.getTypeInst`).
  typeSpelling(node.getTypeInst)

proc typeNodeName(node: NimNode): string =
  ## Phase 15 F5: name of a TYPE node (the conversion target `n[0]`).
  ## RFC-0005 S8d: `typeSpelling`, as `valueTypeName` -- a conversion to, or
  ## `low`/`high` of, a user type named like a builtin is not the builtin.
  typeSpelling(node)

proc siteMsg*(n: NimNode, note: string): string =
  ## Round-6 A0 (siteMsg ownership — RFC "siteMsg ownership + a real gap it
  ## doesn't close"). The standing DoD requires every PARSE-TIME classified
  ## decline this RFC adds to open its `SymexErrorInfo.msg` with
  ## `<file>:<line>:<col>: ` so the site can be located directly from the
  ## message — the cautionary counter-example named by the RFC is the
  ## pre-existing `beBudgetExhausted` message, which carries no loop
  ## identity at all. Composes the three components every ad hoc decline
  ## message in this file already assembles by hand (location, the
  ## offending construct's `n.repr`, and a human note) so new call sites
  ## stop reinventing the concatenation.
  let li = n.lineInfoObj
  &"{li.filename}:{li.line}:{li.column}: {note} in `" & n.repr & "`"

proc siteLoc*(n: NimNode): string =
  ## Round-6 A3 (RFC "siteMsg ownership + a real gap it doesn't close",
  ## ~L1318-1352). The SAME `lineInfoObj`+`repr` components `siteMsg`
  ## assembles, but with no `note` slot — for a statement (like
  ## `isVariantConstructSym`) whose classified-decline message can only be
  ## built at WALK time, where no `NimNode` exists. A walk-time site glues
  ## its own dynamically-computed note onto this string VERBATIM; it must
  ## NOT attempt to reformat or re-derive file:line:col/`repr` from it.
  let li = n.lineInfoObj
  &"{li.filename}:{li.line}:{li.column}: `" & n.repr & "`"

proc declineUnsupportedFieldRead(n: NimNode, fieldName: string, fieldTy: IRType,
                                 preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  ## Round-6 Bug #2 (scoped decline, ADR/RFC fork-resolution 2026-08-15).
  ## `fieldTy` is a per-field UNSUPPORTED PLACEHOLDER
  ## (`isUnsupportedFieldPlaceholder`, `types.nim` — see its doc block for the
  ## full mechanism): `classifyObjectRecordFields` (`dsl_typebridge.nim`)
  ## marked this field's DECLARED type unsupported (today: `seq[T]` with an
  ## unbacked element kind — `fieldTy.kind` stays `itSeq`, only
  ## `seqUnsupportedFieldReason` is set; the field's real `seqElemTy` is
  ## preserved). Called from every `nnkDotExpr` field-access arm below at the
  ## point the field's type is resolved, BEFORE any real accessor IR
  ## (`mkField`/`mkVariantFieldStmt`) is built. Deposits the SND-1 taint
  ## (`mkUnsupported` → `isUnsupported`) on THIS READ's own statement — so
  ## only paths that actually reach this specific field read degrade to a
  ## classified `sxUnknown`; an object/variant merely ALLOCATED (or read on
  ## OTHER fields/arms) proves exactly as before (`allocateSym`'s `itSeq`
  ## arm, `runtime.nim`, never raises for this placeholder).
  ##
  ## The returned dummy is an EMPTY seq literal (`mkSeqLit(@[], seqElemTy)`),
  ## NOT a bare `mkIntLit(0)`: this read's result can be a sub-expression of
  ## a FURTHER accessor in the SAME statement (e.g. `p.options.len`, parsed
  ## as an outer `.len` `nnkDotExpr` whose receiver `p.options` recurses
  ## through `parseExpr` and lands here) — the SND-1 taint alone does not
  ## stop the WALKER from still structurally interpreting whatever this
  ## returns (taint-and-continue, not taint-and-halt), so a KIND-mismatched
  ## dummy (an int where a seq is structurally expected) risks a walker
  ## crash before the taint's `sxUnknown` demotion ever reports. An empty
  ## seq literal is exactly the shape B6's empty-literal rider already
  ## proved safe to allocate (`lowerSeqLit`, `runtime.nim`) — the VALUE is
  ## fake but the SHAPE is right, and SND-1's own soundness guarantee (any
  ## later `sxSat`/`sxUnsat` on this path is demoted to `sxUnknown` at the
  ## `isTargetLabel`/`routeRaise` chokepoints, regardless of what the fake
  ## value computes downstream) is what makes this sound, not the value's
  ## content.
  ##
  ## The decline reason renders `fieldTy.seqUnsupportedFieldReason` VERBATIM
  ## — that payload was built by `dsl_typebridge.fieldDeclineMsg` at the
  ## field's OWN declaration site (parse time, where a `NimNode` existed), so
  ## the message is honest about WHERE the field was declared unsupported,
  ## not merely that this read touched it (the same walk-time-renders-parse-
  ## time-location discipline `siteLoc` established for
  ## `isVariantConstructSym`).
  let reason = "read of field `" & fieldName & "` declined: " &
               fieldTy.seqUnsupportedFieldReason
  preamble.add ctx.declineAtSite(
    seNestedSeqUnsupported,
    siteMsg(n, reason),
    reason)   # kind is structured (unKind); N12: no raw kind-name parenthetical in the rendered msg
  mkSeqLit(@[], fieldTy.seqElemTy, declinedPlaceholder = true)

proc parseVariantCtorField(fieldName: string, fty: IRType,
                            byName: Table[string, NimNode], ctorNode: NimNode,
                            preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  ## Round-6 A1 (ADR-0029). Shared per-field extraction for a literal-
  ## discriminant variant constructor's active-arm/plain field — mirrors
  ## the `nnkObjConstr` itTuple path's byName-based field handling
  ## (P2a/P2b, below) for the two variant field groups (active-arm fields,
  ## always-present plain fields). Top-level (not nested inside the
  ## `of itVariant:` arm): a nested proc there would capture
  ## `preamble: var seq[IRStmt]` by reference, which Nim rejects as a
  ## memory-safety violation, so `preamble`/`ctx` are threaded explicitly
  ## instead. `ctorNode` is the enclosing `nnkObjConstr`, used only for
  ## diagnostics.
  let isRefField = fty.kind in {itRef, itPtr}
  if byName.hasKey(fieldName):
    let valNode = byName[fieldName]
    if isRefField and valNode.kind == nnkNilLit:
      return mkNil(fty)
    elif isRefField and refExprClassify(valNode).ty.kind notin {itRef, itPtr}:
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        "A1: ref-typed variant field `" & fieldName &
               "` initialised from `" & valNode.repr & "`, which does " &
               "not resolve to a genuine ref/ptr address — this " &
               "expression shape is out of scope",
        "A1: recursive ref-field " &
                                    "construction from an unresolvable " &
                                    "expression (feUnsupportedExprKind)")
      return mkNil(fty)
    else:
      return parseExpr(valNode, preamble, ctx)
  elif isRefField:
    return mkNil(fty)
  else:
    let zv = zeroValueForType(fty)
    if zv != nil:
      return zv
    else:
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        "A1: omitted variant field `" & fieldName & "` of type " &
               $fty.kind & " in `" & ctorNode.repr &
               "` has no clean zero-value encoding",
        "A1: omitted variant field `" &
                                    fieldName & "` zero-value " &
                                    "unmodeled (feUnsupportedExprKind)")
      return unsupportedFieldPlaceholder(fty)

proc isStdMathProc(calleeSym: NimNode): bool =
  ## Phase 15 F6: is `calleeSym` a proc defined in the Nim standard library
  ## (`lib/pure/math` or `lib/system`)? Used to route otherwise-unmodeled
  ## float-receiver calls (e.g. `ln`, `sin`) to `iekMathCall` so the runtime
  ## emits `feUnsupportedOp`, instead of `ensureProcRegistered` raising a
  ## compile-time `getImpl` failure. Uses the defining file path of the
  ## symbol's implementation; user procs live outside the stdlib tree.
  if calleeSym.kind != nnkSym:
    return false
  let impl = resolveRoutineImpl(calleeSym)  ## RFC-parser-normalization N2
  if impl == nil:
    return false
  let fn = impl.lineInfoObj.filename.replace('\\', '/')
  result = ("/pure/math" in fn) or ("/lib/system" in fn) or
           fn.endsWith("system.nim") or ("/system/" in fn)

proc isRuneTyped(node: NimNode): bool =
  ## True iff `node`'s Nim type is `std/unicode.Rune` (= `distinct int32` via
  ## RuneImpl). Mirrors the name-pair check in dsl_typebridge.classifyType (A7-S1
  ## intercept) so the two sites always agree. A user-defined `Rune` whose base
  ## type is NOT `RuneImpl` does NOT match (Invariant 3 — no accidental coercion).
  ## Used by the `$` interception sites in A7-S2 to route `$r` to `iekRuneToStr`
  ## BEFORE the `itInt` check (Rune classifies to itInt post-S1, so checking the
  ## classified kind alone would conflate Rune with a plain int).
  ## RFC-0005 S8d: decided by SYMBOL through the shared `isStdlibRuneSym`
  ## (the old name pair also matched a user's own `Rune`/`RuneImpl`).
  var ty = node.getTypeInst
  if ty.isNil: return false
  if ty.kind == nnkVarTy and ty.len == 1: ty = ty[0]
  isStdlibRuneSym(ty)

proc isAtomicIR(e: IRExpr): bool =
  ## RFC-parser-normalization A2a (Mechanism, #146/#149). True iff `e` needs
  ## no hoisting to serve as an operand: a literal, or an `iekVar` reference
  ## (covers BOTH a genuine local/param read AND an already-hoisted synthetic
  ## temp — `freshSynth` + `preamble.add` + `mkVar` is exactly this file's own
  ## established idiom for producing an atomic handle, already used by the
  ## `nnkDerefExpr` and `boolConv` arms above), OR an `iekStrAt` (`s[i]`, a
  ## single-hop byte read — no sub-operands of its own to normalise).
  ##
  ## `iekStrAt` is deliberately included despite being a compound-ish IR
  ## node (SND-4 deposits an inline OOB-defect fork whenever it lowers):
  ## `runtime.nim`'s CR-17(a) defensive guard (`ordering comparison on s[i]
  ## (char) is not modeled`) pattern-matches `e.lhs.kind == iekStrAt or
  ## e.rhs.kind == iekStrAt` on the IMMEDIATE operand of an ordering
  ## comparison — a walk-time shape check, not a data-flow one. Hoisting
  ## `s[i]` into a `let` and reading it back as `iekVar` would silently
  ## defeat that check (the comparison's operand becomes `iekVar`, never
  ## `iekStrAt`), turning a sound `sxUnknown` degrade (a known Z3 mixed-
  ## theory hang shape, ADR-0023/SND-3) into a fabricated, UNSOUND verdict
  ## — caught by `tsymex_snd3_loopdegrade.nim`'s SND-3-2/SND-3-4 regressing
  ## to `sxSat` during this slice's own validation. `s[i]` staying
  ## un-hoisted changes nothing else: the SND-4 OOB fork still deposits
  ## exactly once, whether `s[i]` sits inline or (pre-existing, un-A2a)
  ## behind a hand-written `let`.
  ##
  ## `iekStrLen`/`iekSeqLen` (`s.len`) are ALSO included, for a related but
  ## distinct reason discovered by the same validation pass
  ## (`tsymex_r4_slice_binding.nim`'s "free-int-param bound declines
  ## classified" cell): both are pure, zero-fault single-hop reads
  ## (`rhsHasInlineDefectFork` recurses to their receiver and stops — a
  ## bare-var receiver is never fault-bearing), but hoisting one into a
  ## `let` still manufactures ONE `preamble` entry where before there was
  ## none. When that operand sits inside a comparison that is itself an
  ## operand of a boolean `and`/`or` (e.g. `i > 0 and i < s.len`), the
  ## manufactured entry flips D1c's OWN fast-path predicate
  ## (`rhsPreamble.len == 0 and not rhsHasInlineDefectFork(rhsIR)`,
  ## `dsl_parser.nim` ~:1495) from the flat `mkBinop(bAnd, …)` fast path to
  ## the guarded if/temp path — a PURELY STRUCTURAL change (D1c's guarded
  ## and flat forms are semantically equivalent short-circuit encodings)
  ## that nonetheless changed a free int PARAM's downstream BV-vs-Int Z3
  ## allocation enough to silently defeat `runtime_strings.nim`'s
  ## `iekStrSubstr` CR-17-class decline (`loSV.kind != svInt` never firing
  ## because `i` now allocates Int instead of BV) — the sound classified
  ## `sxUnknown` this test pins became a live (here, merely lucky-fast)
  ## solve instead of the intended non-termination-avoiding decline.
  ## `s.len`/`seq.len` are the only two such kinds `rhsHasInlineDefectFork`
  ## unconditionally clears for a bare-var receiver AND that this
  ## validation pass actually exercised.
  ##
  ## RESOLVED (code review round 1 finding H1, RFC-parser-normalization
  ## #146): the residual, narrower version of this hazard flagged above —
  ## `rhsHasInlineDefectFork` also unconditionally clears `iekField` (:753),
  ## `iekIndex` (:755), and `iekContains` (:769) for bare-var/literal
  ## receivers, the same zero-fault-compound-shape property that earned
  ## `iekStrAt`/`iekStrLen`/`iekSeqLen` their spot above, yet none of the
  ## three is admitted here — is now characterized and permanently audited
  ## by `tests/tsymex_phase15_A2a_atomicir_audit.nim`. Part 1 pins twin
  ## (inline vs. hand-hoisted) verdict/witness equality for all three kinds
  ## as a comparison operand under a boolean `and`/`or` RHS (confirmed
  ## latent-but-benign at HEAD: every twin agrees, so this predicate's
  ## CURRENT non-membership for `iekField`/`iekIndex`/`iekContains` is not
  ## itself a soundness defect). Part 2 is a permanent `staticRead`-based
  ## scan of every SUBFIELD IR-kind shape-peek in `runtime.nim`/
  ## `runtime_strings.nim`, requiring each to sit in this allowlist, the
  ## always-atomic literal/var set, or a documented exemption — so any
  ## FUTURE walk-time shape-match against a kind this predicate does not
  ## admit fails the build immediately, closing the "no completeness audit"
  ## gap the review named, without needing to re-run this analysis by hand.
  e != nil and e.kind in {iekIntLit, iekBoolLit, iekFloatLit, iekStrLit,
                          iekVar, iekStrAt, iekStrLen, iekSeqLen}

proc isResolvedBoolAndOr(n: NimNode): bool =
  ## RFC-parser-normalization A2b/M3 (#146 round 1). The ONE sound signal for
  ## "is this and/or infix the BOOLEAN (short-circuit) form, as opposed to
  ## Nim's same-spelled BITWISE form (e.g. `(hi shl 8) or lo` on uint16)" —
  ## shared by both call sites that need the answer (the bAnd/bOr arm of
  ## `parseExpr`, and `isBooleanShortCircuitInfix` below).
  ##
  ## `n[0].kind == nnkSym` MUST run first: an untyped node's `n.typeKind` can
  ## carry a bogus non-`ntyNone` value (observed `ntyCString`/`ntyFloat32` on
  ## different untyped and/or shapes — see `scratchpad/probe_typekind*.nim`),
  ## so `n.typeKind != ntyNone` is NOT a sound pre-check for this family,
  ## even though it's the idiom used elsewhere in this file for nodes that
  ## don't have and/or's magic-operator quirk. `n[0]` — the operator symbol
  ## itself — is reliable: it resolves to `nnkSym` only on the typed/
  ## production path, where overload resolution has bound it to a concrete
  ## proc; the untyped isolation path (`tsymex_phase1_dsl.nim`, ADR-0002)
  ## leaves it a bare, unresolved `nnkIdent`.
  ##
  ## Round-6 A5 (`g8_multi_param`/`g10_smoke`, reachable via Cluster G
  ## multi-param generic dispatch): `n[0].kind == nnkSym` alone is NOT
  ## sufficient to make `classifyType(n)` on the call node itself safe. `n`
  ## can be a node reached through `ensureProcRegistered`'s own
  ## `monomorphize()` (~:5444) — a purely SYNTACTIC identifier substitution
  ## (`T`/`U` -> concrete type nodes) that never re-runs Nim's real
  ## semchecker over the substituted tree. The `and`/`or` operator itself
  ## still resolves to `nnkSym` in this context (magic `And`/`Or` binds
  ## independent of the still-generic operand types), but `n`'s OWN
  ## `getTypeInst` legitimately has nothing to report — the SAME bogus-
  ## typeKind gap the paragraph above already documents, just surfacing
  ## through `getTypeInst` (a hard, non-catchable "node has no type" compile
  ## error — confirmed via a `try`/`except` probe that this bypasses Nim's
  ## exception machinery entirely) instead of through `typeKind`.
  ##
  ## Fix: derive boolean-vs-bitwise from `n[0]` — the RESOLVED OPERATOR
  ## SYMBOL's own proc signature — instead of from `classifyType(n)` on the
  ## call node. `n[0].getTypeImpl` is always a genuine, fully-resolved
  ## `nnkProcTy` (the symbol table entry for whichever concrete `and`/`or`
  ## overload bound, independent of the call node's own type annotation);
  ## its return-type node is real, resolved AST unaffected by
  ## `monomorphize`'s substitution, so `classifyType` on THAT is safe —
  ## gated by the standing DoD's `typeKind != ntyNone` idiom per clause (d)
  ## (this is a NEW classifyType call site).
  if n[0].kind != nnkSym: return false
  let sig = n[0].getTypeImpl
  if sig.kind != nnkProcTy or sig.len < 1 or sig[0].len < 1: return false
  let retTy = sig[0][0]
  retTy.typeKind != ntyNone and classifyType(retTy).ty.kind == itBool

proc isResolvedBitwiseAndOr(n: NimNode): bool =
  ## The structural complement of `isResolvedBoolAndOr` above, used by the
  ## bAnd/bOr arm of `parseExpr` (:1720-ish) to pick between the three-way
  ## and/or dispatch: an UNTYPED and/or node (bare `nnkIdent` operator) is
  ## the boolean carve-out and never reaches here; a resolved (`nnkSym`
  ## operator) node that `isResolvedBoolAndOr` rejects is the BITWISE
  ## chokepoint path; a resolved node `isResolvedBoolAndOr` accepts is D1c's
  ## boolean short-circuit path.
  ##
  ## The `n[0].kind == nnkSym` conjunct is LOAD-BEARING, not redundant with
  ## `not isResolvedBoolAndOr(n)` alone: dropping it lets an untyped and/or
  ## node (where `isResolvedBoolAndOr` is false only because `n[0].kind !=
  ## nnkSym` short-circuits it) satisfy this predicate and get misrouted
  ## into the bitwise chokepoint instead of the untyped boolean carve-out —
  ## this exact regression happened once already, when 4c642ea's
  ## simplification invisibly dropped the conjunct and was later restored
  ## by 11c72cf. Keep both conjuncts explicit.
  n[0].kind == nnkSym and not isResolvedBoolAndOr(n)

proc isBooleanShortCircuitInfix(n: NimNode): bool =
  ## RFC-parser-normalization A2a, Mechanism constraint 1 (#146/#149). The
  ## shared disambiguator for "is `n` an `and`/`or` operand under D1c's own
  ## boolean short-circuit handling" — the operator alone cannot tell (Nim
  ## spells the BITWISE `and`/`or` with the SAME identifiers); `isResolvedBoolAndOr`
  ## (M3, RFC #146 round 1 — see its doc comment) makes the call. True iff
  ## `n` is an `nnkInfix` whose operator is `and`/`or` AND `isResolvedBoolAndOr(n)`.
  ##
  ## M3 history: before this unification, this proc independently gated on
  ## `n.typeKind != ntyNone` — the same idiom A2b found unsound for and/or
  ## and replaced at its own call site (the bAnd/bOr arm), but left dormant
  ## here. A concrete repro attempt (untyped `not (p and q)`/`not (p or q)`
  ## through the isolation entry, pinned in `tsymex_phase1_dsl.nim`) found
  ## this was never actually reachable through natural Nim source: `not`
  ## binds tighter than `and`/`or` (precedence 10 vs 4), so `not (p and q)`
  ## requires parens, and in untyped (unsemchecked) AST those parens survive
  ## as a literal `nnkPar` wrapper — the `n.kind == nnkInfix` conjunct below
  ## already excludes that wrapper before the old `n.typeKind` conjunct was
  ## ever reached. This unification is therefore predicate-parity hygiene
  ## (one sound signal for the boolean-vs-bitwise question instead of two),
  ## not a behavior-changing fix — confirmed by the characterization pins in
  ## `tsymex_phase1_dsl.nim` passing unchanged, and by every typed-path test
  ## in the Phase 15 suite passing byte-identically.
  n.kind == nnkInfix and n.len == 3 and
    isBuiltinNamed(n[0], ["and", "or"]) and  ## RFC-0005 S8c: not a user `and`
    isResolvedBoolAndOr(n)

proc flattenShortCircuitChain(n: NimNode, opName: string,
                              into: var seq[NimNode]) =
  ## RFC-0005 S8t. The operands of a boolean short-circuit chain of ONE
  ## operator (`a and b and c`, however parenthesised), in evaluation order.
  ## Nim evaluates `(a and b) and c` and `a and (b and c)` identically: `a`;
  ## then `b` only if `a` allowed it; then `c` only if `b` did. An operand
  ## is descended into exactly when `parseExpr` would route it to the same
  ## boolean `and`/`or` arm: a builtin (not a user `and`, S8c), not the
  ## bitwise form (`isResolvedBitwiseAndOr`), and the same operator. A
  ## different operator (`(a or b) and c`) stays one operand, lowered by its
  ## own recursive parse.
  let u = if n.kind == nnkPar and n.len == 1: n[0] else: n
  if u.kind == nnkInfix and u.len == 3 and
     u[0].kind in {nnkIdent, nnkSym} and u[0].strVal == opName and
     not isUserCallee(u[0]) and not isResolvedBitwiseAndOr(u):
    flattenShortCircuitChain(u[1], opName, into)
    flattenShortCircuitChain(u[2], opName, into)
  else:
    into.add n

type ShortCircuitPart = tuple[pre: seq[IRStmt], ir: IRExpr]
  ## RFC-0005 S8t. One parsed operand of a short-circuit chain: the
  ## statements its evaluation hoisted, and its value.

proc shortCircuitPartIsPure(p: ShortCircuitPart): bool =
  ## D1c's fast-path test for a non-first operand: nothing hoisted and no
  ## inline defect fork, so evaluating it unconditionally changes nothing.
  p.pre.len == 0 and not rhsHasInlineDefectFork(p.ir)

proc lowerShortCircuitParts(op: IRBinop, parts: seq[ShortCircuitPart],
                            preamble: var seq[IRStmt],
                            ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8t. Lowers a flattened `and`/`or` chain (D1c's short-circuit
  ## model) with ONE guard temporary whose guards NEST:
  ##   and:  let sc = a; if sc: (<b's pre>; sc = b; if sc: (<c's pre>; sc = c))
  ##   or:   the same with `if not sc:`
  ## A pure operand (`shortCircuitPartIsPure`) joins the value before it
  ## flat (`sc = b and c`), as D1c's fast path always did.
  ##
  ## Before S8t each binary node got its own temporary, CHAINED
  ## (`let sc2 = sc1; if sc2: ...`), so the path on which an early operand
  ## was false still reached every later guard as a fresh fork: n operands
  ## with raising reads walked 2^(n-1) paths (12 operands: 2049 Z3 calls in
  ## `if`, `while`, `symexAssert` and `let`; S8q split only `symexAssume`).
  ## Nested, that path leaves the chain at the first false guard: n + 1
  ## paths. Short-circuit order is unchanged: operand k's hoisted statements
  ## (its raising reads) run only inside the guard of operand k-1.
  preamble.add parts[0].pre
  var acc = parts[0].ir
  var k = 1
  while k < parts.len and shortCircuitPartIsPure(parts[k]):
    acc = mkBinop(op, acc, parts[k].ir)
    inc k
  if k == parts.len:
    return acc
  let sc = freshSynth(ctx, "sc")
  preamble.add mkLet(sc, tBool(), acc)
  proc guardOf(): IRExpr =
    if op == bAnd: mkVar(sc)                # and: go on only while true
    else: mkUnop(uNot, mkVar(sc))           # or:  go on only while false
  proc nest(k: int): seq[IRStmt] =
    result = parts[k].pre
    var cur = parts[k].ir
    var j = k + 1
    while j < parts.len and shortCircuitPartIsPure(parts[j]):
      cur = mkBinop(op, cur, parts[j].ir)
      inc j
    result.add mkAssign(sc, cur)
    if j < parts.len:
      result.add mkIf(@[mkBranch(guardOf(), mkBlock(nest(j)))], nil,
                      join = true)
  # RFC-0005 S8w: every guard is a JOIN (`IRStmt.ifJoin`): the walker merges
  # the guard's two outcomes back into one path. Nesting (S8t) already kept
  # a same-operator chain to n + 1 exits, but those exits all flowed on, and
  # an operand of the OTHER operator (`(a or b)` inside an `and` chain) is
  # this same lowering one level down, so each such operand doubled the
  # paths reaching the rest of the chain: 2^m for m of them. Joined, the
  # chain leaves as one path whose `sc` is the chain's value; the reads
  # stay under their guards (a raise is still forked only inside the guard
  # that reaches it).
  preamble.add mkIf(@[mkBranch(guardOf(), mkBlock(nest(k)))], nil,
                    join = true)
  mkVar(sc)

proc parseAtomicOperand(n: NimNode, preamble: var seq[IRStmt],
                        ctx: ParseCtx): IRExpr =
  ## RFC-parser-normalization A2a (D2, #146/#149 Mechanism). The ONLY way to
  ## obtain an operand for a non-short-circuit binary/comparison/unary op.
  ## Parses `n` via `parseExpr`; if the result is already atomic
  ## (`isAtomicIR` — literal / `iekVar` / an existing temp), returns it
  ## unchanged. Otherwise binds a fresh `let` into `preamble` and returns a
  ## `mkVar` reference to it, so the walker's `lower`/`lowerBool` never see a
  ## compound expression tree in operand position — only atoms.
  ##
  ## No-ops (plain `parseExpr` result, no hoist) whenever `ctx.inGuardCond`
  ## is set — Mechanism constraint 4 (the guard-cond carve-out; see
  ## `ParseCtx.inGuardCond`'s doc comment and `mkShortCircuitWhile`).
  ##
  ## Also no-ops when `n` carries no semchecked type (`n.typeKind ==
  ## ntyNone`): hoisting needs `classifyType(n)` to declare the fresh
  ## `let`'s `IRType`, and `classifyType`/`getTypeInst` hard-error at
  ## compile time ("node has no type") on an untyped node — the SAME
  ## pre-check idiom this file already uses before every other
  ## `classifyType` call on a not-necessarily-typed node (e.g. the
  ## `pred`/`succ` and rune-compare intercepts above). This is not merely
  ## defensive: `dsl_parser.nim`'s own isolation entry point (`parseExpr(n:
  ## NimNode): IRExpr`, no `preamble`/`ctx` params) feeds genuinely untyped
  ## AST fixtures straight to this parser (ADR-0002, `tsymex_phase1_dsl.nim`)
  ## and hard-errors itself if ANY preamble content appears — so an untyped
  ## compound operand must stay un-atomized here, exactly as it was
  ## pre-A2a. Every REAL (typed-macro) entry point (`symexTarget`/
  ## `symexAssert`/`symexFind`/…) always supplies fully-typed nodes, so this
  ## carve-out never fires on the production path this chokepoint exists
  ## for.
  ##
  ## Callers MUST NEVER apply this to an operand of a boolean short-circuit
  ## `and`/`or` (constraint 1 — `isBooleanShortCircuitInfix`; that's D1c's
  ## own guarded handling, A2b's scope) — this proc has no view of its
  ## parent context and cannot enforce that exclusion itself.
  ##
  ## Constraints 2+3 (defect-fork ordering / left-to-right evaluation) hold
  ## by construction: `n`'s own inline defect-fork deposits happen inside the
  ## `parseExpr` call below, in `preamble`, BEFORE this proc's own hoisted
  ## `let` (if any) is appended right after — so a caller that parses
  ## operands in Nim's left-to-right order via successive
  ## `parseAtomicOperand` calls never reorders anything.
  let ir = parseExpr(n, preamble, ctx)
  if ctx.inGuardCond or isAtomicIR(ir) or n.typeKind == ntyNone:
    return ir
  let tmp = freshSynth(ctx, "atomic")
  let ty = classifyType(n).ty
  preamble.add mkLet(tmp, ty, ir)
  mkVar(tmp)

proc keepInlineRaiseOrder(l: IRExpr; a: NimNode; mark: int;
                          preamble: var seq[IRStmt]; ctx: ParseCtx) =
  ## RFC-0005 S8bi. Called after a pair of `parseAtomicOperand` calls, with
  ## `l` the first operand (from `a`) and `mark` the preamble length between
  ## the two. `parseAtomicOperand`'s ordering argument (constraints 2+3
  ## above) assumes an operand's raises are in `preamble` once it returns,
  ## which does not hold for one left INLINE that raises when it lowers:
  ## `s[i]` (`iekStrAt`, kept inline for CR-17(a)). When the second operand
  ## then hoists anything, its `let`s ran first: in `s[i] == chr(f(x))` the
  ## closure's `ValueError` was raised on runs where Nim raises
  ## `IndexDefect` from `s[i]`, and a handler reached only that way was
  ## `sxUnsat`. `l` is now also evaluated, for its raise, in a `let` placed
  ## before the second operand's; it stays inline in the expression (its
  ## second lowering forks nothing on the survivors of the first).
  if preamble.len > mark and not ctx.inGuardCond and isAtomicIR(l) and
     rhsHasInlineDefectFork(l) and a.typeKind != ntyNone:
    let tmp = freshSynth(ctx, "evalOrder")
    preamble.insert(mkLet(tmp, classifyType(a).ty, l), mark)

proc parseOperandPair(a, b: NimNode; preamble: var seq[IRStmt];
                      ctx: ParseCtx): (IRExpr, IRExpr) =
  ## RFC-0005 S8ax. `parseAtomicOperand` of a binary operator's two
  ## operands, with the left one read where Nim reads it when the right
  ## one's statements may write (`orderOperands`). RFC-0005 S8be: inside a
  ## `while` guard too. S8ax left the guard in the parser's order and relied
  ## on the walk's read-before-write check (`lowerClosureCall`), which
  ## declines (`ceCaptureByRefUnmodelled`) what the order here decides.
  ##
  ## RFC-0005 batch 5: S8bi's `keepInlineRaiseOrder` first. An inline left
  ## operand that raises when it lowers (`s[i]`) is also evaluated, for its
  ## raise, in a `let` ending its own statements, ahead of the right one's;
  ## the order below then treats that `let` as the left operand's own.
  let m0 = preamble.len
  let l = parseAtomicOperand(a, preamble, ctx)
  let m1 = preamble.len
  let r = parseAtomicOperand(b, preamble, ctx)
  let before = preamble.len
  keepInlineRaiseOrder(l, a, m1, preamble, ctx)
  let m1k = m1 + (preamble.len - before)
  var ops = @[l, r]
  orderOperands(preamble, @[m0, m1k], ops, @[IRType(nil), nil], omOperands,
                ctx)
  (ops[0], ops[1])

proc parseOrderedArgs(n: NimNode; first: int; preamble: var seq[IRStmt];
                      ctx: ParseCtx; mode = omOperands): seq[IRExpr] =
  ## RFC-0005 S8ax. `parseExpr` of `n[first ..< n.len]` (a call's arguments,
  ## or with `omElements` a constructor's elements), each read where Nim
  ## reads it (`orderOperands`). A by-address argument (`var`) is left as
  ## it is.
  var marks: seq[int]
  var tys: seq[IRType]
  var fixed: seq[bool]
  for i in first ..< n.len:
    let c = if n[i].kind == nnkExprColonExpr: n[i][1] else: n[i]
    marks.add preamble.len
    tys.add(if c.typeKind != ntyNone: classifyType(c).ty else: nil)
    fixed.add c.kind == nnkHiddenAddr
    result.add parseExpr(c, preamble, ctx)
  orderOperands(preamble, marks, result, tys, mode, ctx, fixed)   # S8be: guards too

proc parseCtorFieldsInOrder(n: NimNode; objTy: IRType;
                            preamble: var seq[IRStmt];
                            ctx: ParseCtx): Table[string, IRExpr] =
  ## RFC-0005 S8ax. The present non-ref fields of the object constructor
  ## `n`, parsed in SOURCE order, which is the order Nim fills them in, each
  ## read where Nim reads it (`orderOperands`). The constructor then
  ## assembles them in the type's declared order; before S8ax it also
  ## parsed them in that order, so a field written by a call in a field
  ## after it in the declaration but before it in the source was read
  ## before the call.
  var marks: seq[int]
  var tys: seq[IRType]
  var names: seq[string]
  var irs: seq[IRExpr]
  for k in 1 ..< n.len:
    let child = n[k]
    if child.kind != nnkExprColonExpr: continue
    let ix = objTy.fieldNames.find(child[0].strVal)
    if ix < 0 or objTy.fields[ix].kind in {itRef, itPtr}: continue
    marks.add preamble.len
    tys.add objTy.fields[ix]
    names.add child[0].strVal
    irs.add parseExpr(child[1], preamble, ctx)
  orderOperands(preamble, marks, irs, tys, omElements, ctx)   # S8be: guards too
  for j, nm in names: result[nm] = irs[j]

proc lowHighIntLit(tyName: string, wantLow: bool): int64 =
  ## Round-6 A0: the int64 bit-pattern for `low(tyName)`/`high(tyName)`,
  ## `tyName` guaranteed (by the caller) to be one of `intTyNames`. Unsigned
  ## values that overflow `int64` (`high(uint64)`/`high(uint)`) are
  ## reinterpreted via `cast`, mirroring the existing `nnkUIntLit` arm above
  ## (`mkIntLit(n.intVal)`), which already stores oversized unsigned literals
  ## as their raw bit pattern — `mkIntLit` itself carries no width/signedness
  ## (that is recovered from context downstream), so this is the same
  ## encoding every other int literal in this parser already uses.
  case tyName
  of "int8":   (if wantLow: int64(low(int8))   else: int64(high(int8)))
  of "int16":  (if wantLow: int64(low(int16))  else: int64(high(int16)))
  of "int32":  (if wantLow: int64(low(int32))  else: int64(high(int32)))
  of "int64":  (if wantLow: low(int64)         else: high(int64))
  of "int":    (if wantLow: int64(low(int))    else: int64(high(int)))
  of "uint8":  (if wantLow: 0'i64 else: int64(high(uint8)))
  of "uint16": (if wantLow: 0'i64 else: int64(high(uint16)))
  of "uint32": (if wantLow: 0'i64 else: int64(high(uint32)))
  of "uint64": (if wantLow: 0'i64 else: cast[int64](high(uint64)))
  of "uint":   (if wantLow: 0'i64 else: cast[int64](high(uint)))
  else:
    raiseAssert "lowHighIntLit: " & tyName & " not in intTyNames"

proc intTyWidth(tyName: string): int =
  ## Round-6 B2. Bit width of an `intTyNames` member — mirrors
  ## `lowHighIntLit`'s own per-name dispatch (SND-4 "mirror, don't
  ## reinvent"). `int`/`uint` are this platform's native (64-bit) width,
  ## matching `classifyType`'s `tInt(64, ...)` mapping (`dsl_typebridge.nim`).
  case tyName
  of "int8", "uint8":  8
  of "int16", "uint16": 16
  of "int32", "uint32": 32
  of "int64", "uint64", "int", "uint": 64
  else:
    raiseAssert "intTyWidth: " & tyName & " not in intTyNames"

proc intTySigned(tyName: string): bool =
  ## Round-6 B2. `IRType.signed` for an `intTyNames` member: every `uint*`
  ## spelling is unsigned, every other member (`int`/`intN`) is signed.
  not tyName.startsWith("u")

proc normalizeIntTyName(tyName: string): string =
  ## Round-6 B2 rider. `byte` is a plain (non-distinct) alias for `uint8` in
  ## `system` — Nim's typed AST preserves the ALIAS SPELLING rather than
  ## unwrapping it (`classifyType` carries its own dedicated `"byte"`
  ## text-match arm, `dsl_typebridge.nim:565`, for the identical reason: if
  ## the typed AST resolved `byte` straight to `"uint8"`, that arm would be
  ## dead code). Without normalizing it first, `intTyNames` membership/
  ## width/signedness lookups miss the RFC's own PRIMARY consumer shape
  ## (`uint16(b) shl 8` with `b: byte`, chapulin `protocol.nim:93` — `b`
  ## comes off a `seq[byte]`) and fall through to the untouched pre-B2
  ## identity pass-through.
  ##
  ## No OTHER stdlib alias resolves into the int family this way: checked
  ## `Natural`/`Positive` (the other candidates a search would turn up) —
  ## both are RANGE types (`range[0..high(int)]` / `range[1..high(int)]`,
  ## `dsl_typebridge.nim`'s own doc comment), not plain aliases, so they
  ## keep their existing, unrelated `classifyType` range handling and never
  ## reach this int-family width-conversion path at all (a `range[...]`
  ## VALUE converted via `int(...)` classifies through the range arm, never
  ## text-matches an `intTyNames` member here).
  ##
  ## Round-6 B7-rider (ADR-0028 Leg 2, closes the char-widening witness-
  ## corruption companion bug): `char` normalizes to `"uint8"` too, for the
  ## SAME class of reason `byte` does — Nim's `char` is ordinally an 8-bit
  ## UNSIGNED value (never sign-extends), just under a DISTINCT (non-alias)
  ## type name `intTyNames` never listed, so `isIntFamilyName("char")` was
  ## FALSE and a `uint16(<charExpr>)` conversion fell all the way through to
  ## this proc's caller's bare pass-through arm — SILENTLY DROPPING the
  ## widening entirely (the RHS lowered as an 8-bit `svBV8`, Nim's own
  ## DECLARED 16-bit type on the `let` binding notwithstanding — `isLet`'s
  ## walker arm, `runtime.nim`, binds whatever `lower()` returns with NO
  ## width coercion for a non-literal RHS). Confirmed empirically (isolated
  ## repro: `let hi = uint16(s[0]); let lo = uint16(s[1]); let combined =
  ## (hi shl 8) or lo; combined == 0x4142'u16`): the missing widening left
  ## `combined` an 8-bit value; comparing it to the 16-bit literal
  ## `0x4142'u16` truncated the literal to its low byte (`0x42`) at
  ## `coerceIntLit`'s own literal-shaping step, so the checked property
  ## degenerated to `lo == 0x42` with `hi` COMPLETELY UNCONSTRAINED — `sxSat`
  ## is technically correct (`'A','B'` genuinely satisfies the REAL, intended
  ## property), but the reported witness reflects Z3's free (don't-care)
  ## choice for `hi`'s underlying byte, NOT the value the SOURCE property
  ## actually depends on — replaying the reported witness through the real
  ## widen+shl+or expression does NOT reproduce `0x4142`. This is NOT an
  ## extraction bug (`evalStrBytes`/`getStringContents` faithfully report
  ## what the (mis-scoped) constraint actually pinned) — it is a PARSE-TIME
  ## MODELING GAP, structurally the same class B2's own "narrowing/
  ## reinterpret identity pass-through was silently unsound" finding
  ## describes, just for a source type B2 never covered. Mapping `char` to
  ## `"uint8"` here (unsigned, width 8) makes `isIntFamilyName`/
  ## `intTyWidth`/`intTySigned` treat it exactly like `byte` at every
  ## existing call site: `uint16(<char>)`/`int32(<char>)`/etc. now WIDEN
  ## (zero-extend, since char/uint8 is unsigned) through the SAME
  ## `iekConvIntWidth` primitive B2 already built; `char(<byte-or-uint8>)`
  ## normalizes to the SAME width+signedness on both sides and falls to the
  ## existing harmless same-width-different-spelling identity pass-through
  ## (correct: a `byte`↔`char` reinterpretation is bit-identical, no
  ## conversion needed); `char(<a wider int>)` NARROWS and correctly
  ## classified-declines, mirroring `byte`'s own narrowing decline.
  if tyName in ["byte", "char"]: "uint8" else: tyName

proc isIntFamilyName(tyName: string): bool =
  ## Round-6 B2 rider. Membership test that includes the `byte` alias
  ## (see `normalizeIntTyName`) without widening the shared `intTyNames`
  ## const itself — `intTyNames` also gates unrelated call sites
  ## (`lowHighIntLit`'s `low`/`high` magic fold) that this rider does not
  ## touch.
  normalizeIntTyName(tyName) in intTyNames

proc declineIntWidthConv(n: NimNode, preamble: var seq[IRStmt], ctx: ParseCtx,
                          note, src, tgt: string): IRExpr =
  ## Round-6 B2 (RFC-chapulin-hardening) shared classified decline for the
  ## two RECORDED-DECLINE int-conversion shapes (narrowing / same-width
  ## signedness reinterpret) — SND-4 "mirror, don't reinvent" mirror of the
  ## existing CR-2a/A0/A1 decline idiom used throughout this file: a
  ## parse-time `sevError` (opens with `siteMsg`) + `mkUnsupported` SND-1
  ## taint, then a TYPE-CORRECT dummy via `zeroValueForType` — never an
  ## unbound `mkVar` (both shapes are ordinary, reachable Nim; a dangling
  ## `iekVar` would be read at walk time and KeyError, the exact hazard A0's
  ## own decline comment documents).
  ##
  ## Round-6 B2 rider (standing DoD clause (d)): `classifyType(n)` is gated
  ## on `n.typeKind != ntyNone` — the exact guard idiom A5 introduced after
  ## discovering `monomorphize()`'s syntactic substitution can leave a
  ## typed-AST node with genuinely nothing for `getTypeInst` to report even
  ## though the node otherwise looks resolved. `n` here is an ordinary
  ## explicit-conversion `nnkConv` node, so the guard is expected to hold in
  ## every reachable shape today; it costs nothing when it does, and falls
  ## back to the untyped `mkIntLit(0)` dummy (still sound — SND-1's taint is
  ## already registered above, independent of the dummy's own type) on the
  ## day it doesn't.
  preamble.add ctx.declineAtSite(
    feUnsupportedExprKind,
    siteMsg(n, "B2: " & note & " int conversion `" & src & "` -> `" &
                      tgt & "` (RFC-chapulin-hardening B2 recorded decline)"),
    "B2: " & note & " int conversion " & src & "->" &
                                tgt & " (feUnsupportedExprKind)")
  let dummy =
    if n.typeKind != ntyNone: zeroValueForType(classifyType(n).ty)
    else: nil
  (if dummy != nil: dummy else: mkIntLit(0))

proc isPromoteSoundEligibleParam(operand: NimNode, operandTy: IRType): bool =
  ## Issue #163 review (rev item 2 follow-up) soundness carve-out, factored
  ## out so every int-width-conversion call site shares ONE answer instead of
  ## re-deriving it (the R11/R15/R16 "parallel rule drifts from the
  ## classifier" failure mode this review has hit repeatedly). A bare
  ## reference to one of the CURRENT proc's own formal parameters
  ## (`operand.kind == nnkSym and symKind(operand) == nskParam`) whose
  ## classified type carries a proven range AND is signed is exactly the
  ## shape `runtime.nim`'s `promoteSound` (issue #161) promotes at top-level
  ## param entry to a Z3 UNBOUNDED Int (`svInt`) rather than a fixed-width
  ## BV. `mkConvIntWidth`'s walker (`lowerConvIntWidth`, `runtime.nim`) hard-
  ## asserts its operand is ALWAYS a raw BV -- true for every case it was
  ## built for, but NOT true for a promoted param: routing one through it
  ## regressed a correct `sxUnsat` to `sxUnknown` (confirmed empirically,
  ## `nnkHiddenStdConv` arm below). Skip the width-conversion wrapper for
  ## exactly this carve-out -- the identity pass-through is independently
  ## sound here via `promoteSound`, since a promoted param's value is already
  ## an unbounded Z3 Int with no modulus to wrap against.
  operand.kind == nnkSym and symKind(operand) == nskParam and
  operandTy.hasRange and operandTy.signed

proc isIntLiteralNode(n: NimNode): bool =
  ## #163 regression fix (post-round-9 gate). Nim gives an un-suffixed
  ## integer literal a provisional default type (`int`, width 64) and, when
  ## the literal is then used somewhere requiring a NARROWER fixed-width
  ## int -- e.g. the `2` in `x * 2` where `x: int32`, resolving the `*`
  ## overload to `system.\`*\`(x, y: int32): int32` -- wraps the LITERAL
  ## itself in `nnkHiddenStdConv`, not the variable. `classifyType` of that
  ## whole node reports the narrower target width (`int32`), while
  ## `classifyType` of the wrapped literal reports its own provisional
  ## width (`int`, 64) -- so from the 678c6ce gate's point of view this is
  ## indistinguishable from a genuine narrowing conversion, and it declined
  ## the whole expression (`feUnsupportedExprKind`, forcing `sxUnknown`).
  ##
  ## Unlike a narrowing of a VARIABLE (truly unmodeled -- a real width's
  ## worth of bits could be lost at runtime, hence 678c6ce's decline), a
  ## narrowing of a LITERAL is always representation-safe: Nim only accepts
  ## the program at all because it already verified the literal's value
  ## fits the resolved narrower width (otherwise it's a compile error) --
  ## there is no bit to lose. `parseExpr`'s own literal arm
  ## (`mkIntLit(n.intVal)`) never tags a width at all; downstream folding
  ## sizes the literal into whatever BV width the OTHER operand carries.
  ## That is exactly the pre-678c6ce behavior for this shape, and is
  ## unaffected by (and orthogonal to) the WIDENING case 678c6ce targeted
  ## (there the wrapped node is the narrow VARIABLE, never a literal).
  ##
  ## Confirmed via `tests/tdebug_probe.nim` (scratch, not committed): before
  ## this carve-out, `x: int32; if x * 2 == 50'i32: ...` declined with "B2:
  ## hidden narrowing int conversion `int` -> `int32` ... in `2`", forcing
  ## the whole run to `sxUnknown` — the same signature across all 15
  ## suites in the #163 gate regression (any arithmetic/comparison pairing
  ## a plain integer literal against an operand narrower than `int`).
  n.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit,
             nnkUIntLit, nnkUInt8Lit, nnkUInt16Lit, nnkUInt32Lit,
             nnkUInt64Lit}

proc intConvSrcName(operand: NimNode, src: string): string =
  ## RFC-0005 S8j. The int-family spelling an int conversion's operand is
  ## converted FROM. A subrange operand (`int8(x)` with `x: range[0..1000]`)
  ## spells as the range, not its base, so the conversion arm never read it
  ## as an int and the identity pass-through dropped the conversion: 1000
  ## flowed on as the `int8`, neither checked nor truncated. The range's
  ## representation is its base type's (the bounds are bookkeeping), so the
  ## base's width and signedness are the source's. Every other spelling is
  ## returned unchanged.
  if isIntFamilyName(src) or isIntLiteralNode(operand) or
     operand.typeKind != ntyRange:
    return src
  let cls = classifyType(operand)
  if cls.ty.kind != itInt: return src
  (if cls.ty.signed: "int" else: "uint") & $cls.ty.width

proc armYieldsValue(body: NimNode): bool =
  ## RFC-0005 s1. Does this branch arm produce a VALUE, or does it leave the
  ## path? A `case`/`if` in expression position may still carry arms that
  ## `raise`/`return` rather than yielding — `else: raise ...` is the entire
  ## point of the `parseModeLike` shape B7-2 was filed against. Such an arm is
  ## parsed as a plain STATEMENT (no assignment to the temp): the raise
  ## terminates the path, so the temp is never read on it.
  ##
  ## Structural kinds are tested FIRST and `typeKind` consulted only as a
  ## fallback — A5's lesson: a monomorphised node can be genuinely typeless,
  ## and `getTypeInst` on one is a hard, non-catchable compile error.
  if body.isNil: return false
  case body.kind
  of nnkRaiseStmt, nnkReturnStmt, nnkBreakStmt, nnkContinueStmt:
    return false
  of nnkStmtList, nnkStmtListExpr:
    if body.len == 0: return false
    return armYieldsValue(body[^1])
  else: discard
  body.typeKind notin {ntyNone, ntyVoid}

proc hoistCaseExpr(n: NimNode, preamble: var seq[IRStmt],
                        ctx: ParseCtx): IRExpr =
  ## RFC-0005 s1 — A-normalise a `case`/`if` in EXPRESSION position.
  ##
  ## `parseStmt` models both constructs fully (the `nnkCaseStmt` arm lowers to
  ## an if-elif chain; `nnkIfStmt`/`nnkIfExpr` has its own arm). Only the
  ## expression form was missing, so a proc whose implicit `result` is a
  ## `case` — `proc f(s: string): int = case s; of "a": 1; else: raise …` —
  ## fell to `parseExpr`'s catch-all and declined `feUnsupportedExprKind`.
  ##
  ## That decline is what RFC-0001 recorded as BLOCKER B7-2 "case/else-raise
  ## sibling poisoning" and escalated as needing a branch-scoped-degrade
  ## ARCHITECTURE. It needed no such thing: the declining proc is a CALLEE,
  ## parsed whole-proc at registration time, BEFORE any path exists — so the
  ## decline has no path to scope to and necessarily taints the whole query,
  ## including branches that never call it. Make it parse and there is
  ## nothing left to scope.
  ##
  ## Shape (the `nnkStmtListExpr` arm's own A-normalisation channel, which
  ## every other expression-position side-effect in this file already uses):
  ##   `<temp> := zero; <branching STATEMENT assigning temp>; <temp>`
  ##
  ## Scope notes, deliberate:
  ##   * ADR-0029 `caseNarrow` tag mining is NOT mirrored here. Omitting it is
  ##     SOUND — the variant constructor's fallback to the full declared arm
  ##     count is always sound, just less precise (see the `nnkCaseStmt`
  ##     statement arm's own comment) — and mirroring it would duplicate the
  ##     label-mining logic. A later slice can lift it into a shared helper.
  ##   * Elif-condition preambles are surfaced to the OUTER preamble, exactly
  ##     as the `nnkIfStmt` statement arm does. That is the known CR-1b
  ##     deposit shape (issue #157) and is PRE-EXISTING and shared: the same
  ##     source in statement position behaves identically. Diverging here
  ##     would make the two positions disagree, which is worse than the
  ##     shared limitation.
  let resultTy = classifyType(n).ty
  let tmp = freshSynth(ctx, "caseexpr")

  proc armBodyStmt(bodyNode: NimNode): IRStmt =
    ## Bind the temp with `mkLet` INSIDE the arm, exactly as M5 does — each
    ## branch runs only on its OWN forked path (`runtime.nim`'s `isIf` forks
    ## `paths` per-arm before running the body), so rebinding one name across
    ## sibling arms cannot collide, and no zero-initialisation is needed.
    ##
    ## An arm's own preamble stays INSIDE its branch: hoisting it would run
    ## one arm's side effects unconditionally, which is the CR-1b deposit
    ## hazard (#157) this file already pays for at guard sites.
    ##
    ## An arm that does NOT yield a value (`else: raise …` — the entire point
    ## of the shape B7-2 was filed against) is parsed as a plain statement and
    ## binds nothing: the raise terminates the path, so the temp is never read
    ## on it.
    if not armYieldsValue(bodyNode):
      return parseStmt(bodyNode, ctx)
    var bodyPre: seq[IRStmt]
    let bodyIR = parseExpr(bodyNode, bodyPre, ctx)
    bodyPre.add mkLet(tmp, resultTy, bodyIR)
    (if bodyPre.len == 1: bodyPre[0] else: mkBlock(bodyPre))

  # The scrutinee is evaluated unconditionally, so its preamble belongs in the
  # OUTER preamble — before the lowered if-chain.
  let scrutinee = parseExpr(n[0], preamble, ctx)
  var branches: seq[IRBranch]
  var elseBody: IRStmt = nil
  for i in 1 ..< n.len:
    let arm = n[i]
    case arm.kind
    of nnkOfBranch:
      var cond: IRExpr = nil
      for j in 0 ..< arm.len - 1:
        let labelIR = parseExpr(arm[j], preamble, ctx)
        let eq = mkBinop(bEq, scrutinee, labelIR)
        cond = if cond == nil: eq else: mkBinop(bOr, cond, eq)
      branches.add mkBranch(cond, armBodyStmt(arm[arm.len - 1]))
    of nnkElse, nnkElseExpr:
      elseBody = armBodyStmt(arm[0])
    else:
      error(&"RFC-0005 s1: unexpected case-arm kind {arm.kind}", arm)

  if elseBody == nil:
    # An `else`-less case-EXPRESSION is exhaustive by Nim's own rules (an
    # enum/ordinal scrutinee covering every value), so the fall-through is
    # semantically unreachable. It is NOT unreachable in the IR, though: a
    # nil else leaves `tmp` unbound on that edge, and the walker would meet a
    # bare `mkVar` with no env binding — the A0 KeyError class. Bind a zero
    # there so the edge is total. Sound precisely because Nim guarantees it
    # is never taken.
    let zero = if n.typeKind != ntyNone: zeroValueForType(resultTy) else: nil
    if zero == nil:
      # DoD clause (d): never call through on a typeless node.
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        siteMsg(n, "RFC-0005 s1: else-less case-expression whose type " &
                          "has no zero encoding — cannot make the (unreachable) " &
                          "fall-through edge total (feUnsupportedExprKind)"),
        "RFC-0005 s1: else-less case-expression, " &
                                   "no zero-encodable type (feUnsupportedExprKind)")
      return mkIntLit(0)
    elseBody = mkLet(tmp, resultTy, zero)

  preamble.add mkIf(branches, elseBody)
  mkVar(tmp)

proc lvalueRoot(lv: NimNode; heapSteps: var seq[NimNode]): NimNode =
  ## RFC-0005 S8ac. The variable an lvalue chain (`o.a`, `h.cur`, `s[i]`,
  ## `p[]`, `h.inner.n`) is rooted at, nil when it is rooted at anything
  ## else (a call result, a literal). `heapSteps` collects the node of every
  ## ref/ptr dereference on the way (the object or cell type the write lands
  ## in is that node's type); a `var` formal's own indirection is not one.
  var t = lv
  while true:
    # RFC-0005 S8bd: a by-reference base marked from an element or a call
    # result (`markByRef`) is a root, as a marked symbol is.
    if t.kind != nnkSym and t.len == 0 and byRefName(t).len > 0: return t
    case t.kind
    of nnkSym: return t
    of nnkDotExpr, nnkBracketExpr, nnkCheckedFieldExpr, nnkHiddenAddr:
      if t.len == 0: return nil
      t = t[0]
    of nnkDerefExpr, nnkHiddenDeref:
      if t.len == 0: return nil
      if not isVarIndirection(t): heapSteps.add t
      t = t[0]
    of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv:
      if t.len == 0: return nil
      t = t[^1]
    else: return nil

proc byRefRoot(lv: NimNode; heapSteps: var seq[NimNode]): NimNode =
  ## RFC-0005 S8bd. `lvalueRoot`, except that a lvalue reached through a
  ## ref a call returns (`getBox().x`) is rooted at that call: passed by
  ## reference, the call is evaluated once, before the callee runs, and the
  ## cell is the one its ref addresses. (A write-back would evaluate the
  ## call a second time, so `lvalueRoot` has no root for it.)
  result = lvalueRoot(lv, heapSteps)
  if result != nil: return
  heapSteps.setLen 0
  var t = lv
  while true:
    case t.kind
    of nnkDotExpr, nnkCheckedFieldExpr, nnkHiddenAddr:
      if t.len == 0: return nil
      t = t[0]
    of nnkDerefExpr, nnkHiddenDeref:
      if t.len == 0 or isVarIndirection(t): return nil
      heapSteps.add t
      t = t[0]
      if t.kind in {nnkCall, nnkCommand} and t.len > 0 and
         t[0].kind == nnkSym and isUserCallee(t[0]):
        return t
    of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv:
      if t.len == 0: return nil
      t = t[^1]
    else: return nil

proc lvalueCastBlocks(lv: NimNode): bool =
  ## RFC-0005 S8bg. True when `lvalueRoot`'s chain (a dot/bracket/deref walk
  ## through representation-preserving conversions) is blocked by a `cast`:
  ## the lvalue reaches its heap location through a `cast` that
  ## reinterprets memory, a shape `lvalueRoot`/`byRefRoot` do not peel (they
  ## return nil instead, the same as for any other shape they do not know,
  ## which left a cast-reached `var`/`addr` actual to fall into generic
  ## read machinery not expecting its dummy decline value -- a crash, not a
  ## decline). Scanning this chain first, before that machinery runs, lets
  ## the cast get its own named decline instead.
  var t = lv
  while true:
    if t.kind != nnkSym and t.len == 0 and byRefName(t).len > 0: return false
    case t.kind
    of nnkSym: return false
    of nnkDotExpr, nnkBracketExpr, nnkCheckedFieldExpr, nnkHiddenAddr:
      if t.len == 0: return false
      t = t[0]
    of nnkDerefExpr, nnkHiddenDeref:
      if t.len == 0: return false
      t = t[0]
    of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv:
      if t.len == 0: return false
      t = t[^1]
    of nnkCast:
      return true
    else: return false

proc mentionsSym(n, sym: NimNode): bool =
  ## RFC-0005 S8ac. True when `sym` (by symbol identity) occurs in `n`.
  if n.kind == nnkSym: return containsSym(@[sym], n)
  for c in n:
    if mentionsSym(c, sym): return true
  false

proc formalInBody(impl, f: NimNode): NimNode =
  ## RFC-0005 S8bd. The symbol the body of `impl` uses for its formal `f`.
  ## It is `f` itself, except in a generic instance, whose formal list
  ## keeps the generic's symbols while its body uses the instance's: there
  ## it is the body's one parameter symbol of `f`'s name (a lambda's own
  ## parameters, inside the body, are not searched). nil when more than
  ## one symbol of that name is found. (S8an's `ptrFormalStaysLocal` read
  ## a generic callee's body with the formal list's symbol, found no use of
  ## it, and took an escaping pointer for a local one: a false `sxSat`.)
  if f.isNil or mentionsSym(impl[6], f): return f
  var found: NimNode = nil
  var ambiguous = false
  proc scan(n: NimNode) =
    if n.kind == nnkSym:
      if symKind(n) == nskParam and macros.strVal(n) == macros.strVal(f):
        if found.isNil: found = n
        elif not containsSym(@[found], n): ambiguous = true
      return
    if n.kind in RoutineNodes: return
    for c in n: scan(c)
  scan(impl[6])
  if ambiguous: return nil
  if found.isNil: f else: found

proc objectInherits(t: NimNode): bool =
  ## RFC-0005 S8ac. True when object type `t` takes part in inheritance (it
  ## derives from something, or is `{.inheritable.}` / `RootObj`), so a
  ## `ref` of another object type may address it.
  let impl = t.getTypeImpl
  if impl.kind == nnkObjectTy and impl.len >= 2 and
     impl[1].kind == nnkOfInherit:
    return true
  let ts = t.getTypeInst
  if ts.kind == nnkSym and ts.strVal == "RootObj": return true
  let d = if ts.kind == nnkSym: ts.getImpl else: newEmptyNode()
  if d.kind == nnkTypeDef and d.len >= 1 and d[0].kind == nnkPragmaExpr:
    for pr in d[0][1]:
      if pr.kind in {nnkIdent, nnkSym} and pr.strVal == "inheritable":
        return true
  false

proc reprBase(t: NimNode): NimNode =
  ## RFC-0005 S8bg. `t` peeled through every `distinct` and `range` wrapper
  ## to its representation base: a `range` keeps its base's bit layout (the
  ## range check is compile-time only), and so does a `distinct`'s base,
  ## recursively (a `distinct` of a `distinct`).
  var impl = t.getTypeImpl
  while true:
    case impl.kind
    of nnkDistinctTy:
      if impl.len == 0: return impl
      impl = impl[0].getTypeImpl
    of nnkBracketExpr:
      # `range[lo..hi]`'s `getTypeImpl` is `BracketExpr(range, Infix(.., lo,
      # hi))` (two children, the bound expression itself one more): its
      # representation base is its bound literals' own type.
      if impl.len == 2 and impl[0].kind in {nnkSym, nnkIdent} and
         macros.strVal(impl[0]) == "range" and impl[1].kind == nnkInfix and
         impl[1].len == 3:
        impl = impl[1][1].getTypeImpl
      else:
        return impl
    else:
      return impl

proc convReprPreserving(operand, conv: NimNode): bool =
  ## RFC-0005 S8bg. True when a conversion from `operand`'s type to `conv`'s
  ## (an `nnkConv`/`nnkHiddenStdConv`/`nnkHiddenSubConv`) keeps the same
  ## representation: a `distinct` unwrap or rewrap, or a `range` to its
  ## base (or back). False for a conversion that changes the bit layout
  ## (`int` to `float`, a different-width integer): byRefSub leaves those
  ## declined, as before.
  ##
  ## A `ref`/`ptr` object inheritance up/downcast is the same address too
  ## (`objectInherits`, as `typeReachesCell` treats it for aliasing), but
  ## is deliberately NOT included here: the heap model gives every
  ## declared ref/ptr type its own Z3 sort, inheritance notwithstanding, so
  ## substituting the operand for the conversion (as this does for a
  ## distinct or a range) leaves the by-reference formal one sort and the
  ## direct access through the alias (`gAnimal`, `Animal`-sorted) another
  ## -- a sort mismatch at walk time (`weInternalWalkerFault`), not a
  ## soundness bug (the path is tainted, not wrongly decided) but not a
  ## working case either. Left declining, as before S8bg (RFC's "different
  ## mechanisms" list, PRECISION).
  let fromTy = operand.getTypeInst
  let toTy = conv.getTypeInst
  if sameType(fromTy, toTy): return true
  sameType(reprBase(fromTy), reprBase(toTy))

proc typeReachesCell(t: NimNode; cells: seq[NimNode];
                     seen: var seq[string]): bool =
  ## RFC-0005 S8ac. True when a value of type `t` can hold a `ref`/`ptr`
  ## that addresses a value of one of the `cells` types (the object types a
  ## heap lvalue lives in): a ref/ptr whose pointee is one of them, or
  ## either side takes part in inheritance, or an untyped `pointer`,
  ## searched through object/tuple fields, seq/array elements, distinct
  ## bases and pointees. Conservative: an unrecognised type shape is
  ## reported as reaching.
  if t.isNil: return true
  var impl = t.getTypeImpl
  if impl.kind == nnkVarTy and impl.len == 1: impl = impl[0].getTypeImpl
  let key = t.repr & "|" & impl.repr
  if key in seen: return false
  seen.add key
  case impl.kind
  of nnkSym:
    # Builtin scalars, strings, `pointer`.
    impl.strVal == "pointer"
  of nnkRefTy, nnkPtrTy:
    let pointee = impl[0]
    for c in cells:
      if sameType(pointee, c) or objectInherits(pointee) or
         objectInherits(c):
        return true
    typeReachesCell(pointee, cells, seen)
  of nnkObjectTy:
    if impl.len < 3 or impl[2].kind == nnkEmpty: return false
    for f in impl[2]:
      if f.kind == nnkIdentDefs:
        if typeReachesCell(f[^2], cells, seen): return true
      else:
        return true   # a record case: not searched, assume it reaches
    false
  of nnkTupleTy, nnkTupleConstr:
    for f in impl:
      let ft = if f.kind == nnkIdentDefs: f[^2] else: f
      if typeReachesCell(ft, cells, seen): return true
    false
  of nnkBracketExpr:
    # seq[T], array[I, T], set[T], Table[...]: any type argument.
    for i in 1 ..< impl.len:
      if typeReachesCell(impl[i], cells, seen): return true
    false
  of nnkDistinctTy:
    typeReachesCell(impl[0], cells, seen)
  of nnkEnumTy, nnkRange, nnkInfix:
    false
  else:
    true

proc lvalueVarSyms(lv: NimNode; into: var seq[NimNode]) =
  ## RFC-0005 S8an. Every variable an lvalue names: its root and the
  ## variables in its index expressions (`s[i]` names `s` and `i`). The
  ## write-back re-evaluates the lvalue after the call, so a callee that can
  ## change ANY of them makes it a different location from the one Nim
  ## passed.
  if lv.kind == nnkSym:
    if symKind(lv) in {nskVar, nskLet, nskParam, nskForVar, nskTemp} and
       not containsSym(into, lv):
      into.add lv
    return
  for c in lv: lvalueVarSyms(c, into)


proc lvaluePath(lv: NimNode; steps: var seq[string]): NimNode =
  ## RFC-0005 S8as. The root variable of an lvalue that is a plain PATH into
  ## it -- object or tuple fields (`o.a.b`) and constant indices (`a[2]`) --
  ## with the steps from the root outward; nil for anything else (a
  ## dereference, a computed index, a variant arm's field, a conversion).
  var t = lv
  var rev: seq[string]
  while true:
    case t.kind
    of nnkSym:
      for k in countdown(rev.high, 0): steps.add rev[k]
      return t
    of nnkDotExpr:
      if t.len != 2 or t[1].kind != nnkSym: return nil
      rev.add "." & macros.strVal(t[1])
      t = t[0]
    of nnkBracketExpr:
      if t.len != 2: return nil
      var ix = t[1]
      while ix.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and ix.len > 0:
        ix = ix[^1]
      if ix.kind notin {nnkCharLit .. nnkUInt64Lit}: return nil
      rev.add "[" & $ix.intVal & "]"
      t = t[0]
    else: return nil

type
  AliasIndexPairs = seq[tuple[a, b: NimNode]]
    ## RFC-0005 S8ax. Index pairs whose values all being equal makes two
    ## lvalues one location (`aliasPath`).
  PathStep = tuple[field: string; ix: NimNode]

proc stableIndex(ix: NimNode; rest: openArray[NimNode]): bool  ## RFC-0005 S8ax fwd decl

proc aliasSteps(lv: NimNode; steps: var seq[PathStep]): NimNode =
  ## RFC-0005 S8ax. `lvaluePath` with a variant arm's field (Nim's
  ## `nnkCheckedFieldExpr`) as a field step and a computed index of a value
  ## array or the variable's seq that is free of side effects
  ## (`stableIndex`) as an index step (`ix`; `field` is "" there). nil for
  ## any other shape.
  var t = lv
  var rev: seq[PathStep]
  while true:
    case t.kind
    of nnkSym:
      for k in countdown(rev.high, 0): steps.add rev[k]
      return t
    of nnkCheckedFieldExpr:
      if t.len < 1 or t[0].kind != nnkDotExpr: return nil
      t = t[0]
    of nnkDotExpr:
      if t.len != 2 or t[1].kind != nnkSym: return nil
      rev.add (field: "." & macros.strVal(t[1]), ix: nil)
      t = t[0]
    of nnkBracketExpr:
      if t.len != 2: return nil
      var ix = t[1]
      while ix.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and ix.len > 0:
        ix = ix[^1]
      if ix.kind in {nnkCharLit .. nnkUInt64Lit}:
        rev.add (field: "[" & $ix.intVal & "]", ix: nil)
      elif t[0].typeKind in {ntyArray, ntySequence} and
           stableIndex(t[1], []):
        rev.add (field: "", ix: t[1])
      else: return nil
      t = t[0]
    else: return nil

proc aliasPath(a, b: NimNode; pairs: var AliasIndexPairs): bool =
  ## RFC-0005 S8ax. `a` and `b` are paths into one variable (`aliasSteps`)
  ## that are one location only when every index pair added to `pairs` is
  ## equal: they part at a field step or two different constant indices
  ## (no pair, always two locations), or they part only where a computed
  ## index stands (the walk checks the pairs, `aliasGuardStmt`). False
  ## when neither applies -- a different root, a non-path, or one path a
  ## prefix of the other with no computed index (a whole and its part).
  ## Two fields of different variant arms count as two locations: Nim
  ## checks the arm when it takes each one's address, so they are never
  ## both live.
  var sa, sb: seq[PathStep]
  let ra = aliasSteps(a, sa)
  let rb = aliasSteps(b, sb)
  if ra.isNil or rb.isNil or not containsSym(@[ra], rb): return false
  var found: AliasIndexPairs
  for k in 0 ..< min(sa.len, sb.len):
    # Indexed in place: a VM `let` of an element aliases it (S8ab).
    if sa[k].ix == nil and sb[k].ix == nil:
      if sa[k].field != sb[k].field: return true
    elif sa[k].ix != nil and sb[k].ix != nil:
      found.add (a: sa[k].ix, b: sb[k].ix)
    else:
      return false   # a constant against a computed index: not paired
  if found.len == 0: return false
  pairs.add found
  true

proc lvaluesDisjoint(a, b: NimNode): bool =
  ## RFC-0005 S8as. `a` and `b` are paths into one variable
  ## (`lvaluePath`) that part at some step -- two different fields, or two
  ## different constant indices -- so they are two locations no write to
  ## one can reach the other through. Neither is a prefix of the other (a
  ## whole and its part overlap).
  ## RFC-0005 S8ax: a variant arm's field is a path too (`aliasPath`).
  var pairs: AliasIndexPairs
  aliasPath(a, b, pairs) and pairs.len == 0
proc heapCellTail(lv: NimNode): tuple[deref: NimNode, path: seq[string]] =
  ## RFC-0005 S8bf. The last ref/ptr dereference an lvalue reaches its cell
  ## through (`p.inner.x` is the `inner` deref), and the path from that
  ## dereference's object to the cell: field names, and `[]` for an index
  ## (any index, a tuple's included). `deref` is nil when the lvalue is not
  ## in a heap cell (a variable, a field or element of one, a marked
  ## by-reference parameter's own slot) or has a shape this does not read.
  var t = lv
  var rev: seq[string]
  while true:
    if t.kind != nnkSym and t.len == 0 and byRefName(t).len > 0: return
    case t.kind
    of nnkDotExpr:
      if t.len != 2: return
      rev.add(if t[1].kind in {nnkSym, nnkIdent}: macros.strVal(t[1])
              else: "[]")
      t = t[0]
    of nnkBracketExpr:
      if t.len == 0: return
      rev.add "[]"
      t = t[0]
    of nnkCheckedFieldExpr, nnkHiddenAddr:
      if t.len == 0: return
      t = t[0]
    of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv:
      if t.len == 0: return
      t = t[^1]
    of nnkDerefExpr, nnkHiddenDeref:
      if t.len == 0: return
      if isVarIndirection(t):
        t = t[0]
        continue
      for k in countdown(rev.high, 0): result.path.add rev[k]
      result.deref = t
      return
    else: return

proc derefIsPtr(d: NimNode): bool =
  ## RFC-0005 S8bf. `d` (a heap dereference) is through a `ptr`/`pointer`,
  ## not a `ref`.
  var o = d[0]
  while o.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and
        o.len > 0:
    o = o[^1]
  let k = o.getTypeImpl.kind
  k == nnkPtrTy or (k == nnkSym and o.getTypeImpl.strVal == "pointer")

proc heapCellsMayMeet(a, b: NimNode): bool =
  ## RFC-0005 S8bf. True when the heap lvalues `a` and `b` may denote one
  ## cell (or overlapping ones) whatever their roots: the caller cannot
  ## tell two refs apart by the variables that hold them (`let q = p`, a
  ## tuple or an object field holding `p`, two parameters), so ROOT
  ## identity says nothing. They may meet when the objects their last
  ## dereferences address may be one object (the same type, or either
  ## takes part in inheritance) and one path from that object is a prefix
  ## of the other (`p.x` and `q.x`; `p.v` and `q.v.n`; an index matches
  ## any index). A `ptr` may address a value embedded anywhere, so a `ptr`
  ## dereference on either side meets any heap lvalue. Conservative: an
  ## lvalue shape `heapCellTail` does not read is not a heap lvalue here,
  ## and is left to the root and type checks of `varActualMayAlias`.
  let ta = heapCellTail(a)
  let tb = heapCellTail(b)
  if ta.deref.isNil or tb.deref.isNil: return false
  if derefIsPtr(ta.deref) or derefIsPtr(tb.deref): return true
  let ca = ta.deref.getTypeInst
  let cb = tb.deref.getTypeInst
  if not (sameType(ca, cb) or objectInherits(ca) or objectInherits(cb)):
    return false
  for k in 0 ..< min(ta.path.len, tb.path.len):
    if ta.path[k] != tb.path[k] and ta.path[k] != "[]" and
       tb.path[k] != "[]":
      return false
  true

proc actualCell(a: NimNode): NimNode =
  ## RFC-0005 S8bf. The location an actual hands its callee: the lvalue of
  ## a `var` actual (`nnkHiddenAddr`, the formal's own indirection
  ## dropped) or of an `addr lv` one; for a value Nim may pass by pointer
  ## (anything but a scalar, `isInertArg`; a string is passed by pointer),
  ## the value's own expression. nil for a scalar value.
  var t = a
  while t.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and t.len > 0 and
        t.typeKind != ntyVarargs:
    t = t[^1]
  if t.kind in {nnkHiddenAddr, nnkAddr} and t.len == 1:
    var lv = t[0]
    if isVarIndirection(lv): lv = lv[0]
    return lv
  if isInertArg(a) and a.typeKind != ntyString: return nil
  t

proc varActualMayAlias(n: NimNode; i: int; lv, root: NimNode;
                       heapSteps: seq[NimNode];
                       conds: var seq[AliasIndexPairs];
                       skip: seq[int] = @[]; cellsBound = false;
                       byRef = false): bool =
  ## RFC-0005 S8ac. The write-back of a non-variable `var` actual
  ## (`userCallStmt`) copies the lvalue in, walks the callee on the copy and
  ## copies it out. Nim passes the lvalue's ADDRESS, so the two agree unless
  ## the callee can reach the same location another way while it runs:
  ## through another argument that names the same root variable (by
  ## address, or by a non-scalar value Nim may pass by pointer), or, for a
  ## heap lvalue, through another argument whose type can hold a ref to the
  ## cell. Then copy-in/copy-out is not Nim's semantics, and the call
  ## declines.
  ## RFC-0005 S8an: every variable the lvalue names counts, not only its
  ## root: `setIJ(s[i], i)` writes `s[old i]` in Nim, and the write-back
  ## after the call wrote `s[new i]`. And a plain-variable actual is
  ## checked too: `setIJ(i, i)` is one location written twice in the
  ## callee's order, which two by-name write-backs do not reproduce.
  ## RFC-0005 S8bf: and another argument whose location may be the same
  ## heap cell through a DIFFERENT ref (`heapCellsMayMeet`): `let q = p;
  ## setBoth(p.x, q.x)` names two roots, and `q.x`'s type (`var int`) holds
  ## no ref, so neither check above saw it, and the two write-backs ran in
  ## argument order (a false `sxSat`). `skip` holds the arguments passed by
  ## reference with this one (`userCallStmt`), which are one cell in the
  ## walk too.
  ##
  ## RFC-0005 S8bs: `cellsBound` (a direct call, `userCallStmt`): an `addr
  ## x` actual of the variable the lvalue is a path into is `x`'s address
  ## cell, and the walker binds the `var` formal to that cell at the path
  ## (`bindVarLocs`, `inheritAddrCells`), so the two are one location in the
  ## walk. `byRef`: the lvalue is passed by reference (`byRefSub`), so only
  ## another `var` or `addr` actual can be a second location for it; one
  ## passed by value (a `ptr` to the cell, `setXP(pb[].x, pb)`) reads and
  ## writes the same heap.
  var cells: seq[NimNode]
  for d in heapSteps: cells.add d.getTypeInst
  var syms: seq[NimNode]
  lvalueVarSyms(lv, syms)
  if not containsSym(syms, root): syms.add root
  for j in 1 ..< n.len:
    if j == i or j in skip: continue
    let a = n[j]
    if cellsBound and heapSteps.len == 0 and root != nil and
       root.kind == nnkSym:
      let x = addrCellLocal(a)
      if x != nil and containsSym(@[x], root): continue
    if byRef and a.kind != nnkHiddenAddr and addrActualLvalue(a) == nil:
      continue
    # RFC-0005 S8bf: the same heap cell through a different ref.
    let oc = actualCell(a)
    if oc != nil and heapCellsMayMeet(lv, oc): return true
    # A scalar passed by value cannot alias. A string can: Nim passes a
    # non-`var` string by pointer, so it is checked like any composite.
    if isInertArg(a) and a.typeKind != ntyString: continue
    # RFC-0005 S8as: another `var` or `addr` actual on a disjoint path of
    # the same variable (`o.a` and `o.b`, `a[0]` and `a[2]`) is another
    # location.
    let olv = if a.kind == nnkHiddenAddr and a.len == 1: a[0]
              else: addrActualLvalue(a)
    # RFC-0005 S8ax: or one only when computed indices are equal, which
    # the walk checks (`conds`, `aliasGuardStmt`).
    if olv != nil:
      var pairs: AliasIndexPairs
      if aliasPath(lv, olv, pairs):
        if pairs.len > 0: conds.add pairs
        continue
    for s in syms:
      if mentionsSym(a, s): return true
    if cells.len > 0:
      var seen: seq[string]
      if typeReachesCell(a.getTypeInst, cells, seen): return true
  false

# ---- RFC-0005 S8an: `addr x` passed as a `ptr T` ----------------------------

proc addrActualLvalue(a: NimNode): NimNode =
  ## RFC-0005 S8an. The lvalue `lv` of an actual spelled `addr lv` (or
  ## `unsafeAddr lv`, which lowers to the same `nnkAddr`), nil otherwise.
  var t = a
  while t.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and t.len > 0:
    t = t[^1]
  if t.kind == nnkAddr and t.len == 1: t[0] else: nil

proc addrCellLocal(e: NimNode): NimNode =
  ## RFC-0005 S8ax. The variable `x` of `e` spelled `addr x` (through
  ## conversions, and through a `var` formal's hidden indirection) when `x`
  ## is a variable, parameter or `result` of a routine; nil otherwise (a
  ## field, an element, a dereference, a module-level variable). Such an
  ## `x` has an address cell in the walk (`mkNewT`'s `addrOf`): the
  ## pointer is a value like any other -- stored, returned, compared,
  ## re-pointed -- and the walker keeps `x` and its cell equal.
  let lv = addrActualLvalue(e)
  if lv == nil: return nil
  var t = lv
  if isVarIndirection(t): t = t[0]
  if t.kind != nnkSym or
     symKind(t) notin {nskVar, nskLet, nskParam, nskResult, nskForVar} or
     isModuleGlobal(t):
    return nil
  t

proc elemCellOf(e: NimNode): tuple[root, idx: NimNode] =
  ## RFC-0005 S8be. `e` spelled `addr s[i]` (through conversions, and
  ## through a `var` formal's hidden indirection) where `s` is a variable,
  ## parameter or `result` of a routine of type `seq[T]`, `T` an `int`,
  ## `bool`, `float` or `string`; `(nil, nil)` otherwise. Such an element
  ## has an element cell in the walk (`walkElemCell`): the pointer is a
  ## value like any other, and the walker keeps the element and the cell
  ## equal until the seq is resized.
  let lv = addrActualLvalue(e)
  if lv == nil or lv.kind != nnkBracketExpr or lv.len != 2: return
  var t = lv[0]
  if isVarIndirection(t): t = t[0]
  if t.kind != nnkSym or
     symKind(t) notin {nskVar, nskLet, nskParam, nskResult, nskForVar} or
     isModuleGlobal(t) or t.typeKind notin {ntySequence, ntyVar}:
    return
  let sty = classifyType(t).ty
  if sty.kind != itSeq or sty.seqElemTy == nil or
     sty.seqElemTy.kind notin {itInt, itBool, itFloat32, itFloat64, itString}:
    return
  (t, lv[1])

proc lowerElemCell(e, root, idx: NimNode; preamble: var seq[IRStmt];
                   ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8be. `addr s[i]` (`elemCellOf`): the index is evaluated and
  ## checked where `addr` takes it (an out-of-range index raises
  ## `IndexDefect` there), and the cell is identified by the seq and that
  ## value, whatever later happens to `i`.
  let name = strVal(root)
  let elemTy = classifyType(root).ty.seqElemTy
  let ix = freshSynth(ctx, "elemIx")
  preamble.add mkLet(ix, classifyType(idx).ty, parseExpr(idx, preamble, ctx))
  preamble.add mkIndexStmt(freshSynth(ctx, "elemChk"), mkVar(name), mkVar(ix),
                           elemTy, siteLoc(e))
  let cell = freshSynth(ctx, "elemCell")
  preamble.add mkNewT(cell, classifyType(e).ty, addrOf = name,
                      addrIdx = mkVar(ix))
  mkVar(cell)

proc lowerAddrCell(e, x: NimNode; preamble: var seq[IRStmt];
                   ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8ax. `addr x` (`addrCellLocal`): the address cell of `x`,
  ## allocated by its first `addr` in the frame and the same pointer after.
  let name = strVal(x)
  preamble.add mkNewT(addrCellName(name), classifyType(e).ty, addrOf = name)
  mkVar(addrCellName(name))

proc isSymOf(n, sym: NimNode): bool =
  ## RFC-0005 S8an. `n` is `sym` (by symbol identity), through conversions.
  var t = n
  while t.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and t.len > 0:
    t = t[^1]
  t.kind == nnkSym and containsSym(@[sym], t)

proc dropVarIndirection(n, f: NimNode): NimNode =
  ## RFC-0005 S8au. `n` with every `nnkHiddenDeref(f)` -- the typed AST's
  ## spelling of a use of the `var` formal `f` -- replaced by `f` itself.
  if n.kind == nnkHiddenDeref and n.len == 1 and isSymOf(n[0], f):
    return n[0]
  if n.len == 0: return n
  result = copyNimNode(n)
  for c in n: result.add dropVarIndirection(c, f)

proc ptrUsesStayLocal(n, f: NimNode; seen: var seq[string]): bool =
  ## RFC-0005 S8an. True when every use of the pointer `f` in `n` is one
  ## that cannot let it outlive the call: a dereference `f[]` (read, write,
  ## or passed on as a `var` actual) that is not itself under `addr`, a
  ## comparison (`==`, `!=`, `isNil`), or an argument to a `ptr` formal of a
  ## user routine that itself keeps its pointer local. Anything else (a
  ## store, a return, a capture, an argument to anything else) may escape.
  case n.kind
  of nnkSym:
    return not containsSym(@[f], n)
  of nnkDerefExpr, nnkHiddenDeref:
    if n.len == 1 and isSymOf(n[0], f): return true
  of nnkAddr:
    if n.len == 1 and n[0].kind in {nnkDerefExpr, nnkHiddenDeref} and
       n[0].len == 1 and isSymOf(n[0][0], f):
      return false
  of RoutineNodes:
    return not mentionsSym(n, f)
  of nnkInfix, nnkCall, nnkCommand, nnkPrefix, nnkHiddenCallConv:
    if n.len > 0 and n[0].kind == nnkSym:
      let head = n[0]
      let builtinCmp = macros.strVal(head) in ["==", "!=", "isNil"] and
                       not isUserCallee(head)
      let userCall = isUserCallee(head)
      if builtinCmp or userCall:
        for j in 1 ..< n.len:
          if isSymOf(n[j], f):
            if builtinCmp: continue
            if not ptrFormalStaysLocal(head, j - 1, seen): return false
          elif userCall and n[j].kind == nnkHiddenAddr and n[j].len == 1 and
               isSymOf(n[j][0], f):
            # RFC-0005 S8au: the pointer variable itself passed to a `var
            # ptr` formal. It stays local when that formal only ever
            # dereferences it (never rebinds or stores it).
            if not ptrFormalStaysLocal(head, j - 1, seen): return false
          elif not ptrUsesStayLocal(n[j], f, seen):
            return false
        return true
  else: discard
  for c in n:
    if not ptrUsesStayLocal(c, f, seen): return false
  true

proc ptrFormalStaysLocal(callee: NimNode; idx: int;
                         seen: var seq[string]): bool =
  ## RFC-0005 S8an. True when user routine `callee`'s `idx`-th formal is a
  ## `ptr` whose every use stays local (`ptrUsesStayLocal`). A routine
  ## already being checked is assumed to (the check is a greatest fixed
  ## point: recursion passes the pointer to itself, which escapes only if
  ## some other use does).
  if callee.kind != nnkSym: return false
  let key = macros.strVal(callee) & "@" & callee.lineInfo & "#" & $idx
  if key in seen: return true
  seen.add key
  let impl = resolveRoutineImpl(callee)
  if impl == nil or impl.len < 7: return false
  let formal = impl[3]
  if formal.kind != nnkFormalParams: return false
  var k = 0
  var fsym: NimNode = nil
  var isVarF = false
  for i in 1 ..< formal.len:
    let id = formal[i]
    if id.kind != nnkIdentDefs: return false
    for j in 0 ..< id.len - 2:
      if k == idx:
        fsym = id[j]
        if id[^2].kind == nnkVarTy:
          # RFC-0005 S8au: `p: var ptr T`.
          if id[^2].len != 1 or id[^2][0].getTypeImpl.kind != nnkPtrTy:
            return false
          isVarF = true
        elif id[j].getTypeImpl.kind != nnkPtrTy:
          return false
      inc k
  if fsym == nil or fsym.kind != nnkSym: return false
  # RFC-0005 S8bd: the body's own symbol for the formal (`formalInBody`).
  fsym = formalInBody(impl, fsym)
  if fsym == nil: return false
  if isVarF:
    # RFC-0005 S8au: a `var ptr` formal's every use is spelled
    # `nnkHiddenDeref(p)` (the caller's pointer variable). Read without
    # that indirection, the body uses `p` exactly as a `ptr` formal's
    # does, and the same rule applies: `p[]` stays local, a bare `p`
    # (a rebind `p = q`, a store, a return) does not. A `var ptr` formal
    # that only dereferences is a `ptr` formal; the `var` is never used.
    return ptrUsesStayLocal(dropVarIndirection(body(impl), fsym), fsym, seen)
  ptrUsesStayLocal(body(impl), fsym, seen)

proc addrActualMayAlias(n: NimNode; i: int; lv, root: NimNode;
                        heapSteps: seq[NimNode];
                        conds: var seq[AliasIndexPairs];
                        skip: seq[int] = @[]; cellsBound = false): bool =
  ## RFC-0005 S8an. `varActualMayAlias` for an `addr lv` actual: another
  ## `addr` of the SAME lvalue is the same cell (`userCallStmt` shares it),
  ## so it does not alias; any other argument that names the root, or can
  ## hold a ref to a heap cell on the lvalue's path, does.
  ## RFC-0005 S8bf: as does one whose location may be the same heap cell
  ## through a different ref (`heapCellsMayMeet`; `skip` as there).
  var cells: seq[NimNode]
  for d in heapSteps: cells.add d.getTypeInst
  var syms: seq[NimNode]
  lvalueVarSyms(lv, syms)
  if not containsSym(syms, root): syms.add root
  ## RFC-0005 S8bs: `cellsBound` (a direct call), when this actual is `x`'s
  ## address cell (`addrCellLocal`): a `var` actual that is `x` or a path
  ## into it is bound to that cell by the walker (`bindVarLocs`).
  let key = scopedRepr(lv)
  let cellX = if cellsBound: addrCellLocal(n[i]) else: nil
  for j in 1 ..< n.len:
    if j == i: continue
    let a = n[j]
    let olv = addrActualLvalue(a)
    if olv != nil and scopedRepr(olv) == key: continue
    if j in skip: continue
    if cellX != nil and a.kind == nnkHiddenAddr and a.len == 1:
      var hs: seq[NimNode]
      var vl = a[0]
      if isVarIndirection(vl): vl = vl[0]
      let r = lvalueRoot(vl, hs)
      if r != nil and r.kind == nnkSym and hs.len == 0 and
         containsSym(@[cellX], r):
        continue
    # RFC-0005 S8bf: the same heap cell through a different ref.
    let oc = actualCell(a)
    if oc != nil and heapCellsMayMeet(lv, oc): return true
    # RFC-0005 S8as: an `addr` (or `var`) of a disjoint path of the same
    # variable is another cell, and the alias check is by path: S8an
    # declined any second argument naming the root.
    let vlv = if a.kind == nnkHiddenAddr and a.len == 1: a[0] else: olv
    if vlv != nil:   # RFC-0005 S8ax: `conds`, as `varActualMayAlias`
      var pairs: AliasIndexPairs
      if aliasPath(lv, vlv, pairs):
        if pairs.len > 0: conds.add pairs
        continue
    if isInertArg(a) and a.typeKind != ntyString: continue
    for s in syms:
      if mentionsSym(a, s): return true
    if cells.len > 0:
      var seen: seq[string]
      if typeReachesCell(a.getTypeInst, cells, seen): return true
  false

proc calleeOuterSyms*(calleeSym: NimNode): seq[NimNode] =
  ## RFC-0005 S8au. The variables outside its own frame that a call of
  ## `calleeSym` can reach while it runs: every module-level global its
  ## body names, every enclosing variable it captures (a nested routine,
  ## `nestedCaptureSyms`), and, transitively, those of each user routine
  ## its body names (a call, or the routine passed on as a value). A
  ## lambda built inside the body is part of it, so its globals are found
  ## too. Symbol identity throughout.
  var work: seq[NimNode]
  var seenR: seq[NimNode]
  if calleeSym.kind == nnkSym: work.add calleeSym
  var acc: seq[NimNode]
  proc scan(n: NimNode; acc, work: var seq[NimNode]) =
    if n == nil: return
    if n.kind == nnkSym:
      if isModuleGlobal(n):
        if not containsSym(acc, n): acc.add n
      elif isUserRoutine(n):
        work.add n
      return
    for c in n: scan(c, acc, work)
  var i = 0
  while i < work.len:
    let r = work[i]
    inc i
    if containsSym(seenR, r): continue
    seenR.add r
    let impl = resolveRoutineImpl(r)
    if impl == nil or impl.len < 7: continue
    if isNestedRoutine(r):
      for s in nestedCaptureSyms(impl):
        if not containsSym(acc, s): acc.add s
    scan(body(impl), acc, work)
  acc

proc outerReachesCell(outer, heapSteps: seq[NimNode]): NimNode =
  ## RFC-0005 S8au. The first of `outer` (`calleeOuterSyms`) whose type can
  ## hold a ref to a cell on a heap lvalue's path (`typeReachesCell`), or
  ## nil. Copy-in/copy-out of `p.x` is Nim's pass-by-address only while
  ## the callee cannot reach `p.x` another way; a global or a capture of
  ## type `Box` (`gBox.x = 5`) reaches it as surely as another argument
  ## does (S8ac's `varActualMayAlias`), and the write-back after the call
  ## then lands over the callee's direct write.
  if heapSteps.len == 0: return nil
  var cells: seq[NimNode]
  for d in heapSteps: cells.add d.getTypeInst
  for g in outer:
    var seen: seq[string]
    if typeReachesCell(g.getTypeInst, cells, seen): return g
  nil

# ---- RFC-0005 S8bh: a call through a proc value -----------------------------

proc cellTypeKey(t: NimNode): string =
  ## RFC-0005 S8bh. A key for the object (or value) type a ref/ptr
  ## addresses, the same whether read from a pointer type's pointee or from
  ## a dereference: its implementation's spelling. Two types spelled alike
  ## share a key (a collision only makes more calls decline).
  if t.isNil: return "t:?"
  let im = if t.kind in {nnkObjectTy, nnkTupleTy}: t else: t.getTypeImpl
  "t:" & $hash(im.repr)

proc typeReachKeys(t: NimNode; into: var seq[string]; seen: var seq[string]) =
  ## RFC-0005 S8bh. `typeReachesCell`, enumerated: the `cellTypeKey` of
  ## every object type a ref held by a value of type `t` may address; `t:?`
  ## for any object type (a `ptr`, which may address a value embedded
  ## anywhere, `pointer`, or a ref into an inheritance hierarchy); `*` for
  ## an unknown reach (a proc value, whose own captures are not known, or a
  ## type shape not searched).
  template add(k: string) =
    if k notin into: into.add k
  if t.isNil:
    add "*"
    return
  var impl = t.getTypeImpl
  if impl.kind == nnkVarTy and impl.len == 1: impl = impl[0].getTypeImpl
  let key = t.repr & "|" & impl.repr
  if key in seen: return
  seen.add key
  case impl.kind
  of nnkSym:
    if impl.strVal == "pointer": add "t:?"
  of nnkPtrTy:
    add "t:?"
    typeReachKeys(impl[0], into, seen)
  of nnkRefTy:
    add cellTypeKey(impl[0])
    if objectInherits(impl[0]): add "t:?"
    typeReachKeys(impl[0], into, seen)
  of nnkObjectTy:
    if impl.len < 3 or impl[2].kind == nnkEmpty: return
    for f in impl[2]:
      if f.kind == nnkIdentDefs: typeReachKeys(f[^2], into, seen)
      else: add "*"
  of nnkTupleTy, nnkTupleConstr:
    for f in impl:
      typeReachKeys((if f.kind == nnkIdentDefs: f[^2] else: f), into, seen)
  of nnkBracketExpr:
    for i in 1 ..< impl.len: typeReachKeys(impl[i], into, seen)
  of nnkDistinctTy:
    typeReachKeys(impl[0], into, seen)
  of nnkEnumTy, nnkRange, nnkInfix:
    discard
  else:
    add "*"

proc substFormal(n, gone, keep: NimNode): NimNode =
  ## RFC-0005 S8bh. `n` with every use of the formal `gone` spelled as the
  ## formal `keep` (symbol identity; a lambda nested in `n` included, as it
  ## captures the formal).
  if n.kind == nnkSym and containsSym(@[gone], n): return keep
  if n.len == 0: return n
  result = copyNimNode(n)
  for c in n: result.add substFormal(c, gone, keep)

proc lambdaEffects(n: NimNode; ctx: ParseCtx; lam: IRExpr): IRExpr =
  ## RFC-0005 S8bh. `lam` (the `iekLambda` of routine `n`) with what a call
  ## through it needs to apply its `var`/`addr` effects as a direct call
  ## does (`closureCallIR`, `lowerClosureCall`):
  ##   * for each pair of same-typed `var` formals, the body with the second
  ##     spelled as the first: the callee as it runs when one location is
  ##     passed to both (`f(x, x)`, or `f(p.x, q.x)` with `p == q`), its
  ##     writes through the two landing on one location in its order;
  ##   * for each `ptr` formal, whether every use of it stays local to the
  ##     call (S8an's `ptrUsesStayLocal`), so an `addr` actual may be a cell;
  ##   * what the body can reach outside its formals: the variables it
  ##     names that it does not declare (captures, module-level globals,
  ##     and those of each routine it calls, transitively) and the object
  ##     types their refs may address (`typeReachKeys`); `*` when that is
  ##     not known (a proc-valued formal or capture it may call).
  let formal = n[3]
  var syms, tys: seq[NimNode]
  for i in 1 ..< formal.len:
    let id = formal[i]
    if id.kind != nnkIdentDefs: continue
    for j in 0 ..< id.len - 2:
      syms.add id[j]
      tys.add id[^2]
  let bodyNode = body(n)
  var pairs: seq[tuple[keep, gone: int]]
  var aliasBodies: seq[IRStmt]
  var varIx: seq[int]
  for k in 0 ..< syms.len:
    if tys[k].kind == nnkVarTy and tys[k].len == 1: varIx.add k
  # Four `var` formals make six specialisations; more are not made (a call
  # sharing a location among them declines).
  if varIx.len in 2 .. 4:
    for a in 0 ..< varIx.len:
      for b in a + 1 ..< varIx.len:
        let i = varIx[a]
        let j = varIx[b]
        if not sameType(tys[i][0], tys[j][0]): continue
        let keep = formalInBody(n, syms[i])
        let gone = formalInBody(n, syms[j])
        if keep.isNil or gone.isNil or keep.kind != nnkSym or
           gone.kind != nnkSym:
          continue
        pairs.add (keep: i, gone: j)
        aliasBodies.add parseStmt(substFormal(bodyNode, gone, keep), ctx)
  var ptrLocal: seq[bool]
  for k in 0 ..< syms.len:
    var pl = false
    if tys[k].kind != nnkVarTy and syms[k].kind == nnkSym and
       syms[k].getTypeImpl.kind == nnkPtrTy:
      let fb = formalInBody(n, syms[k])
      if fb != nil:
        var seen: seq[string]
        pl = ptrUsesStayLocal(bodyNode, fb, seen)
    ptrLocal.add pl
  var outer: seq[string]
  block reach:
    var decls, refs, nested: seq[NimNode]
    collectDeclaredSyms(n, decls)
    collectOuterRefs(bodyNode, refs, nested)
    var os: seq[NimNode]
    for s in refs:
      if not containsSym(decls, s) and not containsSym(os, s): os.add s
    var work = nested
    proc scan(m: NimNode; os, work: var seq[NimNode]) =
      if m == nil: return
      if m.kind == nnkSym:
        if isModuleGlobal(m):
          if not containsSym(os, m): os.add m
        elif isUserRoutine(m):
          work.add m
        return
      for c in m: scan(c, os, work)
    scan(bodyNode, os, work)
    for r in work:
      for s in calleeOuterSyms(r):
        if not containsSym(os, s): os.add s
    var seen: seq[string]
    for s in os:
      let nm = "n:" & s.strVal
      if nm notin outer: outer.add nm
      typeReachKeys(s.getTypeInst, outer, seen)
    for k in 0 ..< syms.len:
      if syms[k].kind == nnkSym and syms[k].getTypeImpl.kind == nnkProcTy:
        if "*" notin outer: outer.add "*"
  withLambdaEffects(lam, pairs, aliasBodies, ptrLocal, outer)

proc hierarchyConv(n, operand: NimNode): tuple[isHier: bool;
    tgtTy, tgtPointee: IRType; srcChain, tgtChain: seq[string]] =
  ## RFC-0005 S8bh (item 3). `n` (an `nnkConv`) converts a ref (or ptr) of
  ## one inheritance hierarchy to another type of the same hierarchy: both
  ## pointees carry an `inheritChain` with the same root, one chain a prefix
  ## of the other. Anything else (a value object, two unrelated types) is
  ## not this conversion.
  let t = classifyType(n).ty
  let o = classifyType(operand).ty
  if t == nil or o == nil or t.kind notin {itRef, itPtr} or o.kind != t.kind:
    return
  let tp = if t.kind == itRef: t.refPointeeTy else: t.ptrPointeeTy
  let op = if o.kind == itRef: o.refPointeeTy else: o.ptrPointeeTy
  if tp == nil or op == nil:
    return
  # RFC-0005 S8bn (item 8): a case object of a hierarchy too (`hierChain`).
  let tc = hierChain(tp)
  let sc = hierChain(op)
  if tc.len == 0 or sc.len == 0 or tc[0] != sc[0]: return
  let short = min(tc.len, sc.len)
  if tc[0 ..< short] != sc[0 ..< short]: return
  (true, t, tp, sc, tc)

proc byRefTypeKey(n: NimNode): string =
  ## RFC-0005 S8ba. A type's spelling, the module that declares it (two
  ## modules may each declare a `Box`) and the line and column of its
  ## definition. No file path: the key reaches the cache key, which must
  ## not depend on where the checkout lives.
  let ti = n.getTypeInst
  let li = ti.getTypeImpl.lineInfoObj
  var owner = ""
  if ti.kind == nnkSym:
    let o = ti.owner
    if o.kind == nnkSym: owner = macros.strVal(o)
  ti.repr & "@" & owner & ":" & $li.line & ":" & $li.column

proc byRefFormalSym(impl: NimNode; idx: int): tuple[f: NimNode, isPtr, ok: bool] =
  ## RFC-0005 S8ba. The `idx`-th formal of `impl`, and whether it is a
  ## `ptr T` (rather than a `var T`); `ok` is false for any other formal.
  if impl == nil or impl.len < 7 or impl[3].kind != nnkFormalParams: return
  var k = 0
  for i in 1 ..< impl[3].len:
    let id = impl[3][i]
    if id.kind != nnkIdentDefs: return
    for j in 0 ..< id.len - 2:
      if k == idx:
        if id[j].kind != nnkSym: return
        if id[^2].kind == nnkVarTy: return (id[j], false, true)
        if id[j].getTypeImpl.kind == nnkPtrTy: return (id[j], true, true)
        return
      inc k

proc substByRefBody(n, f: NimNode; b: ByRefSub): NimNode =
  ## RFC-0005 S8ba. `n` with every use of the formal `f` spelled as the
  ## caller's lvalue `b.tail`: `f[]` (a `ptr` formal's dereference, or the
  ## typed AST's `nnkHiddenDeref` of a `var` formal) is the lvalue, and a
  ## bare `ptr` formal (passed on, compared) is `addr` of it, as
  ## `substAddrAlias` spells a local alias.
  if n.kind in {nnkDerefExpr, nnkHiddenDeref} and n.len == 1 and
     isSymOf(n[0], f):
    return copyNimTree(b.tail)
  if b.isPtr:
    if n.kind == nnkHiddenAddr and n.len == 1 and isSymOf(n[0], f):
      return copyNimTree(b.addrNode)
    if isSymOf(n, f): return copyNimTree(b.addrNode)
  if n.len == 0: return n
  result = copyNimNode(n)
  let isCallLike = n.kind in {nnkCall, nnkCommand, nnkInfix, nnkPrefix,
                              nnkHiddenCallConv}
  for i, c in n:
    # A `var` formal passed on to another `var` formal is the bare symbol
    # in the typed AST (Nim drops the deref/addr pair): it is the caller's
    # lvalue passed by address, `nnkHiddenAddr(lvalue)`, the shape Nim
    # gives `g(p.x)` written directly.
    if not b.isPtr and isCallLike and i >= 1 and c.kind == nnkSym and
       containsSym(@[f], c):
      result.add copyNimTree(b.addrNode)
    else:
      result.add substByRefBody(c, f, b)

proc substByRefImpl(impl: NimNode; subs: seq[ByRefSub]): NimNode =
  ## RFC-0005 S8ba. `impl` with each by-reference formal's uses spelled as
  ## its lvalue (`substByRefBody`).
  result = copyNimTree(impl)
  var bd = impl[6]
  for b in subs:
    let fs = byRefFormalSym(impl, b.idx)
    bd = substByRefBody(bd, formalInBody(impl, fs.f), b)
  result[6] = bd

proc stripFieldChecks(n: NimNode): NimNode =
  ## RFC-0005 S8bs. `n` with each variant arm field access
  ## (`nnkCheckedFieldExpr`) replaced by its field access: the arm is
  ## checked where the actual is evaluated (`byRefSub`), as Nim checks it
  ## once, where it takes the field's address.
  if n.kind == nnkCheckedFieldExpr and n.len > 0:
    return stripFieldChecks(n[0])
  if n.len == 0: return n
  result = copyNimNode(n)
  for c in n: result.add stripFieldChecks(c)

proc byRefSub(calleeSym: NimNode; idx: int; lv0, actual: NimNode;
              viaAddr: bool): ByRefSub =
  ## RFC-0005 S8ba. Pass the heap lvalue `lv` to `calleeSym`'s `idx`-th
  ## formal BY REFERENCE: Nim passes its address, so the callee's writes and
  ## any direct access it makes through a global or a capture (`gBox.x = 5`
  ## while `lv` is `p.x` and `gBox == p`) land on one cell in its order.
  ## The callee is specialised: the formal's uses are spelled as `lv`, whose
  ## last ref is a fresh parameter that takes the formal's place and is
  ## given the ref the caller evaluates at the call (so a callee that
  ## rebinds the variable the ref came from does not move the address, as
  ## in Nim). `lv` must reach its cell through that one ref by value-object
  ## fields only (`p.x`, `p.a.b`, `p[]`, `o.inner.x`; the ref a symbol or a
  ## field of one), and the formal must have no use the specialisation
  ## cannot spell (a non-generic callee; a `var T` formal, or a `ptr T` one,
  ## every use of which is replaced). `actual` is the argument as written
  ## (`nnkHiddenAddr(lv)`, or `addr lv` when `viaAddr`). `idx` is -1 when
  ## the lvalue cannot be passed this way.
  ##
  ## RFC-0005 S8bd: the ref may also be an element (`a[i].x`; the index is
  ## read once, with the ref, before the call) or a user call's result
  ## (`getBox().x`, called once), and the callee may be generic: the
  ## specialisation is made of the instantiation (`ensureProcRegistered`).
  ##
  ## RFC-0005 S8bs: a variant arm's field on the way (`po[].a`) too; its
  ## arm is checked where the caller evaluates the actual
  ## (`stripFieldChecks`).
  result.idx = -1
  if calleeSym.kind != nnkSym: return
  var lv = stripFieldChecks(lv0)
  let impl = resolveRoutineImpl(calleeSym)
  if impl == nil: return
  let fs = byRefFormalSym(impl, idx)
  if not fs.ok or fs.isPtr != viaAddr: return
  var fields: seq[string]
  # RFC-0005 S8bg: a representation-preserving conversion of the whole
  # lvalue (`int(b.m)`, a `distinct` unwrap outside every field, or a
  # `range` to its base) is transparent too: stripped before the
  # field/deref walk below, which then sees the conversion's own operand,
  # unconverted. A conversion cannot sit any deeper in the chain (at the
  # `t[0]` position just below, the operand of the mandatory deref further
  # down): to be dereferenced at all, it would have to convert TO a
  # ref/ptr, which only a `ref`/`ptr` inheritance up/downcast does, and
  # that one is NOT representation-preserving here (the heap model gives
  # every declared ref/ptr type its own Z3 sort; see `convReprPreserving`)
  # -- so there is no shape for a conversion to reach that position.
  while lv.kind in {nnkConv, nnkHiddenStdConv, nnkHiddenSubConv} and
        lv.len > 0 and convReprPreserving(lv[^1], lv):
    lv = lv[^1]
  var t = lv
  while t.kind == nnkDotExpr and t.len == 2 and t[1].kind == nnkSym:
    fields.add macros.strVal(t[1])
    t = t[0]
  if t.kind notin {nnkHiddenDeref, nnkDerefExpr} or t.len != 1 or
     isVarIndirection(t):
    return
  # The marked symbol only names the parameter: a field's own symbol
  # (`inner` in `o.inner`) carries the ref's type as well as a variable's.
  let src =
    if t[0].kind == nnkSym: t[0]
    elif t[0].kind == nnkDotExpr and t[0].len == 2 and t[0][1].kind == nnkSym:
      t[0][1]
    elif t[0].kind == nnkBracketExpr or
         (t[0].kind != nnkSym and t[0].len == 0 and byRefName(t[0]).len > 0):
      t[0]   ## RFC-0005 S8bd: marked as itself (`markByRef`)
    elif t[0].kind in {nnkConv, nnkHiddenSubConv, nnkHiddenStdConv} and
         t[0].len > 0 and hierarchyConv(t[0], t[0][^1]).isHier:
      # RFC-0005 S8bh (item 3): a ref converted along its inheritance chain
      # (`Base(d).x`) is the operand's own address; marked as itself, like an
      # element, and evaluated once (with a down-conversion's check) before
      # the call.
      t[0]
    elif t[0].kind in {nnkCall, nnkCommand} and t[0].len > 0 and
         t[0][0].kind == nnkSym and isUserCallee(t[0][0]):
      # RFC-0005 S8bd: a call's result is named by the callee's own
      # `result` symbol, which has the type the call returns.
      let ci = resolveRoutineImpl(t[0][0])
      if ci != nil and ci.len > 7 and ci[7].kind == nnkSym and
         sameType(ci[7].getTypeInst, t[0].getTypeInst):
        ci[7]
      else: nil
    else: nil
  if src.isNil: return
  let baseNode = t[0]
  let mk = markByRef(src)
  if mk.isNil: return
  proc rebuild(n: NimNode; depth: int; mk: NimNode): NimNode =
    result = copyNimNode(n)
    if depth == 0:
      result.add mk
    else:
      result.add rebuild(n[0], depth - 1, mk)
      result.add copyNimTree(n[1])
  var b = ByRefSub(idx: idx, isPtr: fs.isPtr, tail: rebuild(lv, fields.len, mk),
                   name: strVal(mk), baseTy: classifyType(baseNode).ty,
                   base: baseNode)
  var a = actual
  while a.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and a.len > 0:
    a = a[^1]
  b.addrNode = copyNimNode(a)
  b.addrNode.add copyNimTree(b.tail)
  var path = ""
  for k in countdown(fields.high, 0): path.add "." & fields[k]
  b.keyPart = (if fs.isPtr: "p" else: "v") & byRefTypeKey(baseNode) & "/" &
              byRefTypeKey(t) & path
  # RFC-0005 S8bd: the body's own symbol for the formal (`formalInBody`).
  let f = formalInBody(impl, fs.f)
  if f.isNil or mentionsSym(substByRefBody(impl[6], f, b), f): return
  b

proc isToOpenArray(n: NimNode): bool =
  ## RFC-0005 S8bu. `n` is system's `toOpenArray(x, first, last)`.
  n.kind in {nnkCall, nnkCommand} and n.len == 4 and n[0].kind == nnkSym and
    isBuiltinNamed(n[0], ["toOpenArray"])

proc openArraySource(n: NimNode): NimNode =
  ## RFC-0005 S8bu. The actual an `openArray` view is taken of: `n` without
  ## the conversion Nim inserts to the parameter's type (`s`, `a`, or a
  ## `toOpenArray` call).
  result = n
  while result.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and
        result.len == 2 and result.typeKind in {ntyOpenArray, ntyVarargs}:
    result = result[1]

proc arrayAsSeq(x: NimNode; preamble: var seq[IRStmt]; ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bu. The array `x` as the seq of its elements (an openArray
  ## view of a whole array), `x` evaluated once.
  let aty = classifyType(x).ty
  let a = freshSynth(ctx, "oaArr")
  preamble.add mkLet(a, aty, parseExpr(x, preamble, ctx))
  var elems: seq[IRExpr]
  for k in 0 ..< aty.size: elems.add mkIndex(mkVar(a), mkIntLit(int64(k)))
  mkSeqLit(elems, aty.elemTy)

proc toOpenArraySlice(x: NimNode; preamble: var seq[IRStmt]; ctx: ParseCtx;
                      lo: var IRExpr): IRExpr =
  ## RFC-0005 S8bu. `toOpenArray(src, first, last)`: the view of `src` (a seq
  ## or an array, evaluated once, then the bounds, in Nim's order) from
  ## position `first` to `last`, a slice (`iekSeqSlice`) whose bounds are
  ## fixed `let`s (`lo` names the first, for a write-back). Nim checks the
  ## bounds unless the view is empty by `last == first - 1` (probe on the
  ## pinned toolchain: `(5, 4)` and `(-1, -2)` of a 4-element seq are empty,
  ## `(5, 3)` raises `IndexDefect`), which is the slice's own check whenever
  ## `last >= first - 1`. Below that Nim raises nothing and makes a view of
  ## negative length (`(2, 0)` has `len == -1`) whose reads are past the
  ## storage: declined on its paths. The bounds are the program's `int`s
  ## (bit-vectors, compared as such here); the slice takes them across the
  ## signed Int bridge (`ssView`).
  let src = x[1]
  let cls = classifyType(src).ty
  let intTy = tInt(64, signed = true)
  var baseIR: IRExpr
  var low = 0'i64
  case cls.kind
  of itSeq:
    baseIR = parseExpr(src, preamble, ctx)
  of itArray:
    baseIR = arrayAsSeq(src, preamble, ctx)
    low = arrayIndexLow(src)
  else:
    preamble.add ctx.declineAtSite(feUnsupportedOp,
      siteMsg(x, "RFC-0005 S8bu: `toOpenArray` of a " & $cls.kind &
              " (`" & src.repr & "`) is not modelled: the walk views a seq " &
              "or an array only (feUnsupportedOp)"),
      "toOpenArray of an unmodelled storage (feUnsupportedOp)")
    lo = mkIntLit(0)
    return mkSeqLit(@[], classifyType(x).ty.seqElemTy)
  let elemTy = classifyType(x).ty.seqElemTy
  let b = freshSynth(ctx, "oaBase")
  preamble.add mkLet(b, tSeq(elemTy), baseIR)
  var bounds: seq[IRExpr]
  for k in 2 .. 3:
    var e = parseExpr(x[k], preamble, ctx)
    if low != 0: e = mkBinop(bSub, e, mkIntLit(low))
    let t = freshSynth(ctx, "oaBound")
    preamble.add mkLet(t, intTy, e)
    bounds.add mkVar(t)
  preamble.add mkIf(@[mkBranch(
    mkBinop(bLt, bounds[1], mkBinop(bSub, bounds[0], mkIntLit(1))),
    ctx.declineAtSite(feUnsupportedOp,
      siteMsg(x, "RFC-0005 S8bu: `" & x.repr & "` may have `last < first " &
              "- 1`, which Nim does not check: the view has a negative " &
              "length and its reads are past the storage, which the walk " &
              "does not model (feUnsupportedOp)"),
      "toOpenArray of negative length (feUnsupportedOp)"))])
  lo = bounds[0]
  mkSeqSlice(mkVar(b), bounds[0], bounds[1], view = true)

proc openArrayView(n: NimNode; preamble: var seq[IRStmt];
                   ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bu. The seq the `openArray[T]` actual `n` views (the walk
  ## holds an openArray as that seq, `classifyType`): a seq itself, an
  ## array's elements, or a `toOpenArray` slice of either. A string's
  ## (`openArray[char]`) is declined.
  let x = openArraySource(n)
  if isToOpenArray(x):
    var lo: IRExpr
    return toOpenArraySlice(x, preamble, ctx, lo)
  let cls = classifyType(x).ty
  case cls.kind
  of itSeq: parseExpr(x, preamble, ctx)
  of itArray: arrayAsSeq(x, preamble, ctx)
  else:
    preamble.add ctx.declineAtSite(feUnsupportedOp,
      siteMsg(n, "RFC-0005 S8bu: an `openArray` view of a " & $cls.kind &
              " (`" & x.repr & "`) is not modelled: the walk views a seq " &
              "or an array only (feUnsupportedOp)"),
      "openArray view of an unmodelled storage (feUnsupportedOp)")
    mkSeqLit(@[], classifyType(n).ty.seqElemTy)

proc varLocOf(lv: NimNode; temp, mode: string;
              preamble: var seq[IRStmt]; ctx: ParseCtx;
              locs: var seq[VarLoc]) =
  ## RFC-0005 S8bs. Record where the copy-in/copy-out argument `temp` came
  ## from (`IRStmt.cVarLocs`) when `lv` is a path into a routine's variable
  ## (`b.x`, `o.inner.y`, `s[i]`, a variant arm's `o.a`), so the walk can
  ## tell a callee that reaches the variable through its address cell (`gpb
  ## = addr b`, then `setX(b.x)` writing `gpb[].x`). A field step is the
  ## field's name; an index is read into a `let` the walker reads (it is
  ## free of side effects, `stableIndex`, so that is the value the actual
  ## used); any other step is `?`, which the walker declines if the
  ## variable has a cell. A lvalue through a ref or ptr is a heap cell, not
  ## the variable's: nothing is recorded. For a by-value argument (`mode`
  ## `ptr` or `copy`) only a path is recorded: any other expression is a
  ## new value.
  var heapSteps: seq[NimNode]
  let root = lvalueRoot(lv, heapSteps)
  if root.isNil or root.kind != nnkSym or heapSteps.len > 0 or
     symKind(root) notin {nskVar, nskLet, nskParam, nskResult, nskForVar} or
     isModuleGlobal(root):
    return
  var rev: seq[NimNode]
  var t = lv
  var ok = true
  while t.kind != nnkSym:
    case t.kind
    of nnkCheckedFieldExpr:
      if t.len < 1 or t[0].kind != nnkDotExpr:
        ok = false
        break
      t = t[0]
    of nnkDotExpr:
      if t.len != 2 or t[1].kind != nnkSym:
        ok = false
        break
      rev.add t
      t = t[0]
    of nnkBracketExpr:
      # RFC-0005 S8bu: an array's element too (`locGet`).
      if t.len != 2 or t[0].typeKind notin {ntySequence, ntyArray} or
         not stableIndex(t[1], []):
        ok = false
        break
      rev.add t
      t = t[0]
    of nnkHiddenDeref:
      if not isVarIndirection(t):
        ok = false
        break
      t = t[0]
    else:
      ok = false
      break
  var path: seq[string]
  if not ok:
    if mode in ["ptr", "copy"]: return
    path = @["?"]
  else:
    for k in countdown(rev.high, 0):
      let st = rev[k]
      if st.kind == nnkDotExpr:
        path.add macros.strVal(st[1])
      else:
        let ix = freshSynth(ctx, "varLocIx")
        var ixIR = parseExpr(st[1], preamble, ctx)
        # RFC-0005 S8bu: an array's step is its position (the index less
        # the array's first index).
        if st[0].typeKind == ntyArray:
          let lo = arrayIndexLow(st[0])
          if lo != 0: ixIR = mkBinop(bSub, ixIR, mkIntLit(lo))
        preamble.add mkLet(ix, classifyType(st[1]).ty, ixIR)
        path.add "[" & ix
  locs.add (temp: temp, root: strVal(root), path: path, mode: mode)

proc byValueShare(a: NimNode): string =
  ## RFC-0005 S8bs. How Nim passes the by-value argument `a` (`VarLoc`'s
  ## `mode`): `ptr` by address -- an array; an object that is inheritable
  ## or larger than three words, a tuple larger than three words (the C
  ## code generator's `ccgIntroducedPtr`) -- or `copy`, a copy that shares
  ## a seq's or string's memory with the original; "" for a copy that
  ## shares nothing the walk keeps apart (a scalar, a ref, a small object of
  ## scalars).
  let ty = a.getTypeInst
  proc payload(t: NimNode; depth: int): bool =
    if depth > 8: return true
    case t.typeKind
    of ntySequence, ntyString, ntyOpenArray, ntyVarargs: true
    of ntyObject, ntyTuple, ntyArray:
      let impl = t.getTypeImpl
      var found = false
      proc scan(n: NimNode) =
        if found: return
        if n.kind == nnkIdentDefs and n.len >= 2:
          if n[^2].kind != nnkEmpty and payload(n[^2], depth + 1):
            found = true
          return
        if n.kind == nnkBracketExpr and t.typeKind == ntyArray and n.len == 3:
          if payload(n[2], depth + 1): found = true
          return
        for c in n: scan(c)
      scan(impl)
      found
    else: false
  case ty.typeKind
  of ntySequence, ntyString: "copy"
  of ntyArray, ntyOpenArray, ntyVarargs: "ptr"
  of ntyObject:
    let impl = ty.getTypeImpl
    if impl.kind == nnkObjectTy and impl.len > 1 and
       impl[1].kind == nnkOfInherit:
      return "ptr"
    if getSize(ty) > 3 * sizeof(float): return "ptr"
    if payload(ty, 0): "copy" else: ""
  of ntyTuple:
    if getSize(ty) > 3 * sizeof(float): return "ptr"
    if payload(ty, 0): "copy" else: ""
  else: ""

proc byValueLoc(arg: NimNode; k: int; preamble: var seq[IRStmt];
                ctx: ParseCtx; locs: var seq[VarLoc]) =
  ## RFC-0005 S8bs. Record where the by-value argument `arg` (the `k`-th)
  ## came from (`VarLoc` `#<k>`) when Nim passes it by address or shares its
  ## memory (`byValueShare`): a path the walk may keep equal to a cell.
  ## RFC-0005 S8bu: for a closure or proc-value call too (`ccVarLocs`).
  ## An `openArray` view shares its storage's memory: a whole seq's is the
  ## seq's own (`copy`); an array's, or a `toOpenArray` slice's, is a
  ## location the walker does not bind (`?`: declined when the storage's
  ## variable has a cell or element cells).
  if arg.kind == nnkHiddenAddr: return
  let src = openArraySource(arg)
  if src != arg or isToOpenArray(arg):
    let st = if isToOpenArray(src): src[1] else: src
    if not isToOpenArray(src) and classifyType(st).ty.kind == itSeq:
      varLocOf(st, "#" & $k, "copy", preamble, ctx, locs)
    else:
      var vl: seq[VarLoc]
      varLocOf(st, "#" & $k, "var", preamble, ctx, vl)
      for l in vl:
        locs.add (temp: l.temp, root: l.root, path: @["?"], mode: "copy")
    return
  var a = arg
  while a.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and a.len > 0 and
        sameType(a.getTypeInst, a[^1].getTypeInst):
    a = a[^1]
  let share = byValueShare(a)
  if share.len > 0:
    varLocOf(a, "#" & $k, share, preamble, ctx, locs)

proc armChecked(lv: NimNode; b: ByRefSub; preamble: var seq[IRStmt];
                ctx: ParseCtx): bool =
  ## RFC-0005 S8bs. A by-reference lvalue through a variant arm's field
  ## (`po[].a`): Nim checks the arm where it takes the address, before the
  ## call, so the lvalue is read there once (its `FieldDefect` fork) when
  ## its ref is a variable, read again without effect. False for any other
  ## ref (a call, an element): it cannot be read twice.
  var has = false
  proc scan(n: NimNode) =
    if n.kind == nnkCheckedFieldExpr: has = true
    for c in n: scan(c)
  scan(lv)
  if not has: return true
  if b.base.kind != nnkSym: return false
  preamble.add mkLet(freshSynth(ctx, "armCheck"), classifyType(lv).ty,
                     parseExpr(lv, preamble, ctx))
  true

proc addrTakenIn(n, sym: NimNode): bool =
  ## RFC-0005 S8bn (item 3). `n` takes the address of a location rooted at
  ## the symbol `sym` (`addr x`, `addr x.f`, `unsafeAddr x`). A `var`
  ## argument (`nnkHiddenAddr`) is not one: no pointer outlives that call.
  if n == nil: return false
  var operand: NimNode = nil
  if n.kind == nnkAddr and n.len >= 1:
    operand = n[^1]
  elif n.kind in {nnkCall, nnkCommand} and n.len == 2 and
       n[0].kind == nnkSym and macros.strVal(n[0]) in ["addr", "unsafeAddr"]:
    operand = n[1]
  if operand != nil:
    var steps: seq[NimNode]
    let r = lvalueRoot(operand, steps)
    if r != nil and r.kind == nnkSym and containsSym(@[sym], r): return true
  for c in n:
    if addrTakenIn(c, sym): return true
  false

proc varActualPtrSafety(lv: NimNode): int =
  ## RFC-0005 S8bn (item 3). What the location `lv`, passed to a `var`
  ## formal, is to a `ptr` of unknown origin (`IRStmt.cVarPtrSafe`): 1 when
  ## it is a part of a local of the routine that declares it (no
  ## dereference on the way) whose address that routine never takes, so no
  ## pointer can address it; 2 when it is that routine's own `var` formal,
  ## passed on whole (its location is the formal's own actual); 0 for any
  ## other location (a global, a heap cell, a taken address).
  var steps: seq[NimNode]
  let root = lvalueRoot(lv, steps)
  if root.isNil or root.kind != nnkSym or steps.len > 0 or isModuleGlobal(root):
    return 0
  case root.symKind
  of nskParam:
    if lv.kind == nnkSym and root.getTypeInst.kind == nnkVarTy: 2 else: 0
  of nskVar, nskLet, nskResult, nskForVar:
    let o = root.owner
    if o.isNil or o.kind != nnkSym: return 0
    let impl = o.getImpl
    if impl.isNil or impl.kind == nnkNilLit or addrTakenIn(impl, root): 0
    else: 1
  else: 0

proc varSeqViews(n: NimNode): NimNode =
  ## RFC-0005 S8bu. The call `n` with each `var openArray` actual that views
  ## a whole seq (`nnkHiddenAddr(conv(s))`) spelled as the seq passed by
  ## address (`nnkHiddenAddr(s)`), as a `var seq` actual is: the formal is
  ## that seq in the walk (`classifyType`), and Nim passes its address.
  result = n
  for i in 1 ..< n.len:
    let a = n[i]
    if a.kind != nnkHiddenAddr or a.len != 1: continue
    let x = openArraySource(a[0])
    if x == a[0] or isToOpenArray(x) or classifyType(x).ty.kind != itSeq:
      continue
    if result == n: result = copyNimTree(n)
    let b = copyNimNode(a)
    b.add x
    result[i] = b

proc varViewSource(a: NimNode): NimNode =
  ## RFC-0005 S8bu. For a `var openArray` actual viewing an array or a
  ## `toOpenArray` slice (after `varSeqViews`), the view (the array, or the
  ## `toOpenArray` call); nil for any other actual.
  if a.kind != nnkHiddenAddr or a.len != 1: return nil
  let x = openArraySource(a[0])
  if isToOpenArray(x): return x
  if x != a[0] and classifyType(x).ty.kind == itArray: return x
  nil

proc viewTemp(view, actual: NimNode; preamble: var seq[IRStmt];
              ctx: ParseCtx; lo: var IRExpr): string =
  ## RFC-0005 S8bu. A temporary seq holding the `var openArray` view
  ## `view` (`varViewSource`) of the actual `actual`; `lo` names the
  ## slice's first position (nil for a whole array).
  lo = nil
  let viewIR =
    if isToOpenArray(view): toOpenArraySlice(view, preamble, ctx, lo)
    else: arrayAsSeq(view, preamble, ctx)
  result = freshSynth(ctx, "oaView")
  preamble.add mkLet(result, classifyType(actual).ty, viewIR)

proc viewStorage(view: NimNode): NimNode =
  ## RFC-0005 S8bu. The storage a `var openArray` view writes to.
  if isToOpenArray(view): view[1] else: view

proc viewWriteBack(view, actual: NimNode; t: string; lo: IRExpr;
                   ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bu. The temporary `t` (`viewTemp`) written back over the
  ## elements of its storage it views: a seq's by `iekSeqSplice`, an
  ## array's element by element (an openArray's length never changes).
  let storage = viewStorage(view)
  var wbPre: seq[IRStmt]
  let elemTy = classifyType(actual).ty.seqElemTy
  let back =
    if classifyType(storage).ty.kind == itSeq:
      mkSeqSplice(parseExpr(storage, wbPre, ctx), lo, mkVar(t))
    else:
      let aty = classifyType(storage).ty
      let whole =
        if lo == nil: mkVar(t)
        else: mkSeqSplice(arrayAsSeq(storage, wbPre, ctx), lo, mkVar(t))
      let ws = freshSynth(ctx, "oaBack")
      wbPre.add mkLet(ws, tSeq(elemTy), whole)
      var elems: seq[IRExpr]
      for k in 0 ..< aty.size:
        let e = freshSynth(ctx, "oaElem")
        wbPre.add mkIndexStmt(e, mkVar(ws), mkIntLit(int64(k)), elemTy)
        elems.add mkVar(e)
      mkArrayLit(elems, aty.elemTy)
  let w = parseAsgn(nnkAsgn.newTree(storage, newEmptyNode()), back, wbPre, ctx)
  mkBlock(wbPre & @[w])

proc userCallStmt(n0, calleeSym: NimNode; callKey, retName: string;
                  retTy: IRType; offsetPositions: seq[int];
                  preamble: var seq[IRStmt]; ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8ac. The `isCall` of a walked user routine, with its
  ## arguments lowered into `preamble`. A `var` formal's actual (Nim spells
  ## it `nnkHiddenAddr`) that is a VARIABLE is written back by the walker
  ## (#140, by name). One that is any other lvalue -- a field (`h.cur`,
  ## `o.a`), an element (`s[0]`), a dereference (`p[]`) -- had no such
  ## channel: its argument is a temporary, and the callee's writes to the
  ## formal were dropped (a silent false verdict). It is now bound to a
  ## temporary the walker writes back, and the call is wrapped as
  ##   try: <call>
  ##   finally: <lvalue> = <temporary>
  ## so the write lands on every exit, a raise included, as it does in Nim
  ## (the callee writes through the address before it raises). The write
  ## takes `parseAsgn`'s lvalue arms, so an lvalue shape a source
  ## assignment declines declines here too, as does a call where the
  ## callee could reach the location another way (`varActualMayAlias`).
  ##
  ## RFC-0005 S8an: an `addr lv` actual (`ptr T` formal) is a heap cell for
  ## the call. `lv` is stored into a fresh `ptr` cell, the cell is the
  ## argument (the callee reads and writes it through `p[]`), and the cell
  ## is read back into `lv` in the same `finally`. Every `addr` of one
  ## lvalue in one call is one cell, so `p == q` and a write through `p`
  ## seen through `q` are exact. The model holds only while the pointer
  ## cannot outlive the call (`ptrFormalStaysLocal`), and while the callee
  ## cannot reach `lv` another way (`addrActualMayAlias`, and the
  ## `cGuardRoots` the walker withholds); otherwise the call declines.
  ##
  ## RFC-0005 S8ba: a heap lvalue (a `var` actual, or an `addr` one) the
  ## callee can also reach through a global or a capture
  ## (`outerReachesCell`) is passed by reference instead (`byRefSub`): the
  ## call goes to a specialisation of the callee that reads and writes the
  ## cell itself. It declines (S8au's `feUnsupportedOp`) only when the
  ## lvalue or the formal has a shape that cannot be passed so.
  ##
  ## RFC-0005 S8bf: so is a heap lvalue that may be the same cell as
  ## another heap lvalue actual of the call (`heapCellsMayMeet`: `let q =
  ## p; setBoth(p.x, q.x)`). Each is passed by reference, so the callee's
  ## writes through the two formals land on the heap in its order, and the
  ## heap decides whether the two refs are one. An actual of such a pair
  ## that cannot be passed so takes the write-back below, which declines
  ## (`varActualMayAlias` sees the other).
  ##
  ## RFC-0005 S8bu: a `var openArray` actual is a view of its storage. One
  ## of a whole seq is the seq passed by address (`varSeqViews`). One of an
  ## array or of a `toOpenArray` slice is a temporary seq holding the view,
  ## written back over the viewed elements of the storage in the same
  ## `finally` (an openArray's length never changes), under the gates of a
  ## `var` actual's write-back.
  let n = varSeqViews(n0)
  var argIRs: seq[IRExpr]
  var byRefs: seq[ByRefSub]   ## RFC-0005 S8ba
  var writeBacks: seq[IRStmt]
  var guards: seq[string]   ## RFC-0005 S8an: `IRStmt.cGuardRoots`
  var varSafe = newSeq[int](max(n.len - 1, 0))   ## RFC-0005 S8bn: `cVarPtrSafe`
  var anyVarActual = false
  var addrCells: seq[tuple[key, cell: string]]   ## RFC-0005 S8an
  var locs: seq[VarLoc]   ## RFC-0005 S8bs: `IRStmt.cVarLocs`
  # RFC-0005 S8au: what the callee reaches outside its arguments, computed
  # once per call and only when a heap actual asks.
  var outer: seq[NimNode]
  var outerDone = false
  proc outerOf(): seq[NimNode] =
    if not outerDone:
      outer = calleeOuterSyms(calleeSym)
      outerDone = true
    outer
  # RFC-0005 S8ax: where each argument's statements start, its type, and
  # whether it is passed by address (`orderOperands`).
  var argMarks: seq[int]
  var argTys: seq[IRType]
  var argFixed: seq[bool]
  # RFC-0005 S8bk: where each by-address argument's lvalue was lowered, so
  # that its address is taken at the call (`placeLateAddr`).
  var argLate: seq[LateAddr]
  # RFC-0005 S8ax: index pairs under which two by-address arguments are
  # one location (`aliasPath`); the call declines on the paths where they
  # all may be equal.
  var aliasConds: seq[AliasIndexPairs]
  # RFC-0005 S8bf: for each argument, the other `var`/`addr` heap actuals
  # whose cell may be its own (`heapCellsMayMeet`). Two `addr`s of one
  # lvalue are one cell already (`addrCells`), not a pair.
  var peers = newSeq[seq[int]](n.len)
  block:
    var cellOf = newSeq[NimNode](n.len)
    for i in 1 ..< n.len:
      let c = actualCell(n[i])
      if c != nil and (n[i].kind == nnkHiddenAddr or
                       addrActualLvalue(n[i]) != nil):
        cellOf[i] = c
    for i in 1 ..< n.len:
      if cellOf[i].isNil: continue
      for j in 1 ..< n.len:
        if j == i or cellOf[j].isNil: continue
        if addrActualLvalue(n[i]) != nil and addrActualLvalue(n[j]) != nil and
           scopedRepr(cellOf[i]) == scopedRepr(cellOf[j]):
          continue
        if heapCellsMayMeet(cellOf[i], cellOf[j]): peers[i].add j
  for i in 1 ..< n.len:
    argMarks.add preamble.len
    argTys.add(if n[i].typeKind != ntyNone: classifyType(n[i]).ty else: nil)
    argFixed.add(n[i].kind == nnkHiddenAddr or addrActualLvalue(n[i]) != nil)
    argLate.add LateAddr()
    let addrLv = addrActualLvalue(n[i])
    if addrLv != nil:
      var heapSteps: seq[NimNode]
      let root = lvalueRoot(addrLv, heapSteps)
      block byRef:
        # RFC-0005 S8ba: the cell the callee also reaches is passed by
        # reference. Same gates as the cell model below, in its order.
        for c in addrCells:
          if c.key == scopedRepr(addrLv): break byRef
        var seen: seq[string]
        # RFC-0005 S8bd: a lvalue reached through a call's ref is rooted
        # at the call (`byRefRoot`).
        var brSteps: seq[NimNode]
        let brRoot = byRefRoot(addrLv, brSteps)
        # RFC-0005 S8bf: or one that may be another heap actual's cell
        # (`peers`), every one of which is passed so too.
        # RFC-0005 S8ax: index pairs the alias check finds are declined
        # on their paths, as on the cell model's (`aliasConds`).
        var brConds: seq[AliasIndexPairs]
        if brRoot.isNil or not ptrFormalStaysLocal(calleeSym, i - 1, seen) or
           addrActualMayAlias(n, i, addrLv, brRoot, brSteps, brConds,
                              peers[i]) or
           (peers[i].len == 0 and outerReachesCell(outerOf(), brSteps) == nil):
          break byRef
        let b = byRefSub(calleeSym, i - 1, addrLv, n[i], true)
        if b.idx < 0: break byRef
        if not armChecked(addrLv, b, preamble, ctx): break byRef   ## RFC-0005 S8bs
        aliasConds.add brConds
        byRefs.add b
        let lo = preamble.len
        argIRs.add parseExpr(b.base, preamble, ctx)
        argLate[^1] = LateAddr(ok: true, lo: lo, hi: preamble.len,
                               bindEnd: preamble.len,
                               growable: lvalueIndexGrowable(b.base))
        continue
      block:
        var syms: seq[NimNode]
        lvalueVarSyms(addrLv, syms)
        for s in syms:
          if s.strVal notin guards: guards.add s.strVal
      # RFC-0005 S8ax: `addr x` of a routine's variable is its address
      # cell (`addrCellLocal`), which outlives the call: the callee may
      # keep the pointer, and the walker keeps `x` equal to the cell.
      let cellX = addrCellLocal(n[i])
      if cellX != nil:
        if addrActualMayAlias(n, i, addrLv, root, heapSteps, aliasConds,
                              cellsBound = true):   ## RFC-0005 S8bs
          preamble.add ctx.declineAtSite(feUnsupportedOp,
            siteMsg(n, "`addr " & addrLv.repr & "` is passed to `" &
                    calleeSym.strVal & "` alongside another argument that " &
                    "reaches the same location: the cell for the call and " &
                    "the other argument are not one location in the walk " &
                    "(feUnsupportedOp)"),
            "addr argument aliases another argument (feUnsupportedOp)")
        argIRs.add lowerAddrCell(n[i], cellX, preamble, ctx)
        continue
      let key = scopedRepr(addrLv)
      var cell = ""
      for c in addrCells:
        if c.key == key: cell = c.cell
      if cell.len > 0:
        argIRs.add mkVar(cell)
        continue
      cell = freshSynth(ctx, "addrCell")
      addrCells.add (key: key, cell: cell)
      let ptrTy = classifyType(n[i]).ty
      let elemTy = classifyType(addrLv).ty
      var seen: seq[string]
      let escapes = root.isNil or not ptrFormalStaysLocal(calleeSym, i - 1, seen)
      # RFC-0005 S8be: an element of a routine's seq whose pointer may
      # outlive the call is its element cell (`elemCellOf`), which the
      # walker keeps equal to the element wherever the pointer goes.
      let elc = elemCellOf(n[i])
      if escapes and elc.root != nil and
         not addrActualMayAlias(n, i, addrLv, root, heapSteps, aliasConds):
        addrCells.setLen(addrCells.len - 1)
        argIRs.add lowerElemCell(n[i], elc.root, elc.idx, preamble, ctx)
        continue
      if escapes:
        preamble.add ctx.declineUnsafeCast(
          siteMsg(n, "`addr " & addrLv.repr & "` is passed to `" &
                  calleeSym.strVal & "`, which may let the pointer escape " &
                  "the call (it is stored, returned, captured or passed " &
                  "on to a routine that may): the pointee is modelled as " &
                  "a cell for the call only (heUnsafeCast)"),
          "addr argument may escape the call (heUnsafeCast)")
      elif addrActualMayAlias(n, i, addrLv, root, heapSteps, aliasConds):
        preamble.add ctx.declineAtSite(feUnsupportedOp,
          siteMsg(n, "`addr " & addrLv.repr & "` is passed to `" &
                  calleeSym.strVal & "` alongside another argument that " &
                  "reaches the same location: the cell for the call and " &
                  "the other argument are not one location in the walk " &
                  "(feUnsupportedOp)"),
          "addr argument aliases another argument (feUnsupportedOp)")
      elif (let g = outerReachesCell(outerOf(), heapSteps); g != nil):
        # RFC-0005 S8au: the callee reaches the cell through a global or a
        # capture, not only through its arguments.
        preamble.add ctx.declineAtSite(feUnsupportedOp,
          siteMsg(n, "`addr " & addrLv.repr & "` is passed to `" &
                  calleeSym.strVal & "`, which can also reach that heap " &
                  "location through `" & macros.strVal(g) & "` (a " &
                  "module-level global or a captured variable): the cell " &
                  "for the call and the direct access are not one " &
                  "location in the walk (feUnsupportedOp)"),
          "addr argument reachable through a global (feUnsupportedOp)")
      varLocOf(addrLv, cell, "addr", preamble, ctx, locs)   ## RFC-0005 S8bs
      let lvLo = preamble.len
      let lvIR = parseExpr(addrLv, preamble, ctx)
      let lvHi = preamble.len
      preamble.add mkNewT(cell, ptrTy)
      preamble.add mkDerefWrite(mkVar(cell), lvIR, elemTy, ptrFamily = true,
                                cell = true)
      argLate[^1] = LateAddr(ok: true, lo: lvLo, hi: lvHi,
                             bindEnd: preamble.len,
                             growable: lvalueIndexGrowable(addrLv))
      let back = freshSynth(ctx, "addrBack")
      var wbPre = @[mkPtrDeref(back, mkVar(cell), elemTy, cell = true)]
      let w = parseAsgn(nnkAsgn.newTree(addrLv, newEmptyNode()), mkVar(back),
                        wbPre, ctx)
      writeBacks.add mkBlock(wbPre & @[w])
      argIRs.add mkVar(cell)
      continue
    # RFC-0005 S8bu: a `var openArray` view of an array or a slice.
    let view = varViewSource(n[i])
    if view != nil:
      var lo: IRExpr = nil
      let t = viewTemp(view, n[i], preamble, ctx, lo)
      var lv = viewStorage(view)
      if isVarIndirection(lv): lv = lv[0]
      block:
        var syms: seq[NimNode]
        lvalueVarSyms(lv, syms)
        for s in syms:
          if s.strVal notin guards: guards.add s.strVal
      var heapSteps: seq[NimNode]
      let root = if lv.kind == nnkSym: lv else: lvalueRoot(lv, heapSteps)
      if root.isNil or
         varActualMayAlias(n, i, lv, root, heapSteps, aliasConds,
                           cellsBound = true):
        writeBacks.add ctx.declineAtSite(feUnsupportedOp,
          siteMsg(n, "`var openArray` argument `" & view.repr & "` of `" &
                  calleeSym.strVal & "` views a location the callee may " &
                  "reach another way (or it has no root variable): the " &
                  "callee's writes to it are not modelled (feUnsupportedOp)"),
          "var openArray write-back not modelled (feUnsupportedOp)")
      elif (let g = outerReachesCell(outerOf(), heapSteps); g != nil):
        writeBacks.add ctx.declineAtSite(feUnsupportedOp,
          siteMsg(n, "`var openArray` argument `" & view.repr & "` of `" &
                  calleeSym.strVal & "` views a heap location the callee " &
                  "can also reach through `" & macros.strVal(g) & "`: the " &
                  "callee's writes through the two are not modelled in its " &
                  "order (feUnsupportedOp)"),
          "var openArray reachable through a global (feUnsupportedOp)")
      else:
        # The view is not the storage's own shape: a variable with a cell
        # declines in the walker (`bindVarLocs`' path it does not follow).
        var vl: seq[VarLoc]
        varLocOf(lv, t, "var", preamble, ctx, vl)
        for l in vl:
          locs.add (temp: l.temp, root: l.root, path: @["?"], mode: l.mode)
        writeBacks.add viewWriteBack(view, n[i], t, lo, ctx)
      argIRs.add mkVar(t)
      continue
    # RFC-0005 S8bd: a by-reference actual is evaluated once, as its base
    # (below); the lvalue itself is lowered only when it is not one.
    var byRefTaken = false
    # RFC-0005 S8bg: a `var` actual reached through a `cast` (`cast[ptr
    # T](p)[]`): `lvalueRoot`/`byRefRoot` have no case for a `cast`, and
    # below it, the ordinary read does not expect the dummy value a
    # decline already recorded while parsing the cast as a plain
    # expression (`parseExpr`'s own `nnkCast` arm) -- a crash
    # (`lowerLeafInExpr`'s container-kind assert), not a decline. Caught
    # here, before either the by-reference attempt or that read runs, with
    # its own decline naming the cast.
    var castBlocked = false
    var castLv: NimNode = nil
    if n[i].kind == nnkHiddenAddr and n[i].len == 1:
      var lv = n[i][0]
      if isVarIndirection(lv): lv = lv[0]
      if lv.kind != nnkSym and lvalueCastBlocks(lv):
        castBlocked = true
        castLv = lv
      else:
        block byRef:
          # RFC-0005 S8ba: a heap lvalue the callee also reaches through a
          # global or a capture is passed by reference (`byRefSub`). Same
          # gates as the write-back below, in its order.
          if lv.kind == nnkSym: break byRef
          var heapSteps: seq[NimNode]
          let root = byRefRoot(lv, heapSteps)   ## RFC-0005 S8bd
          # RFC-0005 S8bf: or one that may be another heap actual's cell
          # (`peers`), every one of which is passed so too.
          # RFC-0005 S8ax: `aliasConds`, as for an `addr` actual above.
          var brConds: seq[AliasIndexPairs]
          # RFC-0005 S8bs: whether or not the callee can reach the cell
          # another way: Nim passes the lvalue's address, and the cell itself
          # is that, where a copy written back is only while nothing else
          # reaches it.
          if root.isNil or varActualMayAlias(n, i, lv, root, heapSteps,
                                             brConds, peers[i], byRef = true):
            break byRef
          let b = byRefSub(calleeSym, i - 1, lv, n[i], false)
          if b.idx < 0: break byRef
          # RFC-0005 S8bs: the arm check is a read of the lvalue in the
          # late range, so a later argument that may write declines the
          # call (`placeLateAddr` cannot snapshot an arm).
          let lo = preamble.len
          if not armChecked(lv, b, preamble, ctx): break byRef
          aliasConds.add brConds
          byRefs.add b
          argIRs.add parseExpr(b.base, preamble, ctx)
          argLate[^1] = LateAddr(ok: true, lo: lo, hi: preamble.len,
                                 bindEnd: preamble.len,
                                 growable: lvalueIndexGrowable(b.base))
          byRefTaken = true
    if byRefTaken: continue
    if castBlocked:
      writeBacks.add ctx.declineAtSite(feUnsupportedOp,
        siteMsg(n, "`var` argument `" & castLv.repr & "` of `" &
                calleeSym.strVal & "` is reached through a `cast`, which " &
                "may reinterpret the memory at that address: the callee's " &
                "writes through it are not modelled (feUnsupportedOp)"),
        "var argument reached through a cast (feUnsupportedOp)")
      let dummyTy = classifyType(castLv).ty
      let dummy = zeroValueForType(dummyTy)
      argIRs.add(if dummy != nil: dummy else: mkIntLit(0))
      continue
    let irLo = preamble.len
    var ir = parseExpr(n[i], preamble, ctx)
    let irHi = preamble.len
    # RFC-0005 S8bs: a by-value argument Nim passes by address, or whose
    # memory it shares, is a path the walk may keep equal to a cell.
    byValueLoc(n[i], i - 1, preamble, ctx, locs)
    if n[i].kind == nnkSym and varActualPtrSafety(n[i]) == 2:
      # RFC-0005 S8bn: the caller's own `var` formal passed on to a `var`
      # formal (Nim drops the `addr`); read only for a `var` formal.
      varSafe[i - 1] = 2
      anyVarActual = true
    if n[i].kind == nnkHiddenAddr and n[i].len == 1:
      var lv = n[i][0]
      if isVarIndirection(lv): lv = lv[0]
      varSafe[i - 1] = varActualPtrSafety(lv)   ## RFC-0005 S8bn
      anyVarActual = true
      block:
        var syms: seq[NimNode]
        lvalueVarSyms(lv, syms)
        for s in syms:
          if s.strVal notin guards: guards.add s.strVal
      if lv.kind == nnkSym:
        # RFC-0005 S8an: a plain variable named by another argument that
        # may pass it by address (`varActualMayAlias`) declines too.
        if varActualMayAlias(n, i, lv, lv, @[], aliasConds,
                             cellsBound = true):   ## RFC-0005 S8bs
          writeBacks.add ctx.declineAtSite(feUnsupportedOp,
            siteMsg(n, "`var` argument `" & lv.repr & "` of `" &
                    calleeSym.strVal & "` is also reached through another " &
                    "argument: the callee's writes through the two are " &
                    "not modelled in its order (feUnsupportedOp)"),
            "var argument write-back not modelled (feUnsupportedOp)")
      else:
        var heapSteps: seq[NimNode]
        let root = lvalueRoot(lv, heapSteps)
        if root.isNil or
           varActualMayAlias(n, i, lv, root, heapSteps, aliasConds,
                             cellsBound = true):   ## RFC-0005 S8bs
          writeBacks.add ctx.declineAtSite(feUnsupportedOp,
            siteMsg(n, "`var` argument `" & lv.repr & "` of `" &
                    calleeSym.strVal & "` is not a variable and the callee " &
                    "may reach it another way (or it has no root " &
                    "variable): the callee's writes to it are not " &
                    "modelled (feUnsupportedOp)"),
            "var argument write-back not modelled (feUnsupportedOp)")
        elif (let g = outerReachesCell(outerOf(), heapSteps); g != nil):
          # RFC-0005 S8au: the callee reaches the heap location through a
          # global or a capture (`gBox.x = 5` while `p.x` is the actual and
          # `gBox == p`). Nim writes one cell in the callee's order; the
          # write-back after the call would land over the direct write.
          writeBacks.add ctx.declineAtSite(feUnsupportedOp,
            siteMsg(n, "`var` argument `" & lv.repr & "` of `" &
                    calleeSym.strVal & "` is a heap location the callee " &
                    "can also reach through `" & macros.strVal(g) & "` (a " &
                    "module-level global or a captured variable): the " &
                    "callee's writes through the two are not modelled in " &
                    "its order (feUnsupportedOp)"),
            "var argument reachable through a global (feUnsupportedOp)")
        else:
          if ir.kind != iekVar:
            let t = freshSynth(ctx, "varArg")
            preamble.add mkLet(t, classifyType(lv).ty, ir)
            ir = mkVar(t)
          varLocOf(lv, ir.vname, "var", preamble, ctx, locs)   ## RFC-0005 S8bs
          var wbPre: seq[IRStmt]
          let w = parseAsgn(nnkAsgn.newTree(lv, newEmptyNode()), ir, wbPre, ctx)
          # An lvalue shape `parseAsgn` declines is its own scoped marker
          # (`isUnsupported`): every path leaving the call reaches it.
          writeBacks.add(if wbPre.len == 0: w else: mkBlock(wbPre & @[w]))
          # RFC-0005 S8bk: copied in at the call, through the address the
          # copy-out writes (`placeLateAddr`).
          argLate[^1] = LateAddr(ok: true, lo: irLo, hi: irHi,
                                 bindEnd: preamble.len,
                                 growable: lvalueIndexGrowable(lv))
    argIRs.add ir
  orderOperands(preamble, argMarks, argIRs, argTys, omOperands, ctx,
                argFixed, argLate)   ## RFC-0005 S8ax, S8bk; S8be: in a `while` guard too
  # RFC-0005 S8ax: the indices are free of side effects (`stableIndex`), so
  # reading them again after the arguments is reading the same values.
  for pairs in aliasConds:
    var cond: IRExpr = nil
    for pr in pairs:
      let eq = mkBinop(bEq, parseExpr(pr.a, preamble, ctx),
                       parseExpr(pr.b, preamble, ctx))
      cond = if cond == nil: eq else: mkBinop(bAnd, cond, eq)
    preamble.add mkIf(@[IRBranch(cond: cond,
      body: ctx.declineAtSite(feUnsupportedOp,
        siteMsg(n, "two arguments of `" & calleeSym.strVal & "` passed by " &
                "address are one location when their indices are equal, " &
                "which this path allows: the callee's writes through the " &
                "two are not modelled in its order (feUnsupportedOp)"),
        "by-address arguments may be one location (feUnsupportedOp)"))])
  # RFC-0005 S8ba: the by-reference formals call the callee's
  # specialisation to them.
  let key = if byRefs.len == 0: callKey
            else: ensureProcRegistered(ctx, calleeSym, n, byRefs)
  let call = mkCall(key, retName, argIRs, retTy, offsetPositions, guards,
                    locs, (if anyVarActual: varSafe else: @[]))
  if writeBacks.len == 0: call
  else: mkTry(call, @[], mkBlock(writeBacks))

const maxModelledInitialSize = 1'i64 shl 20
  ## RFC-0005 S8at. The largest `initialSize` an `initTable`/`initHashSet`
  ## call is modelled at (see `parseInitContainer`). RFC-0005 S8bc / batch
  ## 5: the largest length every seq constructor is (`parseNewSeqLen`).

proc sizeOperandOnce(ir: IRExpr; n: NimNode; preamble: var seq[IRStmt];
                     ctx: ParseCtx): IRExpr =
  ## RFC-0005 batch 5. A size or length argument read by its guard's
  ## branches and by the result: bound to a `let` unless it is already an
  ## atom, so it is evaluated once, as Nim evaluates it. `parseExpr` leaves
  ## a closure call inline, and `parseAtomicOperand` hoists nothing in a
  ## `while` guard: `while newSeq[int](f(x)).len > 2` applied `f` three
  ## times per test (each guard branch and the length), and
  ## `initTable[int, int](f(x))` twice -- a write `f` makes landed twice (a
  ## false `sxSat`, and a false `sxUnsat` for the count Nim makes). The
  ## guard already gives the `while` guard a preamble, so binding adds
  ## none.
  if isAtomicIR(ir) or n.typeKind == ntyNone: return ir
  let tmp = freshSynth(ctx, "sizeArg")
  preamble.add mkLet(tmp, classifyType(n).ty, ir)
  mkVar(tmp)

proc parseInitContainer(n, calleeSym: NimNode; preamble: var seq[IRStmt];
                        ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8at. `initTable[K, V](initialSize)` / `initHashSet[T](...)`
  ## of the stdlib, when the result classifies as a modelled `Table` /
  ## `HashSet`: the empty container (`zeroValueForType`, the value an
  ## uninitialised `var t: Table[K, V]` already gets); `nil` for any other
  ## call. The call was walked as a generic user callee, whose return type
  ## names generics no argument binds, and `classifyType` aborted macro
  ## expansion on it ("node has no type"): a crash on valid user code.
  ##
  ## The size only sizes the backing store, except that Nim converts it to
  ## `Natural` (`slotsNeeded(count: Natural)`), so a negative size raises
  ## `RangeDefect` -- forked here. A size above `maxModelledInitialSize`
  ## overflows the slot arithmetic (`count div 2 + count + 4`, an
  ## `OverflowDefect`) or exhausts memory allocating the store, depending on
  ## its value and the host: that path is declined, scoped to it.
  if calleeSym.kind != nnkSym or
     calleeSym.strVal notin ["initTable", "initHashSet"] or
     not isStdlibDecl(calleeSym) or n.len > 2:
    return nil
  let cls = classifyType(n)
  if cls.ty.kind notin {itTable, itSet}: return nil
  if n.len == 2:
    var lit = n[1]
    while lit.kind in {nnkHiddenStdConv, nnkConv} and lit.len >= 1:
      lit = lit[lit.len - 1]
    let literalOk = lit.kind in nnkCharLit..nnkUInt64Lit and
      lit.intVal >= 0 and lit.intVal <= maxModelledInitialSize
    if not literalOk:
      let sizeIR = sizeOperandOnce(parseExpr(n[1], preamble, ctx), n[1],
                                   preamble, ctx)
      let name = calleeSym.strVal
      preamble.add mkIf(@[
        mkBranch(mkBinop(bLt, sizeIR, mkIntLit(0)),
                 mkRaise("RangeDefect", nil)),
        mkBranch(mkBinop(bGt, sizeIR, mkIntLit(maxModelledInitialSize)),
                 ctx.declineAtSite(feUnsupportedOp,
                   "`" & name & "` with an initial size above " &
                   $maxModelledInitialSize & " is not modelled: the slot " &
                   "count overflows (OverflowDefect) or the store's " &
                   "allocation exhausts memory, depending on the value " &
                   "and the host -- path degraded to sxUnknown",
                   name & ": initial size above " &
                   $maxModelledInitialSize))])
  zeroValueForType(cls.ty)

proc parseNewSeqLen(lenNode: NimNode; name: string;
                    preamble: var seq[IRStmt]; ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bc (item 5). `newSeq`'s length, guarded as Nim guards it:
  ## the parameter is `Natural`, so a negative length raises `RangeDefect`
  ## at the call (the typed argument's hidden conversion, stripped here and
  ## checked explicitly, as `parseInitContainer` does its size). A length
  ## above `maxModelledInitialSize` allocates that many elements: an
  ## `OutOfMemDefect`, or not, depending on the host -- that path is
  ## declined, scoped to it. A literal in range needs no guard.
  var lit = lenNode
  while lit.kind == nnkHiddenStdConv and lit.len >= 1:
    lit = lit[lit.len - 1]
  if lit.kind in nnkCharLit..nnkUInt64Lit and lit.intVal >= 0 and
     lit.intVal <= maxModelledInitialSize:
    return mkIntLit(lit.intVal)
  let lenIR = sizeOperandOnce(parseAtomicOperand(lit, preamble, ctx), lit,
                              preamble, ctx)
  preamble.add mkIf(@[
    mkBranch(mkBinop(bLt, lenIR, mkIntLit(0)), mkRaise("RangeDefect", nil)),
    mkBranch(mkBinop(bGt, lenIR, mkIntLit(maxModelledInitialSize)),
             ctx.declineAtSite(feUnsupportedOp,
               "`" & name & "` with a length above " &
               $maxModelledInitialSize & " is not modelled: allocating it " &
               "raises OutOfMemDefect or not, depending on the host -- " &
               "path degraded to sxUnknown",
               name & ": length above " & $maxModelledInitialSize))])
  lenIR

proc parseGetOrDefault(n, calleeSym: NimNode; preamble: var seq[IRStmt];
                       ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bc. The stdlib's `getOrDefault(t, key)` /
  ## `getOrDefault(t, key, default)` on a modelled `Table`: the value at
  ## `key` when the table has it, else `default` (or `default(V)`, the
  ## value an uninitialised `var v: V` gets). `nil` for any other call, and
  ## for a value type with no zero (it then walks the stdlib body, as
  ## before). Lowered as
  ##
  ##   if contains(t, key): let r = t[key]   (`isIndex`: never raises here)
  ##   else:                let r = default
  ##
  ## Nim evaluates `t`, `key` and `default` before the lookup, so the key
  ## and the default are bound first (`parseAtomicOperand`). Presence is
  ## `contains`, i.e. `hasKey`, which is exactly the stdlib's own
  ## `rawGet(...) >= 0` test: a NaN float key is never present, so its
  ## lookup is the default (`tabKeyNaN`, S8at). The stdlib body was walked
  ## before; its `hashes.Hash` locals classify as no modelled type, so every
  ## call declined, and under `and` it was a walker fault.
  if calleeSym.kind != nnkSym or calleeSym.strVal != "getOrDefault" or
     not isStdlibDecl(calleeSym) or n.len notin [3, 4]:
    return nil
  let recvCls = classifyType(n[1])
  if recvCls.ty.kind != itTable: return nil
  let valTy = recvCls.ty.tabValTy
  let zero = if n.len == 3: zeroValueForType(valTy) else: nil
  if n.len == 3 and zero == nil: return nil
  let recvIR = liftIndexContainer(parseExpr(n[1], preamble, ctx),
                                  recvCls.ty, preamble, ctx)
  let keyIR = parseAtomicOperand(n[2], preamble, ctx)
  let defIR = if n.len == 4: parseAtomicOperand(n[3], preamble, ctx)
              else: zero
  let synth = freshSynth(ctx, "tgod")
  preamble.add mkIf(
    @[mkBranch(mkContains(recvIR, keyIR),
               mkIndexStmt(synth, recvIR, keyIR, valTy))],
    mkLet(synth, valTy, defIR))
  mkVar(synth)

proc mgetOrPutCall(n: NimNode): NimNode =
  ## RFC-0005 S8bc (item 7). The stdlib's `mgetOrPut(t, key, default)` /
  ## `mgetOrPut(t, key)` call on a modelled `Table` under `n`'s hidden
  ## wrappers (its `var B` result reaches every use as an `nnkHiddenDeref`),
  ## or nil. Its key must be a literal or a plain variable: the cell is
  ## addressed more than once (the presence test, the insert, the read and
  ## a mutation's write back, all as `t[key]`), so evaluating the key twice
  ## must be evaluating it once -- the S8at element arms' own gate
  ## (`arrayElemLvalue`). Any other key keeps the stdlib body walk (a
  ## decline, as before).
  let c = unwrapHidden(n)
  if c.kind notin {nnkCall, nnkCommand} or c.len notin [3, 4] or
     c[0].kind != nnkSym or c[0].strVal != "mgetOrPut" or
     not isStdlibDecl(c[0]):
    return nil
  if classifyType(unwrapHidden(c[1])).ty.kind != itTable: return nil
  if unwrapHidden(c[2]).kind notin {nnkSym, nnkCharLit .. nnkUInt64Lit,
                                    nnkFloatLit .. nnkFloat64Lit,
                                    nnkStrLit .. nnkTripleStrLit}:
    return nil
  c

proc parseMGetOrPut(n: NimNode; preamble: var seq[IRStmt];
                    ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bc (item 7). `mgetOrPut(t, key, default)` read as a value:
  ## the get-or-insert. Lowered as
  ##
  ##   let d = default                       (Nim evaluates it eagerly)
  ##   if contains(t, key): discard  else: t[key] = d
  ##   let r = t[key]                        (`isIndex`: present here)
  ##
  ## The returned value is the cell's value at the call. The REFERENCE
  ## `mgetOrPut` returns is modelled by its writers, not here: a mutation
  ## through it (`t.mgetOrPut(k, @[]).add v`, `+= v`, `inc`, `= v`) reaches
  ## the S8at element arms as the lvalue `t[key]` (`elemLvalueBracket`),
  ## which read this value and write the result back to `t[key]` -- the
  ## same cell the reference denotes, since nothing between the call and
  ## the write can move it. The stdlib body was walked before: its
  ## `hashes.Hash` locals classify as no modelled type (a decline), and the
  ## `+=` / `inc` forms on its result declined or, for `inc`, dropped the
  ## write (see the `inc`/`dec` arm).
  let c = mgetOrPutCall(n)
  if c == nil: return nil
  let recvCls = classifyType(unwrapHidden(c[1]))
  let valTy = recvCls.ty.tabValTy
  let zero = if c.len == 3: zeroValueForType(valTy) else: nil
  if c.len == 3 and zero == nil: return nil
  let defIR = if c.len == 4: parseAtomicOperand(c[3], preamble, ctx)
              else: zero
  let keyIR = parseExpr(c[2], preamble, ctx)
  let recvIR = liftIndexContainer(parseExpr(c[1], preamble, ctx),
                                  recvCls.ty, preamble, ctx)
  var ins: seq[IRStmt]
  let store = parseAsgn(nnkAsgn.newTree(nnkBracketExpr.newTree(c[1], c[2]),
                                        newEmptyNode()),
                        defIR, ins, ctx)
  ins.add store
  preamble.add mkIf(@[mkBranch(mkContains(recvIR, keyIR), mkBlock(@[]))],
                    mkBlock(ins))
  # The receiver is read again AFTER the insert: `liftIndexContainer` may
  # have bound a field receiver to a temp, which the insert does not update.
  let recvAfter = liftIndexContainer(parseExpr(c[1], preamble, ctx),
                                     recvCls.ty, preamble, ctx)
  let synth = freshSynth(ctx, "mgop")
  preamble.add mkIndexStmt(synth, recvAfter, keyIR, valTy)
  mkVar(synth)

proc simpleRefExpr(e: NimNode): bool =
  ## RFC-0005 S8bh. `e` reads a ref with no effect and no index: a
  ## variable, or a field of one (through dereferences).
  case e.kind
  of nnkSym: true
  of nnkDotExpr: e.len == 2 and simpleRefExpr(e[0])
  of nnkHiddenDeref, nnkDerefExpr, nnkHiddenStdConv, nnkHiddenSubConv:
    e.len >= 1 and simpleRefExpr(e[^1])
  else: false

proc closureCallIR(n0, calleeSym: NimNode; calleeName: string;
                   preamble: var seq[IRStmt]; ctx: ParseCtx;
                   ordered = false):
                   tuple[e: IRExpr, hoisted: bool] =
  ## RFC-0005 S8bh. The `iekClosureCall` of `n`, a call through the proc
  ## value `calleeSym`. Before S8bh its arguments were lowered by value and
  ## nothing carried a `var` formal's writes back: `let f = setBoth; f(x,
  ## y)` left `x` and `y` as they were (a false `sxSat`), whether `f` was a
  ## proc used as a value, a lambda, a generic callee's proc parameter or a
  ## proc passed to a callee; and an `addr` actual declined
  ## (`feUnsupportedExprKind`). A call with a `var` formal or an `addr`
  ## actual is now applied as a direct call is (`userCallStmt`):
  ##   * a `var` actual that is a variable is written by the walker after
  ##     the call (`ccVarTys`: the formal's exit value, by name, as #140);
  ##   * any other lvalue (a field, an element, a heap cell) is copied into
  ##     a temporary the walker writes, and the temporary is written back
  ##     to the lvalue when the call returns or raises (S8ac's shape);
  ##   * an `addr lv` actual is a cell for the call (S8an's shape), one per
  ##     lvalue;
  ##   * one location passed twice (`f(x, x)`) runs the body specialised to
  ##     it (`ccAlias`, `lambdaAliasBodies`), and two heap lvalues that are
  ##     one cell exactly when their refs are equal (`f(p.x, q.x)`, S8bf's
  ##     peers) branch on that equality: the specialised body when they
  ##     are, the plain one when not. Two `addr` peers share their cell
  ##     when the refs are equal.
  ## The call is hoisted to a statement (`let <synth> = <call>`), so its
  ## writes land before the rest of the expression reads them, and the
  ## result is that temporary (`hoisted`). What the body can reach on its
  ## own is known only once the callee is (`lowerClosureCall`), which
  ## declines a call whose locations it can also reach (`ccTouch`). A shape
  ## this does not model declines here (`feUnsupportedOp`).
  ##
  ## RFC-0005 batch 4: `ordered` lowers a call with no `var` formal and no
  ## `addr` actual through S8ax's `parseOrderedArgs`, as the sites that
  ## ordered their arguments before S8bh did (a proc-valued variable in
  ## expression position, S8be's call through a proc-valued expression).
  ##
  ## RFC-0005 S8bu: a `var openArray` actual as `userCallStmt` passes one:
  ## a whole seq's view is the seq (`varSeqViews`), an array's or a slice's
  ## a temporary written back over the elements it views.
  let n = varSeqViews(n0)
  let ti = calleeSym.getTypeInst
  var varTys: seq[IRType]
  var anyVar = false
  var retVoid = true
  if ti.kind == nnkProcTy and ti.len > 0 and ti[0].kind == nnkFormalParams:
    let fp = ti[0]
    retVoid = fp[0].kind == nnkEmpty or
              (fp[0].kind == nnkSym and macros.strVal(fp[0]) == "void")
    for i in 1 ..< fp.len:
      let id = fp[i]
      if id.kind != nnkIdentDefs: continue
      let isVar = id[^2].kind == nnkVarTy
      for j in 0 ..< id.len - 2:
        varTys.add(if isVar: classifyType(id[^2]).ty else: nil)
        if isVar: anyVar = true
  var anyAddr = false
  for i in 1 ..< n.len:
    if addrActualLvalue(n[i]) != nil: anyAddr = true
  # RFC-0005 S8bu: where each argument the walk passes as a value came from,
  # when it is a path into a routine's variable Nim passes by address or
  # shares (`ccVarLocs`, as `userCallStmt`'s `cVarLocs`): the walker binds
  # the formal to the variable's cell when it has one (`bindVarLocs`).
  var locs: seq[VarLoc]
  if not anyVar and not anyAddr:
    var argIRs: seq[IRExpr]
    if ordered:
      argIRs = parseOrderedArgs(n, 1, preamble, ctx)
    else:
      for i in 1 ..< n.len:
        argIRs.add parseExpr(n[i], preamble, ctx)
    # The index of a path is read without side effects (`stableIndex`), so
    # reading it after the arguments reads the value the argument used.
    for i in 1 ..< n.len:
      byValueLoc(n[i], i - 1, preamble, ctx, locs)
    return (e: mkClosureCall(calleeName, argIRs, locs = locs), hoisted: false)
  let nArgs = n.len - 1
  proc isVarFormal(k: int): bool = k < varTys.len and varTys[k] != nil
  proc declineHere(msg: string): IRStmt =
    ctx.declineAtSite(feUnsupportedOp,
      siteMsg(n, "call through `" & calleeName & "`: " & msg &
              " (feUnsupportedOp, RFC-0005 S8bh)"),
      "closure call var/addr effect not modelled (feUnsupportedOp)")
  # The location each `var`/`addr` actual hands the callee.
  var lvOf = newSeq[NimNode](nArgs + 1)
  for i in 1 ..< n.len:
    let a = addrActualLvalue(n[i])
    if a != nil:
      lvOf[i] = a
    elif isVarFormal(i - 1) and varViewSource(n[i]) == nil:
      if n[i].kind == nnkHiddenAddr and n[i].len == 1:
        var lv = n[i][0]
        if isVarIndirection(lv): lv = lv[0]
        lvOf[i] = lv
      elif n[i].kind == nnkSym:
        lvOf[i] = n[i]   ## a `var` formal passed on (Nim drops the addr)
  # S8bf's peers: two heap lvalues that may be one cell through different
  # refs. Two `addr`s, or two `var`s, of one lvalue are one location
  # already (`same`), not a pair.
  var same = newSeq[int](nArgs + 1)
  for i in 1 ..< n.len: same[i] = i
  var peers = newSeq[seq[int]](nArgs + 1)
  for i in 1 ..< n.len:
    if lvOf[i].isNil: continue
    for j in 1 ..< i:
      if lvOf[j].isNil: continue
      if (addrActualLvalue(n[i]) != nil) != (addrActualLvalue(n[j]) != nil):
        continue
      if scopedRepr(lvOf[i]) == scopedRepr(lvOf[j]):
        if same[i] == i: same[i] = same[j]
  for i in 1 ..< n.len:
    if lvOf[i].isNil or same[i] != i: continue
    for j in 1 ..< n.len:
      if j == i or lvOf[j].isNil or same[j] != j: continue
      if lvOf[i].kind != nnkSym and lvOf[j].kind != nnkSym and
         heapCellsMayMeet(lvOf[i], lvOf[j]):
        peers[i].add j
  var argIRs: seq[IRExpr]
  var alias = newSeq[int](nArgs)
  for k in 0 ..< nArgs:
    # Two `addr`s of one lvalue are one cell already: no specialisation.
    alias[k] = (if addrActualLvalue(n[k + 1]) != nil: k else: same[k + 1] - 1)
  var addrArgs: seq[int]
  var touch: seq[string]
  var declines: seq[IRStmt]
  # RFC-0005 batch 4: S8ax's computed-index pairs (`aliasPath`): two
  # lvalues of one variable that are one location only when their indices
  # are equal. The checks below count them as two; the call is guarded on
  # the pairs below, as `userCallStmt`'s is.
  var aliasConds: seq[AliasIndexPairs]
  var temps = newSeq[string](nArgs + 1)     ## the walker-written location
  var backs: seq[tuple[i: int, lv: NimNode]]   ## lvalue write-backs
  var cellBacks: seq[IRStmt]
  var cellOfArg = newSeq[string](nArgs + 1)
  proc addTouch(lv: NimNode; heapSteps: seq[NimNode]) =
    var syms: seq[NimNode]
    lvalueVarSyms(lv, syms)
    for s in syms:
      let nm = "n:" & s.strVal
      if nm notin touch: touch.add nm
    for d in heapSteps:
      let k = if derefIsPtr(d) or objectInherits(d.getTypeInst): "t:?"
              else: cellTypeKey(d.getTypeInst)
      if k notin touch: touch.add k
  # RFC-0005 batch 5 (S8bk): where each argument's statements start, its
  # type, whether it is passed by address, and where a by-address lvalue
  # was lowered (`orderOperands`, `placeLateAddr`), as `userCallStmt` keeps.
  var argMarks: seq[int]
  var argTys: seq[IRType]
  var argFixed: seq[bool]
  var argLate = newSeq[LateAddr](nArgs)
  for i in 1 ..< n.len:
    let k = i - 1
    let lv = lvOf[i]
    argMarks.add preamble.len
    argTys.add(if n[i].typeKind != ntyNone: classifyType(n[i]).ty else: nil)
    argFixed.add(not lv.isNil)
    let view = varViewSource(n[i])
    if view != nil:
      # RFC-0005 S8bu: a `var openArray` view of an array or a slice.
      var lo: IRExpr = nil
      let t = viewTemp(view, n[i], preamble, ctx, lo)
      var vlv = viewStorage(view)
      if isVarIndirection(vlv): vlv = vlv[0]
      var heapSteps: seq[NimNode]
      let root = if vlv.kind == nnkSym: vlv else: lvalueRoot(vlv, heapSteps)
      addTouch(vlv, heapSteps)
      if root.isNil or
         varActualMayAlias(n, i, vlv, root, heapSteps, aliasConds, peers[i]):
        declines.add declineHere("`var openArray` argument `" & view.repr &
          "` views a location the callee may reach another way (or it has " &
          "no root variable)")
      var vl: seq[VarLoc]
      varLocOf(vlv, t, "var", preamble, ctx, vl)
      for l in vl:
        locs.add (temp: l.temp, root: l.root, path: @["?"], mode: l.mode)
      cellBacks.add viewWriteBack(view, n[i], t, lo, ctx)
      argIRs.add mkVar(t)
      continue
    if lv.isNil:
      argIRs.add parseExpr(n[i], preamble, ctx)
      byValueLoc(n[i], k, preamble, ctx, locs)   ## RFC-0005 S8bu
      continue
    if lv.kind != nnkSym and lvalueCastBlocks(lv):
      # RFC-0005 batch 5 (S8bg on S8bh's path): a `var` / `addr` actual
      # reached through a `cast` declines naming the cast, as a direct
      # call's does. Read as an expression, the declined cast's dummy
      # value reached `lowerLeafInExpr` (a `weInternalWalkerFault`).
      declines.add declineHere("`" & lv.repr & "` is reached through a " &
        "`cast`, which may reinterpret the memory at that address: the " &
        "callee's writes through it are not modelled")
      let dummy = zeroValueForType(classifyType(lv).ty)
      argIRs.add(if dummy != nil: dummy else: mkIntLit(0))
      continue
    let viaAddr = addrActualLvalue(n[i]) != nil
    var heapSteps: seq[NimNode]
    let root = lvalueRoot(lv, heapSteps)
    addTouch(lv, heapSteps)
    var skip = peers[i]
    for j in 1 ..< n.len:
      if j != i and same[j] == same[i]: skip.add j
    if same[i] != i:
      # The same location as an earlier actual: the same cell / variable.
      if viaAddr:
        argIRs.add mkVar(cellOfArg[same[i]])
        addrArgs.add k
      elif temps[same[i]].len > 0:
        argIRs.add mkVar(temps[same[i]])
      else:
        argIRs.add parseExpr(n[i], preamble, ctx)
      continue
    if root.isNil:
      declines.add declineHere("`" & lv.repr & "` has no root variable")
    elif viaAddr:
      if addrActualMayAlias(n, i, lv, root, heapSteps, aliasConds, skip):
        declines.add declineHere("`addr " & lv.repr & "` is passed alongside " &
          "another argument that reaches the same location")
    elif varActualMayAlias(n, i, lv, root, heapSteps, aliasConds, skip):
      declines.add declineHere("`var` argument `" & lv.repr & "` is also " &
        "reached through another argument")
    if viaAddr:
      let cell = freshSynth(ctx, "addrCell")
      cellOfArg[i] = cell
      let ptrTy = classifyType(n[i]).ty
      let elemTy = classifyType(lv).ty
      varLocOf(lv, cell, "addr", preamble, ctx, locs)   ## RFC-0005 S8bu
      let lvLo = preamble.len
      let lvIR = parseExpr(lv, preamble, ctx)
      let lvHi = preamble.len
      preamble.add mkNewT(cell, ptrTy)
      preamble.add mkDerefWrite(mkVar(cell), lvIR, elemTy, ptrFamily = true,
                                cell = true)
      argLate[k] = LateAddr(ok: true, lo: lvLo, hi: lvHi, bindEnd: preamble.len,
                            growable: lvalueIndexGrowable(lv))
      let back = freshSynth(ctx, "addrBack")
      var wbPre = @[mkPtrDeref(back, mkVar(cell), elemTy, cell = true)]
      let w = parseAsgn(nnkAsgn.newTree(lv, newEmptyNode()), mkVar(back),
                        wbPre, ctx)
      cellBacks.add mkBlock(wbPre & @[w])
      argIRs.add mkVar(cell)
      addrArgs.add k
      continue
    let irLo = preamble.len
    var ir = parseExpr(n[i], preamble, ctx)
    let irHi = preamble.len
    if lv.kind == nnkSym:
      if ir.kind != iekVar:
        declines.add declineHere("`var` argument `" & lv.repr & "` names no " &
          "variable the walk can write")
      argIRs.add ir
      continue
    let t = freshSynth(ctx, "varArg")
    preamble.add mkLet(t, classifyType(lv).ty, ir)
    # RFC-0005 batch 5 (S8bk): copied in at the call, through the address
    # the write-back writes.
    argLate[k] = LateAddr(ok: true, lo: irLo, hi: irHi, bindEnd: preamble.len,
                          growable: lvalueIndexGrowable(lv))
    temps[i] = t
    varLocOf(lv, t, "var", preamble, ctx, locs)   ## RFC-0005 S8bu
    backs.add (i: i, lv: lv)
    argIRs.add mkVar(t)
  # RFC-0005 batch 5 (S8bk on S8bh's path): Nim takes a `var` / `addr`
  # actual's address at the call, after every later argument -- `let f =
  # touch; f(gP.x, moveP())` writes the object `moveP` installed, as
  # `touch(gP.x, moveP())` does -- and reads a by-value argument where
  # S8ax's order puts it. The lvalues read late (`placeLateAddr`); before,
  # the copy-in read the old object and the write-back wrote the new.
  orderOperands(preamble, argMarks, argIRs, argTys, omOperands, ctx,
                argFixed, argLate)
  # The peer pairs: each argument at most one, mutual, both `var` or both
  # `addr`, through refs read without effect, along one field path.
  var pair: tuple[a, b: int] = (0, 0)
  var pairOk = true
  for i in 1 ..< n.len:
    if peers[i].len == 0: continue
    if peers[i].len > 1:
      pairOk = false
      continue
    let j = peers[i][0]
    if i < j:
      if pair.a != 0: pairOk = false
      else: pair = (i, j)
  var eqCond: IRExpr = nil
  if pair.a != 0 and pairOk:
    let ta = heapCellTail(lvOf[pair.a])
    let tb = heapCellTail(lvOf[pair.b])
    var pathOk = ta.path == tb.path and "[]" notin ta.path
    if ta.deref.isNil or tb.deref.isNil or derefIsPtr(ta.deref) or
       derefIsPtr(tb.deref) or not simpleRefExpr(ta.deref[0]) or
       not simpleRefExpr(tb.deref[0]) or
       not sameType(ta.deref.getTypeInst, tb.deref.getTypeInst):
      pathOk = false
    if pathOk:
      eqCond = mkBinop(bEq, parseExpr(ta.deref[0], preamble, ctx),
                       parseExpr(tb.deref[0], preamble, ctx))
    else:
      pairOk = false
  if not pairOk:
    declines.add declineHere("two or more of its `var`/`addr` arguments may " &
      "be one heap cell through different refs, in a shape not modelled " &
      "(more than a pair, a `ptr` dereference, an index, an effectful ref " &
      "or different field paths)")
  let retTy = if retVoid: tBool() else: classifyType(n).ty
  let synth = freshSynth(ctx, "closureCall")
  # RFC-0005 S8bn (item 3): what each `var` actual's location is to a
  # pointer of unknown origin (`varActualPtrSafety`).
  var varSafe = newSeq[int](nArgs)
  for i in 1 ..< n.len:
    if isVarFormal(i - 1) and not lvOf[i].isNil and
       addrActualLvalue(n[i]) == nil:
      varSafe[i - 1] = varActualPtrSafety(lvOf[i])
  proc callWith(al: seq[int]; touchV: seq[string]): IRExpr =
    var aliasV = al
    var identity = true
    for k, a in aliasV:
      if a != k: identity = false
    if identity: aliasV = @[]
    mkClosureCall(calleeName, argIRs, varTys, aliasV, addrArgs, touchV, locs,
                  varSafe)
  proc wrap(call: IRExpr; wbs: seq[IRStmt]): IRStmt =
    let l = mkLet(synth, retTy, call)
    if wbs.len == 0: l else: mkTry(l, @[], mkBlock(wbs))
  proc backsFor(al: seq[int]): seq[IRStmt] =
    for b in backs:
      # RFC-0005 S8bh, after S8x: a `var` copy, not a `let`. In the
      # compile-time VM a `let` of a seq element aliases the element
      # (`vm_alias_guard`).
      var src = temps[al[b.i - 1] + 1]
      var wbPre: seq[IRStmt]
      let w = parseAsgn(nnkAsgn.newTree(b.lv, newEmptyNode()), mkVar(src),
                        wbPre, ctx)
      result.add(if wbPre.len == 0: w else: mkBlock(wbPre & @[w]))
    for c in cellBacks: result.add c
  for d in declines: preamble.add d
  # RFC-0005 batch 4: the computed-index pairs (`aliasConds`). The indices
  # are free of side effects (`stableIndex`), so reading them again here is
  # reading the values the arguments used.
  for pairs in aliasConds:
    var cond: IRExpr = nil
    for pr in pairs:
      let eq = mkBinop(bEq, parseExpr(pr.a, preamble, ctx),
                       parseExpr(pr.b, preamble, ctx))
      cond = if cond == nil: eq else: mkBinop(bAnd, cond, eq)
    preamble.add mkIf(@[IRBranch(cond: cond,
      body: declineHere("two of its `var`/`addr` arguments are one " &
        "location when their indices are equal, which this path allows"))])
  if eqCond != nil and addrActualLvalue(n[pair.a]) != nil:
    # Two `addr` peers: one cell when the refs are equal.
    preamble.add mkIf(@[IRBranch(cond: eqCond,
      body: mkAssign(cellOfArg[pair.b], mkVar(cellOfArg[pair.a])))])
    preamble.add wrap(callWith(alias, touch), backsFor(alias))
  elif eqCond != nil:
    # Two `var` peers: the body specialised to one location when the refs
    # are equal.
    var al2 = alias
    al2[pair.b - 1] = pair.a - 1
    preamble.add mkIf(@[IRBranch(cond: eqCond,
                                 body: wrap(callWith(al2, touch), backsFor(al2)))],
                      wrap(callWith(alias, touch), backsFor(alias)))
  else:
    preamble.add wrap(callWith(alias, touch), backsFor(alias))
  (e: mkVar(synth), hoisted: true)

const seqNewBuiltins = ["newSeq", "newSeqOfCap", "newSeqUninit"]
  ## RFC-0005 S8bi. The seq constructors `parseSeqNew` models.

proc parseSeqNew(op: string; argNode: NimNode; seqTy: IRType;
                 preamble: var seq[IRStmt]; ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bi. `newSeq[T](n)`, `newSeqOfCap[T](n)`, `newSeqUninit[T](n)`
  ## (and the statement `newSeq(s, n)`, as `s = newSeq[T](n)`). Before S8bi
  ## the call fell through to `ensureProcRegistered`, whose parameter walk
  ## of the generic magic aborted the compile ("node has no type").
  ##
  ## RFC-0005 batch 5: one lowering with S8bc's `newSeq` (item 5). Each
  ## takes `n: Natural`, guarded by `parseNewSeqLen` exactly as S8bc's was:
  ## a negative `n` raises `RangeDefect` at the call, and one above
  ## `maxModelledInitialSize` declines, scoped to its path -- allocating
  ## (or reserving) that many elements raises `OutOfMemDefect` or not,
  ## depending on the host, so it is never modelled as succeeding.
  mkSeqNew(parseNewSeqLen(argNode, op, preamble, ctx), seqTy.seqElemTy,
           zeroed = op != "newSeqUninit", ofCap = op == "newSeqOfCap")

proc parseRegexCtor(c: NimNode; preamble: var seq[IRStmt];
                    ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bq (item 3). A `std/re` constructor call outside a regex
  ## call (`regexCtorCall`): `let r = re"(ab"`, `discard rex(p)`. Nim runs
  ## PCRE's compile there, which raises `RegexError` for a pattern it
  ## rejects; otherwise the value is a new `Regex` (a fresh, non-nil ref:
  ## its fields are not exported, so its identity is all a caller sees).
  ## A literal the reader leaves undecided, and a pattern that is not a
  ## literal, decline (`seUnsupportedRegex`, scoped), as they do inside a
  ## regex call. Before S8bq the literal form was `feUnsupportedExprKind`
  ## (`nnkCallStrLit`) and the call form aborted the compile ("node has
  ## no type", from `ensureProcRegistered`'s walk of `re`).
  let (flag, pat) = regexLiteralOf(c)
  ctx.userExnHierarchy["RegexError"] = "ValueError"
  let status = if flag == "?": psUnknown
               else: parsePcre(pat, flag == "rex").status
  case status
  of psRejected:
    preamble.add mkRaise("RegexError", nil)
  of psOk, psUnmodelled:
    discard
  of psUnknown:
    preamble.add ctx.declineAtSite(seUnsupportedRegex,
      "`" & c.repr & "`: whether PCRE accepts the pattern is not decided " &
        "(seUnsupportedRegex: the pattern is not a literal the reader " &
        "decides)",
      "regex constructor: pattern acceptance not decided " &
        "(seUnsupportedRegex)")
  let tmp = freshSynth(ctx, "regex")
  preamble.add mkNewT(tmp, classifyType(c).ty)
  mkVar(tmp)

proc peelConstConv(n: NimNode): NimNode =
  ## RFC-0005 S8bi. Strip the compiler's implicit conversions (`HiddenStdConv`
  ## with an empty type slot) around a value.
  result = n
  while result.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and
        result.len == 2 and result[0].kind == nnkEmpty:
    result = result[1]

proc isConstSetElem(n: NimNode): bool =
  ## RFC-0005 S8bi. An ordinal constant a set literal may hold: an int /
  ## char literal, an enum field (incl. `true` / `false`), or a range of two.
  let e = peelConstConv(n)
  case e.kind
  of nnkCharLit .. nnkUInt64Lit: true
  of nnkSym: e.symKind == nskEnumField
  of nnkRange:
    e.len == 2 and isConstSetElem(e[0]) and isConstSetElem(e[1])
  else: false

proc parseSetLitMember(setNode, keyNode: NimNode; preamble: var seq[IRStmt];
                       ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bi. `contains(<set literal>, k)`, the typed form of `k in
  ## {..}` (and, under `not`, of `k notin {..}`), as the disjunction of
  ## `k == e` per element and `k >= e1 and k <= e2` per range; the empty set
  ## is `false`. Nil when `setNode` is not a literal of constants, which
  ## leaves the call to the paths below (a set-typed VALUE is not modelled).
  ## The key's conversion to the set's base range is peeled, not checked:
  ## membership never raises (probe: `70000 in {1, 3}` and `-1 in {1, 3}`
  ## are false). Before S8bi the literal was `feUnsupportedExprKind`
  ## (`nnkCurly`).
  ##
  ## RFC-0005 S8bq (item 5): an element need not be a constant. Nim then
  ## evaluates the key, then every element left to right, each converted to
  ## the base type and range-checked, with no short circuit (probes:
  ## `k() in {e(), 3}` runs `k` first; `3 in {3, b}` with `b = 70000`
  ## raises `RangeDefect`), and the key still unchecked. So the key is read
  ## first, and each element is bound in order (`parseAtomicOperand`) with
  ## its conversion. Before S8bq such a literal declined
  ## (`feUnsupportedExprKind`).
  var lit = setNode
  while lit.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtListExpr} and
        lit.len >= 1:
    lit = lit[lit.len - 1]
  if lit.kind != nnkCurly: return nil
  var allConst = true
  for el in lit:
    if not isConstSetElem(el): allConst = false
  var key = parseExpr(peelConstConv(keyNode), preamble, ctx)
  if not ctx.inGuardCond and not isAtomicIR(key) and
     keyNode.typeKind != ntyNone:
    # Read once: every disjunct compares the same value.
    let tmp = freshSynth(ctx, "setKey")
    preamble.add mkLet(tmp, classifyType(peelConstConv(keyNode)).ty, key)
    key = mkVar(tmp)
  result = mkBoolLit(false)
  var first = true
  template addTerm(t: IRExpr) =
    result = if first: t else: mkBinop(bOr, result, t)
    first = false
  if not allConst:
    # RFC-0005 S8bq (item 5): every element, in order, with its conversion.
    var terms: seq[IRExpr]
    for el in lit:
      var e = el
      while e.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and e.len == 2 and
            e[0].kind == nnkEmpty and e[1].kind == nnkRange:
        e = e[1]
      if e.kind == nnkRange and e.len == 2:
        let lo = parseAtomicOperand(e[0], preamble, ctx)
        let hi = parseAtomicOperand(e[1], preamble, ctx)
        terms.add mkBinop(bAnd, mkBinop(bGe, key, lo), mkBinop(bLe, key, hi))
      else:
        terms.add mkBinop(bEq, key, parseAtomicOperand(el, preamble, ctx))
    for t in terms: addTerm t
    return
  for el in lit:
    let e = peelConstConv(el)
    if e.kind == nnkRange and key.kind == iekStrAt and
       peelConstConv(e[0]).kind in nnkCharLit .. nnkUInt64Lit and
       peelConstConv(e[1]).kind in nnkCharLit .. nnkUInt64Lit:
      # A byte read `s[i]` stays inline (CR-17(a)), which declines an
      # ordering comparison on it: a range of bytes (at most 256) is its
      # members' equalities instead.
      for code in peelConstConv(e[0]).intVal .. peelConstConv(e[1]).intVal:
        addTerm mkBinop(bEq, key, mkIntLit(code))
      continue
    let term =
      if e.kind == nnkRange:
        mkBinop(bAnd,
          mkBinop(bGe, key, parseExpr(peelConstConv(e[0]), preamble, ctx)),
          mkBinop(bLe, key, parseExpr(peelConstConv(e[1]), preamble, ctx)))
      else:
        mkBinop(bEq, key, parseExpr(e, preamble, ctx))
    addTerm term

proc methodDispatchStmt(n, calleeSym: NimNode; retName: string;
                        retTy: IRType; preamble: var seq[IRStmt];
                        ctx: ParseCtx): IRStmt
  ## RFC-0005 S8bn fwd decl

var procFieldAssigns {.compileTime.}: Table[string, seq[NimNode]]
  ## RFC-0005 S8bn (item 6). Per proc field of an object type (`pfKey`), the
  ## procs the entry's routines assign to it (`o.f = p`, `T(f: p)`), in
  ## first-seen order: a heap object's proc field holds one of them, or
  ## nil, or (an input's, a field assigned another kind of value) a proc no
  ## assignment names. Filled by `parseEntryImpl` (`scanProcFieldAssigns`)
  ## before the parse; read where a call through a heap proc field
  ## dispatches (`procFieldCallIR`).

proc pfObjKey(objNode: NimNode): string =
  ## RFC-0005 S8bn (item 6). The object type of `objNode` (a ref's
  ## pointee), as `procFieldAssigns` keys it.
  var o = objNode
  while o.kind in {nnkHiddenDeref, nnkDerefExpr} and o.len == 1: o = o[0]
  let ti = o.getTypeImpl
  if ti.kind in {nnkRefTy, nnkPtrTy} and ti.len == 1: return ti[0].repr
  o.getTypeInst.repr

proc pfProcSym(v: NimNode): NimNode =
  ## RFC-0005 S8bn (item 6). The proc a proc-valued expression names
  ## directly (through Nim's hidden conversions), or nil.
  var x = v
  while x.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv,
                   nnkHiddenCallConv} and x.len > 0:
    x = x[^1]
  if x.kind == nnkSym and x.symKind in procValueSymKinds: x else: nil

proc pfAdd(key: string; sym: NimNode) =
  for x in procFieldAssigns.getOrDefault(key):
    if x == sym: return
  procFieldAssigns.mgetOrPut(key, @[]).add sym

proc scanProcFieldAssigns*(fn: NimNode) =
  ## RFC-0005 S8bn (item 6). Fill `procFieldAssigns` from `fn` and every
  ## user routine it names, transitively.
  procFieldAssigns = initTable[string, seq[NimNode]]()
  var work: seq[NimNode]
  var seenR: seq[NimNode]
  if fn.kind == nnkSym: work.add fn
  proc scan(n: NimNode; work: var seq[NimNode]) =
    if n == nil: return
    case n.kind
    of nnkSym:
      if isUserRoutine(n) and n.getImpl.kind != nnkNilLit:
        work.add n
      return
    of nnkAsgn:
      if n.len == 2:
        var l = n[0]
        if l.kind == nnkCheckedFieldExpr and l.len >= 1: l = l[0]
        if l.kind == nnkDotExpr and l.len == 2 and l[1].kind == nnkSym and
           l.getTypeInst.kind == nnkProcTy:
          let ps = pfProcSym(n[1])
          if ps != nil: pfAdd(pfObjKey(l[0]) & "." & macros.strVal(l[1]), ps)
    of nnkObjConstr:
      for i in 1 ..< n.len:
        let c = n[i]
        if c.kind == nnkExprColonExpr and c.len == 2 and c[0].kind == nnkSym and
           c[1].kind != nnkNilLit and c[1].getTypeInst.kind == nnkProcTy:
          let ps = pfProcSym(c[1])
          if ps != nil: pfAdd(pfObjKey(n) & "." & macros.strVal(c[0]), ps)
    of nnkTypeSection, nnkTypeDef, nnkPragma, nnkCommentStmt:
      return
    else: discard
    for c in n: scan(c, work)
  var i = 0
  while i < work.len:
    let r = work[i]
    inc i
    var dup = false
    for x in seenR:
      if x == r: dup = true
    if dup: continue
    seenR.add r
    let impl = r.getImpl
    if impl.kind notin RoutineNodes or impl.len < 7: continue
    scan(impl[6], work)

proc pfCode(key: string; v: NimNode): int64 =
  ## RFC-0005 S8bn (item 6). The shadow code of a proc field's value `v`: 0
  ## for nil, the 1-based position of the proc it names in
  ## `procFieldAssigns[key]`, -1 for any other value (no candidate).
  if v.kind == nnkNilLit: return 0
  let ps = pfProcSym(v)
  if ps == nil: return -1
  let cs = procFieldAssigns.getOrDefault(key)
  for i, c in cs:
    if c == ps: return int64(i + 1)
  -1

proc isClosureFieldTy(t: IRType): bool =
  t != nil and t.kind == itUninterp and t.uninterpName == "__closure"

proc isProcFieldCall(n: NimNode): bool =
  ## RFC-0005 S8bn (item 6). `n` calls the proc stored in an object's field
  ## (`o.f(x)`: the callee is a field access of proc type).
  n.kind in {nnkCall, nnkCommand} and n.len >= 1 and
    n[0].kind in {nnkDotExpr, nnkCheckedFieldExpr} and
    n[0].getTypeInst.kind == nnkProcTy

proc procFieldCallIR(n: NimNode; preamble: var seq[IRStmt]; ctx: ParseCtx):
    tuple[e: IRExpr, hoisted: bool] =
  ## RFC-0005 S8bn (item 6). A call through a proc field is a call through a
  ## proc value: the field is read once, into a temporary, and the call
  ## takes S8bh's proc-value path (`closureCallIR`) through it, `var` /
  ## `addr` effects included. Nim reads the callee before the arguments.
  ## A field holding a proc the walk knows (a by-value object built with
  ## it) runs that proc's body; one it does not (an input, a heap field)
  ## has no target (`ceClosureUnknownCallee`, its effects havocked).
  ##
  ## A proc field of a heap object (`ref`/`ptr` object) is held as a shadow
  ## code (`@pf_<f>`, `pfCode`): each assignment and constructor stores the
  ## code of the proc it names, `new` stores 0 (nil). The call reads the
  ## code and dispatches over the procs the routines assign to the field
  ## (`procFieldAssigns`), each a walked call; any other code (nil, an
  ## input's proc, a value no assignment names) takes the proc-value path
  ## above, declined -- only on a path an execution takes (S8bc's
  ## infeasible-path drop at every decline).
  let dot = if n[0].kind == nnkCheckedFieldExpr: n[0][0] else: n[0]
  var operand = if dot.kind == nnkDotExpr: dot[0] else: nil
  if operand != nil and operand.kind in {nnkHiddenDeref, nnkDerefExpr} and
     operand.len == 1:
    operand = operand[0]
  let opTy = if operand != nil: classifyType(operand).ty else: nil
  if opTy != nil and opTy.kind in {itRef, itPtr}:
    let isPtr = opTy.kind == itPtr
    let pointee = if isPtr: opTy.ptrPointeeTy else: opTy.refPointeeTy
    if pointee != nil and pointee.kind == itTuple and dot[1].kind == nnkSym:
      let field = macros.strVal(dot[1])
      let key = pfObjKey(dot[0]) & "." & field
      let cands = procFieldAssigns.getOrDefault(key)
      let codeT = freshSynth(ctx, "procFieldCode")
      preamble.add mkFieldDeref(codeT, parseExpr(operand, preamble, ctx),
                                tInt(64, signed = true), pointee,
                                "@pf_" & field, isPtr)
      let pt = n[0].getTypeInst      # nnkProcTy[FormalParams[ret, ...], ...]
      let rt = if pt.len > 0 and pt[0].kind == nnkFormalParams: pt[0][0]
               else: newEmptyNode()
      let isVoid = rt.kind == nnkEmpty or
                   (rt.kind == nnkSym and macros.strVal(rt) == "void")
      let retTy = if isVoid: tBool() else: classifyType(n).ty
      let retName = if isVoid: "" else: freshSynth(ctx, "procFieldRet")
      var branches: seq[IRBranch]
      for i, c in cands:
        var call = newNimNode(nnkCall, n)
        call.add c
        for j in 1 ..< n.len: call.add n[j]
        let ck = ensureProcRegistered(ctx, c, call)
        var pre: seq[IRStmt]
        let st = userCallStmt(call, c, ck, retName, retTy, @[], pre, ctx)
        branches.add mkBranch(mkBinop(bEq, mkVar(codeT), mkIntLit(int64(i + 1))),
                              mkBlock(pre & @[st]))
      var other: seq[IRStmt]
      other.add ctx.declineMarker(feUnsupportedOp,
        siteMsg(n, "a call through the heap proc field `" & field & "` " &
                "holding a proc no assignment the walk sees names (an " &
                "input's, nil, or a computed value): no target to run " &
                "(RFC-0005 S8bn; feUnsupportedOp)"))
      let fv = freshSynth(ctx, "procField")
      other.add mkLet(fv, classifyType(n[0]).ty, parseExpr(n[0], other, ctx))
      let cc = closureCallIR(n, n[0], fv, other, ctx)
      if isVoid:
        if not cc.hoisted:
          other.add mkLet(freshSynth(ctx, "closureCallSink"), tBool(), cc.e)
      else:
        other.add mkLet(retName, retTy, cc.e)
      preamble.add(if branches.len == 0: mkBlock(other)
                   else: mkIf(branches, mkBlock(other)))
      if isVoid: return (mkBoolLit(true), true)
      return (mkVar(retName), false)
  let fv = freshSynth(ctx, "procField")
  preamble.add mkLet(fv, classifyType(n[0]).ty, parseExpr(n[0], preamble, ctx))
  closureCallIR(n, n[0], fv, preamble, ctx)

proc parseBitSetLit(n: NimNode; setTy: IRType; preamble: var seq[IRStmt];
                    ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bq (item 2, and item 5's non-constant elements). A set
  ## literal as a value of the builtin `set[T]` `setTy`: `bsoLit` of each
  ## element as a pair (`e, e`, one node) and each range as its bounds.
  ## Elements are evaluated left to right, each with its conversion to `T`,
  ## which range-checks it (probe: `{z, 1}` with `z = 70000` raises
  ## `RangeDefect`; `{lo..hi}` with `hi < lo` is empty).
  var args: seq[IRExpr]
  for el in n:
    var e = el
    while e.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and e.len == 2 and
          e[0].kind == nnkEmpty and e[1].kind == nnkRange:
      e = e[1]
    if e.kind == nnkRange and e.len == 2:
      let lo = parseAtomicOperand(e[0], preamble, ctx)
      let hi = parseAtomicOperand(e[1], preamble, ctx)
      args.add lo
      args.add hi
    else:
      let v = parseAtomicOperand(el, preamble, ctx)
      args.add v
      args.add v
  mkBitSet(bsoLit, args, setTy)

proc bitSetElemPure(n: NimNode): bool =
  ## RFC-0005 S8bq. `n` calls nothing: a literal, a symbol, a conversion, a
  ## field or an index of such. Evaluating it moves no location.
  case n.kind
  of nnkCharLit .. nnkUInt64Lit, nnkSym, nnkNilLit: true
  of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv, nnkDotExpr, nnkBracketExpr,
     nnkHiddenDeref, nnkDerefExpr, nnkCheckedFieldExpr, nnkPar:
    for c in n:
      if c.kind notin {nnkEmpty, nnkType} and c.kind != nnkSym and
         not bitSetElemPure(c):
        return false
    true
  else: false

proc bitSetLvalueStable(n: NimNode): bool =
  ## RFC-0005 S8bq. `regexCapturesLvalue`'s locations, an index under the
  ## compiler's conversion (`a[1]` on an `array[2, T]` converts `1`) too.
  case n.kind
  of nnkSym:
    symKind(n) in {nskVar, nskParam, nskTemp, nskForVar, nskResult}
  of nnkDotExpr:
    n.len == 2 and bitSetLvalueStable(n[0])
  of nnkHiddenDeref, nnkDerefExpr:
    n.len == 1 and bitSetLvalueStable(n[0])
  of nnkBracketExpr:
    let ix = peelConstConv(n[1])
    n.len == 2 and bitSetLvalueStable(n[0]) and
      (ix.kind in nnkCharLit..nnkUInt64Lit or
       (ix.kind == nnkSym and symKind(ix) in {nskVar, nskLet, nskParam,
                                              nskConst, nskForVar}))
  else: false

proc parseBitSetInclExcl(n: NimNode; preamble: var seq[IRStmt];
                         ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bq (item 2). The statement `incl(s, k)` / `excl(s, k)` on a
  ## builtin set: `s = incl(s, k)` through the assignment's lvalue arms. Nim
  ## takes `s`'s address, then evaluates `k` (converted to `T`, which
  ## range-checks it), then writes. The model reads `s`, evaluates `k` and
  ## writes `s` again, which is that location only if nothing between can
  ## move it: `s` a variable, or a location `bitSetLvalueStable` admits
  ## with an element that calls nothing. Any other shape declines, scoped.
  ## Before S8bq a builtin set never classified, so this was a decline.
  let lv = unwrapHidden(n[1])
  let setTy = classifyType(lv).ty
  let name = n[0].strVal
  if not (lv.kind == nnkSym or
          (bitSetLvalueStable(lv) and bitSetElemPure(n[2]))):
    return ctx.declineAtSite(feUnsupportedOp,
      "`" & name & "` on `" & lv.repr & "` with `" & n[2].repr & "`: the " &
        "element may move the location it writes (feUnsupportedOp)",
      name & " on a location its element may move (feUnsupportedOp)")
  let cur = parseAtomicOperand(lv, preamble, ctx)
  let k = parseAtomicOperand(n[2], preamble, ctx)
  let op = if name == "incl": bsoIncl else: bsoExcl
  parseAsgn(nnkAsgn.newTree(lv, newEmptyNode()),
            mkBitSet(op, @[cur, k], setTy), preamble, ctx)

proc parseRoutineCallExpr(n, calleeSym: NimNode, preamble: var seq[IRStmt],
                          ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8c. An expression-position call to a ROUTINE (not a builtin
  ## model): the opaque/foreign/transparent arms, a call through a
  ## proc-valued variable, else the A-normalised user-proc call. `n` is the
  ## call-shaped node -- `nnkCall`, or an `nnkInfix`/`nnkPrefix`/
  ## `nnkHiddenCallConv` whose head resolved to a user routine (all four put
  ## the callee at `n[0]` and its arguments at `n[1..]`). Split out of the
  ## `nnkCall` arm so the user-callee gates of all four arms reach the SAME
  ## routine-call handling, not a copy of it.
  let userCallee = isUserRoutine(calleeSym)
  # Opaque effectful proc (#137 + Phase 9 user extension via
  # `{.symexOpaque.}` pragma) — fresh-symbolic return, no body walk.
  #
  # Issue #163: `{.symexTransparent.}` routes here TOO, and deliberately
  # gets the conservative opaque treatment rather than the drop. Reaching
  # the expression arm means the call's result is being used, which
  # contradicts the pragma's void-and-observably-nothing promise — so the
  # promise is not honoured. Keeping the body unwalked is still right (that
  # is the half of `{.symexOpaque.}` an over-claimed pragma still earns);
  # only the deletion is withheld.
  let calleeName = calleeSym.strVal
  let opaModel = getStdlibModelFor(calleeName, itBool)
  # RFC-0005 S8b: a bodiless foreign (`importc`/`dynlib`/...) callee is an
  # opaque effect too -- see `isBodilessForeign` (it was walked as an EMPTY
  # body, a silent zero result).
  # RFC-0005 S8c: the `OpaqueEffectfulProcs` catalog is a list of stdlib
  # NAMES (`echo`, `send`, `open`, ...); a user routine that happens to share
  # one is walked, not blacked out. Only the pragma / foreign arms apply to it.
  if (opaModel.kind == smkOpaqueEffectful and not userCallee) or
     hasSymexOpaquePragma(calleeSym) or
     hasSymexTransparentPragma(calleeSym) or isBodilessForeign(calleeSym):
    # #163 review R10: the callee over-claimed `{.symexTransparent.}` on
    # the OTHER route from R7's (`isInertOpaqueCall` gate, statement
    # position, above) — its RESULT IS USED, here in expression position.
    # Emit a SPECIFIC parse-time degrade naming the callee and the real
    # broken promise, exactly R7's pattern: entirely a front-end
    # (`ctx.parseErrors`) classification, sitting alongside (not instead
    # of) the generic `feOpaqueCallUnmodelled` the resulting opaque-call
    # fallback also produces at walk time. Without this, the ONLY message
    # the caller sees is the generic opaque-call text, which literally
    # tells them to "mark it `{.symexTransparent.}`" — wrong advice for a
    # callee that already carries the pragma; the real problem is that the
    # promise is honoured only in STATEMENT position.
    if hasSymexTransparentPragma(calleeSym):
      # RFC-0005 S8 (§13.3, i3): an annotation violation, not a decline.
      ctx.annotationViolation(n, avResultUsed, calleeName,
        "call `" & calleeName & "` is tagged `{.symexTransparent.}` " &
        "but its result is used here; the pragma is honoured only " &
        "in statement position, so it is treated as opaque instead " &
        "of dropped")
    var argIRs = parseOrderedArgs(n, 1, preamble, ctx)   ## RFC-0005 S8ax
    let retCls = classifyType(n)
    let synth = freshSynth(ctx, calleeName)
    # #163 slice 4: stays `inert = false` (the `mkOpaqueCall` default) —
    # this arm binds a result (`synth`), so clause (a) of the inertness
    # predicate fails by construction; `isInertOpaqueCall` is a
    # statement-position-only check and is deliberately not consulted here.
    preamble.add mkOpaqueCall(calleeName, synth, argIRs, retCls.ty)
    return mkVar(synth)
  # Phase 15 Cluster C (C1, ADR-0009 D6). A call THROUGH a proc-valued
  # VARIABLE (a local/param of proc type), distinct from a normal named-proc
  # call. The discriminator: `calleeSym`'s `getImpl` is NOT a proc/func DEF
  # (a top-level proc resolves to `nnkProcDef`; a proc-valued variable's impl
  # is the `nnkIdentDefs` of its let/var/param binding) AND its instantiated
  # type is a proc type (`nnkProcTy`). Top-level procs-as-VALUES are C3; C1
  # handles only the proc-valued-variable CALL shape → `iekClosureCall`
  # (walker-stubbed `ceNotImplemented` in C1; C2b adds application).
  block closureCallDetect:
    if calleeSym.kind == nnkSym:
      let impl = calleeSym.getImpl
      if impl.kind notin routineShapedForClosureDetect:
        let ti = calleeSym.getTypeInst
        if ti.kind == nnkProcTy:
          # RFC-0005 S8bh: with its `var`/`addr` effects; RFC-0005 S8ax:
          # its arguments in Nim's evaluation order.
          return closureCallIR(n, calleeSym, calleeName, preamble, ctx,
                               ordered = true).e
  # User-proc call in expression position. A-normalise. The instantiation
  # key returned by `ensureProcRegistered` (G1a) is the dispatch key the
  # walker looks up — it MUST be the `mkCall` callee name (not the bare name).
  # RFC-0005 S8bn (item 6): a method dispatches on the receiver's dynamic
  # type.
  if calleeSym.kind == nnkSym and calleeSym.symKind == nskMethod:
    let synthM = freshSynth(ctx, calleeName)
    let d = methodDispatchStmt(n, calleeSym, synthM, classifyType(n).ty,
                               preamble, ctx)
    if d != nil:
      preamble.add d
      return mkVar(synthM)
  let callKey = ensureProcRegistered(ctx, calleeSym, n)
  let retCls = classifyType(n)
  let synth = freshSynth(ctx, calleeName)
  # Round-6 B5 (ADR-0028 Leg 1, chained composition): if the callee's OWN
  # body is a recognized B3/B4 scan closed form, the returned position
  # (tuple field or bare scalar) is a genuine Sequence-theory Int — mark it
  # so the call's fresh retSym allocates svInt there instead of the
  # type-driven BV default (see `IRStmt.isCall.retIntOffsetPositions`'s doc).
  let offsetPositions = calleeIntOffsetReturnPositions(calleeSym)
  # RFC-0005 S8ax: bound first -- `userCallStmt` may rebuild `preamble`
  # (`orderOperands`), and `preamble.add userCallStmt(.., preamble, ..)`
  # appended to the sequence as it stood before the call.
  let callStmt = userCallStmt(n, calleeSym, callKey, synth, retCls.ty,
                              offsetPositions, preamble, ctx)
  preamble.add callStmt
  mkVar(synth)

proc parseBorrowViewedExpr(rw: NimNode,
                           views: seq[tuple[node, baseTy: NimNode]],
                           preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bc (item 2). Parse a borrowed routine call's rewrite `rw`
  ## (`borrowRoutineRewrite`) with its argument views pushed.
  let mark = borrowBaseViews.len
  borrowBaseViews.add views
  result = parseExpr(rw, preamble, ctx)
  borrowBaseViews.setLen mark

proc methodOverrides(sym: NimNode): seq[NimNode] =
  ## RFC-0005 S8bn (item 6). Every method named as `sym` that is visible
  ## where the entry macro was called (`methodRegistry`): the base method
  ## and its overrides.
  for c in methodRegistry.getOrDefault(macros.strVal(sym)):
    if c.kind == nnkSym and c.symKind == nskMethod: result.add c

proc methodRecvPointee(m: NimNode): IRType =
  ## RFC-0005 S8bn (item 6). The object type of method `m`'s first
  ## parameter (its receiver), or nil.
  let impl = m.getImpl
  if impl.kind != nnkMethodDef or impl.len < 4 or impl[3].len < 2: return nil
  let t = classifyType(impl[3][1][^2]).ty
  if t == nil or t.kind != itRef: return nil
  t.refPointeeTy

proc sameTailParams(a, b: NimNode): bool =
  ## RFC-0005 S8bn (item 6). Methods `a` and `b` take the same parameters
  ## after the receiver (an override, not another overload).
  let fa = a.getImpl[3]
  let fb = b.getImpl[3]
  var ta, tb: seq[NimNode]
  for i in 1 ..< fa.len:
    for _ in 0 ..< fa[i].len - 2: ta.add fa[i][^2]
  for i in 1 ..< fb.len:
    for _ in 0 ..< fb[i].len - 2: tb.add fb[i][^2]
  if ta.len != tb.len: return false
  for k in 1 ..< ta.len:
    if ta[k].repr != tb[k].repr: return false
  true

proc methodDispatchStmt(n, calleeSym: NimNode; retName: string;
                        retTy: IRType; preamble: var seq[IRStmt];
                        ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bn (item 6). A method call dispatches on the receiver's
  ## dynamic type: Nim runs the most specific override whose receiver type
  ## is the dynamic type or an ancestor of it. Before S8bn the call
  ## declined (the base body would substitute for an override). The
  ## overrides are the methods of the name visible at the entry
  ## (`methodOverrides`), with the call's other parameters, whose receiver
  ## is in the static receiver type's hierarchy: those at or above it (the
  ## deepest of them is the fallback), and those below it, each tested on
  ## the run-type tag at the depths below the static type's (`of`'s test,
  ## `parseOfTest`), deepest first. The receiver is read once; a nil one
  ## takes the dereference edge (Nim's dispatcher reads its type). nil
  ## when the call is not dispatchable this way (the caller then declines,
  ## as before).
  if n.len < 2: return nil
  let recv = n[1]
  var recvNode = recv
  while recvNode.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkHiddenDeref} and
        recvNode.len > 0:
    recvNode = recvNode[^1]
  let st = classifyType(recv).ty
  if st == nil or st.kind != itRef: return nil
  let sp = st.refPointeeTy
  let sc = hierChain(sp)
  if sc.len == 0 or not simpleRefExpr(recvNode): return nil
  var below: seq[tuple[depth: int; sym: NimNode; chain: seq[string]]]
  var fallback: NimNode = nil
  var fallbackDepth = -1
  for m in methodOverrides(calleeSym):
    if not sameTailParams(m, calleeSym): continue
    let mp = methodRecvPointee(m)
    let mc = hierChain(mp)
    if mc.len == 0 or mc[0] != sc[0]: continue
    let short = min(mc.len, sc.len)
    if mc[0 ..< short] != sc[0 ..< short]: continue
    if mc.len <= sc.len:
      if mc.len > fallbackDepth:
        fallbackDepth = mc.len
        fallback = m
    else:
      below.add (depth: mc.len, sym: m, chain: mc)
  if fallback == nil: return nil
  below.sort(proc (a, b: auto): int = cmp(b.depth, a.depth))
  # The receiver, read once; its tag at the first depth below the static
  # type is read even when no override is below (the dispatcher's read of a
  # nil receiver's type).
  let cell = freshSynth(ctx, "methodRecv")
  preamble.add mkLet(cell, st, parseExpr(recv, preamble, ctx))
  var maxLvl = sc.len
  for b in below: maxLvl = max(maxLvl, b.chain.len - 1)
  var tags = initTable[int, string]()
  for lvl in sc.len .. maxLvl:
    let t = freshSynth(ctx, "methodTag")
    preamble.add mkFieldDeref(t, mkVar(cell), tInt(64, signed = true), sp,
                              "@lvl" & $lvl)
    tags[lvl] = t
  proc callOf(m: NimNode): IRStmt =
    dispatchedMethods.add m
    var c = copyNimNode(n)
    c.add m
    for i in 1 ..< n.len: c.add n[i]
    let key = ensureProcRegistered(ctx, m, c)
    var pre: seq[IRStmt]
    let call = userCallStmt(c, m, key, retName, retTy, @[], pre, ctx)
    mkBlock(pre & @[call])
  var branches: seq[IRBranch]
  for b in below:
    var ok: IRExpr = nil
    for lvl in sc.len ..< b.chain.len:
      let eq = mkBinop(bEq, mkVar(tags[lvl]),
                       mkIntLit(inheritTagCode(b.chain[lvl])))
      ok = if ok == nil: eq else: mkBinop(bAnd, ok, eq)
    branches.add mkBranch(ok, callOf(b.sym))
  let fb = callOf(fallback)
  if branches.len == 0: fb
  else: mkIf(branches, fb)

proc userOrMethodCallStmt(n, calleeSym: NimNode; preamble: var seq[IRStmt];
                          ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bn (item 6). A statement-position user call: a method
  ## dispatches on the receiver's dynamic type (`methodDispatchStmt`);
  ## anything else, or a method not dispatchable so, is walked (or
  ## declined) as before.
  if calleeSym.kind == nnkSym and calleeSym.symKind == nskMethod:
    let d = methodDispatchStmt(n, calleeSym, "", tBool(), preamble, ctx)
    if d != nil: return d
  let callKey = ensureProcRegistered(ctx, calleeSym, n)
  userCallStmt(n, calleeSym, callKey, "", tBool(), @[], preamble, ctx)

proc isOfTest(n: NimNode): bool =
  ## RFC-0005 S8bn (item 7). `n` is the `of` operator (`x of T`): the
  ## system magic, never a user routine of that name.
  n.kind in {nnkInfix, nnkCall, nnkCommand} and n.len == 3 and
    n[0].kind == nnkSym and macros.strVal(n[0]) == "of" and
    not isUserCallee(n[0])

proc parseOfTest(n: NimNode; preamble: var seq[IRStmt]; ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bn (item 7). `x of T` over a ref (or ptr) of an inheritance
  ## hierarchy: false for nil, else a test of `x`'s run-type tag (S8bh's
  ## per-depth tags, `inheritTagKey`). Depths up to `x`'s static type agree
  ## by static typing (S8bn item 9 ties a parameter's to it), so a `T` at
  ## or above it is `x != nil`; a deeper `T` compares each deeper level
  ## with `T`'s chain, a test of the whole subtree below `T` (a descendant
  ## of `T` agrees on `T`'s levels). A `T` off `x`'s chain is false. Before
  ## S8bn `of` was unsupported.
  let operand = n[1]
  let o = classifyType(operand).ty
  # The type operand's own type is `typeDesc[T]`: classify `T`.
  var tn = n[2].getTypeInst
  if tn.kind == nnkBracketExpr and tn.len == 2 and tn[0].kind == nnkSym and
     macros.strVal(tn[0]).normalize == "typedesc":
    tn = tn[1]
  let t = classifyType(tn).ty
  proc pointeeOf(x: IRType): IRType =
    if x == nil: nil
    elif x.kind == itRef: x.refPointeeTy
    elif x.kind == itPtr: x.ptrPointeeTy
    else: x
  let op = pointeeOf(o)
  let tp = pointeeOf(t)
  let sc = hierChain(op)
  let tc = hierChain(tp)
  if o == nil or o.kind notin {itRef, itPtr} or sc.len == 0 or tc.len == 0 or
     sc[0] != tc[0]:
    preamble.add ctx.declineAtSite(feUnsupportedExprKind,
      siteMsg(n, "`of` on a value outside a modelled ref hierarchy " &
              "(RFC-0005 S8bn; feUnsupportedExprKind)"),
      "`of` outside a modelled hierarchy (feUnsupportedExprKind)")
    return mkBoolLit(false)
  let opIR = parseExpr(operand, preamble, ctx)
  let short = min(sc.len, tc.len)
  if sc[0 ..< short] != tc[0 ..< short]:
    return mkBoolLit(false)          # `T` is off `x`'s chain
  let cell = freshSynth(ctx, "ofObj")
  preamble.add mkLet(cell, o, opIR)
  let nonNil = mkBinop(bNe, mkVar(cell), mkNil(o))
  if tc.len <= sc.len:
    return nonNil
  let res = freshSynth(ctx, "ofRes")
  preamble.add mkLet(res, tBool(), mkBoolLit(false))
  var reads: seq[IRStmt]
  var ok: IRExpr = nil
  for lvl in sc.len ..< tc.len:
    let tag = freshSynth(ctx, "ofTag")
    reads.add mkFieldDeref(tag, mkVar(cell), tInt(64, signed = true), op,
                           "@lvl" & $lvl, ptrFamily = o.kind == itPtr)
    let eq = mkBinop(bEq, mkVar(tag), mkIntLit(inheritTagCode(tc[lvl])))
    ok = if ok == nil: eq else: mkBinop(bAnd, ok, eq)
  reads.add mkAssign(res, ok)
  preamble.add mkIf(@[mkBranch(nonNil, mkBlock(reads))])
  mkVar(res)

proc parseExpr*(n: NimNode, preamble: var seq[IRStmt], ctx: ParseCtx): IRExpr =
  # RFC-0005 S8bd: a by-reference base marked from an element or a call
  # result (`markByRef`) is its parameter, as a marked symbol is.
  if n.kind != nnkSym and n.len == 0 and byRefName(n).len > 0:
    return mkVar(byRefName(n))
  # RFC-0005 S8bu: an `openArray` actual is the seq it views.
  if isToOpenArray(n) or
     (n.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkConv} and n.len == 2 and
      n.typeKind == ntyOpenArray):
    return openArrayView(n, preamble, ctx)
  # RFC-0005 S8bc (item 2): a non-operator `{.borrow.}` routine call is its
  # base routine's call on the unwrapped arguments (`borrowRoutineRewrite`).
  block borrowRoutine:
    let (rw, views) = borrowRoutineRewrite(n)
    if rw != nil: return parseBorrowViewedExpr(rw, views, preamble, ctx)
  # RFC-0005 S8bc (item 7): `mgetOrPut(t, k[, d])` read as a value is the
  # get-or-insert (`parseMGetOrPut`). Hooked ahead of the `nnkHiddenDeref`
  # arm its `var B` result is wrapped in.
  if n.kind in {nnkHiddenDeref, nnkCall, nnkCommand}:
    let mg = parseMGetOrPut(n, preamble, ctx)
    if mg != nil: return mg
  if isOfTest(n): return parseOfTest(n, preamble, ctx)   ## RFC-0005 S8bn
  case n.kind
  of nnkNilLit:
    # RFC-0005 S8bn (item 7). A `nil` literal in any typed position (`let
    # b: Base = nil`, an argument, a `return`, an assignment) is its type's
    # nil; it parsed only in a comparison and a ref field's constructor
    # value. A position whose type is not a ref or ptr declines.
    let t = classifyType(n).ty
    if t != nil and t.kind in {itRef, itPtr}:
      mkNil(t)
    else:
      preamble.add ctx.declineAtSite(feUnsupportedExprKind,
        siteMsg(n, "`nil` of a type the walk holds no nil for (" & $t &
                ") (RFC-0005 S8bn; feUnsupportedExprKind)"),
        "nil literal of an unmodelled type (feUnsupportedExprKind)")
      mkIntLit(0)
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # RFC-0005 S8bn (item 7): Nim folds an `of` test static typing decides
    # (`m of Base` for `m: Mid`, `s of Mid` for a sibling `s`) to a bool-
    # typed int literal 0 or 1. (`typeKind`, not `getTypeInst`: an untyped
    # literal -- the isolation entry, `tsymex_phase1_dsl` -- has no type.)
    if n.kind == nnkIntLit and n.intVal in 0'i64 .. 1'i64 and
       n.typeKind == ntyBool:
      mkBoolLit(n.intVal == 1)
    else:
      mkIntLit(n.intVal)
  of nnkUIntLit .. nnkUInt64Lit:
    mkIntLit(n.intVal)
  of nnkCharLit:
    mkIntLit(n.intVal)   ## Phase 15 Z3c: char literal -> its ordinal (char = uint8)
  of nnkFloatLit, nnkFloat32Lit, nnkFloat64Lit:
    mkFloatLit(n.floatVal, if n.kind == nnkFloat32Lit: 32 else: 64)   ## Phase 15 F2
  of nnkIdent, nnkSym:
    let s = n.strVal
    if s == "true": mkBoolLit(true)
    elif s == "false": mkBoolLit(false)
    else:
      # #141: enum value — `getType` of the Sym yields nnkEnumTy
      # directly. Find the value's ord by scanning the enum body.
      if n.kind == nnkSym:
        # Issue #163 review finding R15. `n.getType` on an enum FIELD
        # symbol (e.g. `roLess`) reconstructs the structural type and
        # returns `nnkEnumTy` DIRECTLY -- confirmed by a `treeRepr` probe
        # against this exact toolchain -- and this is the ONLY reliable,
        # general-purpose gate for "is `n` actually an enum constant at
        # all" available here: this whole `nnkSym` arm is reached by EVERY
        # symbol reference (locals, params, consts, proc values, ...), not
        # just enum constants, so this gate must positively confirm
        # enum-ness before doing anything enum-specific -- a `nil` result
        # from an ENUM-SPECIFIC resolution attempt is not evidence of
        # anything for a symbol that was never an enum constant to begin
        # with. (Review round 2, R19 post-mortem: an earlier version of
        # this fix used `getTypeInst` failing-to-resolve as that gate
        # instead, which is also `nil` for every ordinary non-enum
        # symbol -- degrading EVERY variable/const/proc-value reference
        # that reached this arm. Caught by the neighbour-suite regression
        # sweep, not by this file's own test corpus.)
        #
        # That reconstruction throws away explicit field values, though:
        # every child comes back as a bare `nnkSym`, never
        # `nnkEnumFieldDef`, even for a field declared `roLess = -1`. So
        # once we KNOW `n` is enum-typed, `n.getTypeInst` -> `getImpl` is
        # used instead to get the value-preserving impl (R15): it returns
        # the NAMED type symbol (`Ordering`), whose `getImpl` is the
        # ORIGINAL `nnkTypeDef` as written in source, `nnkEnumFieldDef`
        # values intact.
        let directTy = n.getType
        if directTy.kind == nnkEnumTy:
          var enumBody: NimNode = nil
          let tyInst = n.getTypeInst
          if tyInst.kind == nnkSym:
            let implInst = tyInst.getImpl
            if implInst.kind == nnkTypeDef and implInst.len >= 3 and
               implInst[2].kind == nnkEnumTy:
              enumBody = implInst[2]
          if enumBody != nil:
            # Issue #163 review round 2 (R18/R23): both loops that used to
            # walk an enum body independently (this one, and
            # `dsl_typebridge.classifyType`'s enum arm) now share ONE
            # function, `dsl_typebridge.enumFieldOrdinals` -- see its doc
            # comment for the full field-shape inventory (explicit int
            # literal, R18's tuple-constructor form, string-name-only
            # implicit ordinals, and R23's fail-loudly-on-unknown-kind
            # policy). A hand-mirrored second loop here is exactly the
            # divergence class review finding R15 had to close once
            # already.
            for (name, ord) in enumFieldOrdinals(enumBody):
              if name == s:
                return mkIntLit(ord)
          else:
            # Issue #163 review finding R19. `n` IS confirmed enum-typed
            # (the `directTy.kind == nnkEnumTy` gate above), but
            # `getTypeInst` did not land on a usable value-preserving
            # impl. The old code's fallback here was to embed a
            # positional guess via the value-discarding `n.getType`
            # reconstruction (`directTy` itself) -- but that path is
            # PROVEN (the same probe cited above) to always discard every
            # explicit field value, so it could only ever read IMPLICIT
            # auto-increment ordinals: correct by coincidence for a dense
            # zero-based enum, and a confidently wrong embedded constant
            # for any enum with an explicit non-auto ordinal -- silently,
            # with no error, warning, or degrade signal. That is worse
            # than declining: it is exactly the defect class R15 exists to
            # close, reopened one level up the resolution chain. Whether
            # some generic- or alias-mediated shape can still defeat
            # `getTypeInst` for a legitimately enum-typed symbol is not
            # enumerated (the review flagged this explicitly). Per this
            # engine's own Invariant 3 (never crash, never silently wrong
            # -- degrade to `sxUnknown` instead), "not proven unreachable"
            # is not license to guess: record a classified parse error and
            # decline, matching this proc's own established degrade idiom
            # (the else-less case-expression arm elsewhere in this file).
            preamble.add ctx.declineAtSite(
              feEnumOrdinalUnresolved,
              siteMsg(n, "enum constant '" & s & "' -- getTypeInst " &
                                "did not resolve to its declaring enum " &
                                "type; declining rather than embedding a " &
                                "positional guess (feEnumOrdinalUnresolved, " &
                                "issue #163 review R19)"),
              "enum constant '" & s & "' ordinal " &
                                         "unresolved (feEnumOrdinalUnresolved)")
            return mkIntLit(0)
        # `n` is not enum-typed at all (`directTy.kind != nnkEnumTy`) --
        # fall through to the ordinary symbol-resolution paths below
        # (module-level const, top-level proc value, plain variable, ...).
        # v69 (chapulin "&-concat sxUnknown" root cause — which was never
        # about concat): a CONST symbol referenced in value position
        # (`s & SidecarExt`) emitted `iekVar("SidecarExt")`, but module-level
        # consts are never bound in any env — a guaranteed KeyError →
        # weInternalWalkerFault → sxUnknown, in whatever expression happened
        # to reference the const (hence the reported shape-sensitivity:
        # spellings where the const folded to a literal proved fine). Fold
        # the const to its VALUE at parse time: `getImpl` of an nskConst sym
        # is the nnkConstDef `[name, ty, value]`; recursing into the value
        # node reuses every literal/expression arm the parser already has.
        # Unresolvable shapes fall through to mkVar (prior behavior).
        if symKind(n) == nskConst:
          let cImpl = n.getImpl
          if cImpl.kind == nnkConstDef and cImpl.len >= 3 and
             cImpl[2].kind != nnkEmpty:
            return parseExpr(cImpl[2], preamble, ctx)
        # Phase 15 C3 (reconciliation §F-C). A TOP-LEVEL proc referenced in
        # VALUE position (`let g = double`, or `double` as a proc-valued ARG) →
        # an `iekLambda` with empty captures (a unit-env closure). This branch
        # is the bare-`nnkSym` EXPRESSION path ONLY: a proc in CALLEE position is
        # `n[0]` of an `nnkCall` (parsed structurally, never via parseExpr) and a
        # call THROUGH a proc-valued local (`g(n)`) is the C2b `earlyClosure
        # CallDetect` — so neither reaches here. A `nnkParam`-kinded proc-valued
        # PARAMETER (symKind == nskParam) also does not resolve to a
        # `walkableRoutineKinds` impl, so it stays the proc-valued-param
        # svClosure path (C2b), not C3. We require a resolvable
        # `nnkProcDef`/`nnkFuncDef` impl (a real module-scope proc/func body
        # to inline).
        #
        # RFC-parser-normalization N2: the former TWO-gate shape
        # (`symKind(n) in {nskProc, nskFunc}` pre-filter, THEN a separate
        # `impl.kind in {nnkProcDef, nnkFuncDef}` check — N0 widened both)
        # collapses onto ONE `resolveRoutineImpl(n)` call with no symKind
        # pre-check. This is behavior-identical, confirmed by a compile-time
        # probe against this toolchain (`scratchpad/probe_n2_getimpl_
        # symkinds.nim`, Nim 2.2.10): `getImpl` on an `nskParam`/`nskLet`/
        # `nskVar`/`nskForVar`/`nskResult` symbol (every non-routine kind
        # reachable at this bare-`nnkSym` expression site — `nskConst`
        # already returned above) never raises and never yields a
        # `walkableRoutineKinds` member (params/for-vars: `nnkNilLit`;
        # let/var: `nnkIdentDefs`) — so `resolveRoutineImpl` alone correctly
        # excludes every kind the old symKind pre-filter existed to route
        # elsewhere, without a second gate.
        let impl = resolveRoutineImpl(n)
        if impl != nil:
          return parseProcAsValue(n, impl, ctx)
      mkVar(s)
  of nnkStrLit, nnkRStrLit, nnkTripleStrLit:
    mkStrLit(n.strVal)
  of nnkCaseStmt:
    # RFC-0005 s1. A `case` in EXPRESSION position — A-normalise
    # into `<temp> := zero; <branching statement assigning temp>; <temp>` so
    # the already-complete STATEMENT lowering does the modelling. See
    # `hoistCaseExpr` for why this, and not a branch-scoped-degrade
    # architecture, is what BLOCKER B7-2 actually needed. The `nnkIfExpr`
    # sibling arm below (M5, walker v50->51) is the SAME idiom; unifying the
    # two behind one helper is a follow-up refactor-under-green, deliberately
    # not folded into this RED->GREEN slice.
    hoistCaseExpr(n, preamble, ctx)
  of nnkPar, nnkStmtListExpr:
    # CR-1b (RFC-chapulin-hardening, Cluster 2 — crash-totality). A
    # `nnkStmtListExpr` with more than one child is how semcheck presents a
    # value-returning proc's `result = (let hi = ...; hi + 1)` RHS — the
    # implicit tail return of a multi-statement body. Taking only the LAST
    # child (as this arm used to) silently dropped every LEADING statement,
    # including a `let` the tail expression reads — the walker would later
    # crash with an uncaught KeyError on `lower(iekVar)` because the local's
    # binding never made it into `env`. Parse each leading child as an
    # ordinary statement (mirroring `parseStmtInner`'s `nnkLetSection` arm)
    # into `preamble`, the same A-normalisation channel every other
    # expression-position side-effect in this file already uses — callers
    # (`parseCalleeImpl`'s `resultRhs` path, `isLet`/`isAssign` RHS parsing,
    # …) already thread `preamble` ahead of the expression's consumer, so
    # the binding flows into the tail expression's environment at walk time.
    for i in 0 ..< n.len - 1:
      preamble.add parseStmt(n[i], ctx)
    parseExpr(n[n.len - 1], preamble, ctx)
  of nnkLambda:
    # Phase 15 Cluster C (C1, ADR-0009). A lambda in expression position →
    # iekLambda (walker-stubbed `ceNotImplemented` in C1).
    parseLambda(n, ctx)
  of nnkProcDef, nnkFuncDef:
    # Phase 15 C1. A `proc(...) = ...` / `func(...) = ...` value lowered to an
    # expression-position proc/func def (vs the nnkLambda surface form) →
    # iekLambda. (ADR-0009: `func` is treated identically to `proc` here.)
    parseLambda(n, ctx)
  of nnkIteratorDef:
    # Phase 15 C1 (ADR-0009 Deferred). A closure iterator
    # (`iterator(): T {.closure.}`) in expression position is OUT OF SCOPE for
    # Cluster C → emit an iekLambda carrying an iterator marker so the walker
    # stub fires a classified `ceNotImplemented` (Invariant 3 — not a crash).
    # The detail string is surfaced at walk time via the stub message.
    var captures, mutCaptures: seq[string]
    var seen: HashSet[string]
    var bound: HashSet[string]
    let bodyNode = body(n)
    collectBoundLocals(bodyNode, bound)
    collectFreeVarRefs(bodyNode, bound, captures, seen, mutCaptures)
    let site = (siteHash: int64(hash("closure-iterator:" & lambdaBodyHash(n))),
                declOrder: ctx.lambdaCounter)
    inc ctx.lambdaCounter
    # Body is replaced with a sentinel unsupported stmt (closure iterators have
    # no symex-representable body); the walker never descends it (it stubs the
    # whole iekLambda first).
    mkLambda(site.siteHash, site.declOrder, @[],
             ctx.declineMarker(ceNotImplemented, "closure iterators not yet supported"),
             captures, tBool(), mutCaptures)
  of nnkCast:
    # RFC-0005 S8m. `cast[ref Obj](p)` with `p: ref Obj` reinterprets a ref as
    # the very type it already has: the same address, the same `Ref_<id>`
    # sort, so it is the identity and keeps `p`'s heap identity. Before, the
    # cast reached the catch-all below, whose int dummy crashed the first
    # `q != nil` (`eqBV`'s kind assert, `weInternalWalkerFault`). Any other
    # cast (a different pointee, a value reinterpretation) has no layout the
    # heap model can follow, and stays the catch-all's recorded decline. A
    # `cast[ptr T]` binding never gets here: `unsafeCastReason` declines it
    # as `heUnsafeCast` first.
    let tgt = refExprClassify(n)
    let src = if n.len == 2: refExprClassify(n[1]) else: tgt
    if n.len == 2 and tgt.ty.kind in {itRef, itPtr} and
       src.ty.kind == tgt.ty.kind and src.ty == tgt.ty:
      return parseExpr(n[1], preamble, ctx)
    # The decline is the catch-all's own, message for message (no site
    # prefix: RFC-0005 S9's twin-decline dedup keys on message AND anchor,
    # and two casts of one spelling must stay one message).
    let dummyTy = classifyType(n).ty
    preamble.add ctx.declineAtSite(
      feUnsupportedExprKind,
      "CR-2a: unsupported expression kind " & $n.kind & " in `" &
             n.repr & "` — not in the supported expression fragment",
      "CR-2a: unsupported expression kind " &
                                  $n.kind & " (feUnsupportedExprKind)")
    let dummy = zeroValueForType(dummyTy)
    if dummy != nil: dummy else: mkIntLit(0)
  of nnkConv:
    # Phase 15 F5: detect int<->float conversions; other explicit conversions
    # (int widening, etc.) fall through to pass-through unwrapping.
    let operand = n[n.len - 1]
    # RFC-0005 S8bc: an inlined iterator's parameter is its typed formal
    # symbol (the S8at untyped-ident decline here is gone with the
    # substitution that produced the ident).
    let tgt = typeNodeName(n[0])
    let src = valueTypeName(operand)
    let hier = hierarchyConv(n, operand)
    if hier.isHier:
      # RFC-0005 S8bh (item 3). A ref converted along its inheritance chain
      # is the same address (one `Ref_<root>` sort, `refPointeeTypeId`): an
      # up-conversion (`Base(d)`) is the operand itself. A down-conversion
      # (`Derived(b)`) is too, after Nim's check that a non-nil `b`'s
      # dynamic type is a `Derived` (else ObjectConversionDefect). The check
      # compares `b`'s run-type tag at each depth below its static type's
      # with `Derived`'s chain (`inheritTagKey`, runtime_heap.nim). Before
      # S8bh both were the identity pass-through below, over two sorts: an
      # ill-sorted term, and no check at all.
      let opIR = parseExpr(operand, preamble, ctx)
      if hier.tgtChain.len <= hier.srcChain.len:
        opIR
      else:
        let cell = freshSynth(ctx, "objConv")
        preamble.add mkLet(cell, hier.tgtTy, opIR)
        var reads: seq[IRStmt]
        var ok: IRExpr = nil
        for lvl in hier.srcChain.len ..< hier.tgtChain.len:
          let tag = freshSynth(ctx, "objConvTag")
          reads.add mkFieldDeref(tag, mkVar(cell), tInt(64, signed = true),
                                 hier.tgtPointee, "@lvl" & $lvl,
                                 ptrFamily = hier.tgtTy.kind == itPtr)
          let eq = mkBinop(bEq, mkVar(tag),
                           mkIntLit(inheritTagCode(hier.tgtChain[lvl])))
          ok = if ok == nil: eq else: mkBinop(bAnd, ok, eq)
        reads.add mkIf(@[mkBranch(mkUnop(uNot, ok),
                                  mkRaise("ObjectConversionDefect", nil))])
        preamble.add mkIf(@[mkBranch(
          mkBinop(bNe, mkVar(cell), mkNil(hier.tgtTy)), mkBlock(reads))])
        mkVar(cell)
    elif tgt in fltTyNames and src in intTyNames:
      mkConvIntToFloat(parseExpr(operand, preamble, ctx), if tgt == "float32": 32 else: 64)
    elif tgt in intTyNames and src in fltTyNames:
      # RFC-0005 S8g: the target's own width and signedness (`int8(f)` was
      # lowered at width 64, `uint8(f)` as signed).
      mkConvFloatToInt(parseExpr(operand, preamble, ctx),
                       intTyWidth(tgt), intTySigned(tgt))
    elif src in fltTyNames and classifyType(n[0]).ty.kind == itInt and
         classifyType(n[0]).range.hasRange:
      # RFC-0005 S8g: a `range` target (`Natural(f)`). Nim converts to the
      # base type, then range-checks the converted value (`RangeDefect`).
      # This was the identity pass-through: a float flowed on as the
      # "Natural" and the check was never modelled.
      let cls = classifyType(n[0])
      mkConvFloatToInt(parseExpr(operand, preamble, ctx),
                       cls.ty.width, cls.ty.signed,
                       true, cls.range.lo, cls.range.hi)
    elif not isIntLiteralNode(operand) and
         n.typeKind in {ntyRange, ntyEnum} and
         operand.typeKind in {ntyInt, ntyInt8, ntyInt16, ntyInt32, ntyInt64,
                              ntyUInt, ntyUInt8, ntyUInt16, ntyUInt32,
                              ntyUInt64, ntyRange, ntyEnum} and
         classifyType(n).ty.kind == itInt and classifyType(n).range.hasRange and
         classifyType(operand).ty.kind == itInt:
      # RFC-0005 S8i: an integer converted to a `range` or enum target
      # (`Natural(x)`, `range[a..b](x)`, `R(x)`, `E(x)`). Nim range-checks
      # the operand's value (`RangeDefect`), then converts at the target's
      # width. This was the identity pass-through below: an out-of-range
      # value flowed on as the target type, the check never modelled.
      let tcls = classifyType(n)
      let scls = classifyType(operand)
      mkConvIntWidth(parseExpr(operand, preamble, ctx),
                     scls.ty.width, scls.ty.signed,
                     tcls.ty.width, tcls.ty.signed,
                     true, tcls.range.lo, tcls.range.hi)
    elif tgt in intTyNames and src == "bool":
      # v69 (sello #3): `int32(b)` — previously the pass-through below, which
      # left an svBool flowing where an int-kinded SymVal is required
      # (`-int32(b)`, the ref10 mask idiom, then died in negBV's non-BV arm).
      # A-normalise via the M5 if-expression idiom: a fresh temp bound to
      # 1/0 at the conversion's classified width (the v69 isLet proto shapes
      # the literals), read back as the expression value.
      let convTy = classifyType(n).ty
      let tmp = freshSynth(ctx, "boolConv")
      let condIR = parseExpr(operand, preamble, ctx)
      preamble.add mkIf(
        @[mkBranch(condIR, mkLet(tmp, convTy, mkIntLit(1)))],
        mkLet(tmp, convTy, mkIntLit(0)))
      mkVar(tmp)
    elif isIntFamilyName(tgt) and isIntFamilyName(intConvSrcName(operand, src)) and
         tgt != intConvSrcName(operand, src):
      # Round-6 B2 (RFC-chapulin-hardening, ADR-0028 Leg 2): int-family
      # conversion between two DIFFERENT fixed-width type spellings.
      # `uint16(b)` (call syntax) and `b.uint16` (method-call syntax) both
      # arrive here as the identical nnkConv shape — Nim desugars dot-call
      # syntax to the ordinary type conversion, same as the explicit form.
      # `isIntFamilyName` includes the `byte` alias (`normalizeIntTyName`,
      # B2 rider) — the RFC's own primary consumer shape, `uint16(b) shl 8`
      # with `b: byte` (chapulin `protocol.nim:93`), needs it recognized
      # here or it falls through to the untouched identity pass-through.
      # Round-6 B7-rider: `isIntFamilyName` ALSO now includes `char`
      # (normalized to `"uint8"`, same as `byte`) — `uint16(s[i])` off a
      # STRING receiver's char read needs the identical widening treatment,
      # or it silently drops the conversion (`normalizeIntTyName`'s own doc
      # comment has the full root-cause writeup — this was the char-widening
      # witness-corruption companion bug's actual cause).
      let srcN = normalizeIntTyName(intConvSrcName(operand, src))
      let tgtN = normalizeIntTyName(tgt)
      # Both normalized names are guaranteed `intTyNames` members here, so
      # `intTyWidth`/`intTySigned` are total.
      let srcWidth = intTyWidth(srcN)
      let tgtWidthV = intTyWidth(tgtN)
      let srcSigned = intTySigned(srcN)
      let tgtSignedV = intTySigned(tgtN)
      # RFC-0005 S8bc: a constant operand -- a typed integer literal
      # (`int(-200'i16)`) or `low`/`high` of an int-family type
      # (`int(high(int32))`, which the parser lowers to an untagged literal
      # through `lowHighIntLit`) -- whose value the target holds is that
      # value. It reached `mkConvIntWidth`, whose walker asserts a BV operand
      # of the source width, while an untagged literal lowers at 64 bits: a
      # `weInternalWalkerFault` on `y > int(high(int32))`. The hidden
      # conversion arm already passes a literal through (`isIntLiteralNode`).
      let lowHighOp = operand.kind == nnkCall and operand.len == 2 and
        operand[0].kind == nnkSym and operand[0].strVal in ["low", "high"] and
        isStdlibDecl(operand[0]) and typeNodeName(operand[1]) in intTyNames
      if isIntLiteralNode(operand) or lowHighOp:
        let v =
          if lowHighOp:
            lowHighIntLit(typeNodeName(operand[1]),
                          wantLow = operand[0].strVal == "low")
          else: operand.intVal
        let fits =
          if tgtSignedV:
            tgtWidthV >= 64 or
              (v >= -(1'i64 shl (tgtWidthV - 1)) and
               v < (1'i64 shl (tgtWidthV - 1)))
          else:
            v >= 0 and (tgtWidthV >= 64 or v < (1'i64 shl tgtWidthV))
        if fits and (srcSigned or v >= 0):
          return mkIntLit(v)
      # RFC-0005 S8j: which conversions range-check. Probed on the pinned
      # toolchain (c and cpp identical), with the operand through a noinline
      # identity so nothing folds:
      #   * a SIGNED target checks the operand's VALUE against its own
      #     bounds -- `int8(200)`, `int8(300'i16)`, `int32(1 shl 40)` and,
      #     at the SAME width, `int8(200'u8)`, `int32(high(uint32))`,
      #     `int(2^63'u64)` all raise `RangeDefect` ("value out of range:
      #     200 notin -128 .. 127"); `int8(-1'i64) == -1`;
      #   * an UNSIGNED target never checks: `uint8(300) == 44`,
      #     `uint16(-1) == 65535`, `byte(300) == 44` -- it truncates, as C;
      #   * a `char` target checks 0 .. 255 although it normalizes to
      #     `uint8` here: `char(300)`, `char(-1)`, `char(-1'i8)` raise.
      # A checked conversion lowers through S8i's range conversion (the
      # negated check to `rangeDefectConds`, the value then converted --
      # exact wherever the check passes); an unchecked narrowing lowers to
      # the truncation. Both were the recorded narrowing decline below
      # (`int8(x)`, `uint8(x)`, `char(x)`), and the same-width unsigned ->
      # signed case was the unchecked reinterpret.
      let tgtIsChar = tgt == "char"
      let checked =
        if tgtIsChar: srcN != "uint8"
        else: tgtSignedV and (tgtWidthV < srcWidth or
                              (tgtWidthV == srcWidth and not srcSigned))
      if checked:
        let (lo, hi) =
          if tgtIsChar: (0'i64, 255'i64)
          elif tgtWidthV >= 64: (low(int64), high(int64))
          else: (-(1'i64 shl (tgtWidthV - 1)), (1'i64 shl (tgtWidthV - 1)) - 1)
        mkConvIntWidth(parseExpr(operand, preamble, ctx),
                       srcWidth, srcSigned, tgtWidthV, tgtSignedV,
                       true, lo, hi)
      elif tgtWidthV > srcWidth:
        # WIDENING. Zero-/sign-extend is
        # keyed on the SOURCE value's signedness (RFC B2); the resulting
        # SymVal's own `signed` flag takes the TARGET type's signedness.
        mkConvIntWidth(parseExpr(operand, preamble, ctx),
                       srcWidth, srcSigned, tgtWidthV, tgtSignedV)
      elif tgtWidthV < srcWidth:
        # NARROWING into an unsigned target (`byte(x)`/`uint8(x)` from an
        # `int32`): the low bits, never a raise (RFC-0005 S8j; was the
        # recorded B2 decline -- the pre-B2 identity pass-through had left
        # the value unmasked).
        mkConvIntWidth(parseExpr(operand, preamble, ctx),
                       srcWidth, srcSigned, tgtWidthV, tgtSignedV)
      elif srcSigned != tgtSignedV:
        # SAME-WIDTH signedness REINTERPRET (e.g. `uint32(x)` from an
        # `int32`; RFC-0005 S8j: the unsigned -> signed direction checks,
        # above, so only signed -> unsigned reaches here). A1 adjudication (walker v116): B2 originally recorded
        # this as a decline, but the underlying Z3 BV bit pattern is
        # signedness-agnostic — the pre-B2 identity pass-through's actual
        # unsoundness was leaving a STALE `signed` flag (steering
        # signed-vs-unsigned compares downstream), not the value itself.
        # `mkConvIntReinterpret` fixes the flag instead of declining: same
        # width both sides (`srcWidth == tgtWidthV` in this branch), so no
        # extend/truncate primitive is needed at all.
        mkConvIntReinterpret(parseExpr(operand, preamble, ctx),
                              srcWidth, tgtSignedV)
      else:
        # Same normalized width AND signedness under different SPELLINGS
        # ONLY: `byte` vs `uint8` themselves, or `int`/`int64`,
        # `uint`/`uint64` aliasing width 64 on this platform (NEITHER
        # normalized by `normalizeIntTyName`, which only maps `byte` —
        # `srcN`/`tgtN` can still differ textually here) — genuinely a
        # no-op; ordinary identity pass-through, unchanged from pre-B2
        # behavior.
        parseExpr(operand, preamble, ctx)
    else:
      parseExpr(operand, preamble, ctx)
  of nnkHiddenStdConv, nnkHiddenSubConv, nnkHiddenAddr:
    # RFC-0005 S8bc (item 7). An EMPTY `@[]` passed where a `seq[T]` is
    # expected (`t[k] = @[]`, `mgetOrPut(t, k, @[])`, `getOrDefault(t, k,
    # @[])`) types `seq[empty]` and reaches the parameter through
    # `HiddenSubConv(Empty, Prefix(@, Bracket()))`. The `@` arm classifies
    # the literal itself, whose element is no modelled type, so the empty
    # seq was built over the unbacked placeholder sort (`Array Int Bool`)
    # and the first store into it was a walker fault (`Z3 sort mismatch`).
    # The conversion's own type is the `seq[T]` the literal becomes.
    if n.kind == nnkHiddenSubConv and n.len == 2 and
       n[1].kind == nnkPrefix and n[1].len == 2 and
       n[1][0].kind == nnkSym and n[1][0].strVal == "@" and
       n[1][1].kind == nnkBracket and n[1][1].len == 0:
      let convCls = classifyType(n)
      if convCls.ty.kind == itSeq:
        return mkSeqLit(@[], convCls.ty.seqElemTy)
    # Issue #163 review (rev item 2). `nnkHiddenSubConv` joins the existing
    # `nnkHiddenStdConv` passthrough here: it is the conversion the compiler
    # inserts between a `range[..]` value and its BASE type (confirmed via a
    # `treeRepr` probe -- `c > 'm'` for `c: range['a'..'z']` types the `<`
    # operand as `HiddenSubConv(Empty, Sym "c")`; the analogous INT range
    # comparison uses `nnkHiddenStdConv` instead, already handled here). A
    # subrange shares its base type's runtime representation -- Nim's bounds
    # check is compile-time-only bookkeeping, not a width/encoding change --
    # so unwrapping is exactly as sound as the existing `nnkHiddenStdConv`
    # passthrough, not a new kind of identity claim. Before this, ANY
    # expression reaching a bare char-range comparison declined outright
    # (`feUnsupportedExprKind`); finding W3 (`dsl_typebridge.nim`) had
    # already fixed the TYPE side of char ranges, but this EXPRESSION-side
    # gap remained.
    #
    # #163 item 2 (rev). Blind unwrapping is sound ONLY when the hidden
    # conversion is representation-preserving (the subrange-strip case
    # above, and `nnkHiddenAddr`'s address-of annotation, which never
    # changes the pointee's value type). Nim ALSO inserts
    # `nnkHiddenStdConv` to WIDEN a narrower fixed-width int operand up to
    # match a wider peer -- e.g. `a: int32` compared against the untyped
    # literal `3_000_000_000`, which itself types `int64` because it does
    # not fit `int32` (`getImpl`/`treeRepr` puts `a` inside a
    # `HiddenStdConv` whose OWN `getTypeInst` is `int64`; confirmed via
    # `scratchpad/probe_163item2_treerepr.nim`, not committed). Blindly
    # unwrapping parsed `a` at its narrow width with no record of the
    # widening; the comparison's other operand -- a literal too big for
    # that narrow width -- then got folded into a same-sized BV downstream
    # and silently WRAPPED (`3_000_000_000` truncated into 32 bits reads
    # back as the negative `-1294967296`), so `a > 3_000_000_000` came back
    # `sxSat` for a target genuinely UNREACHABLE by any real `int32` value
    # (every `int32` is far below three billion) -- a soundness bug, not
    # merely an imprecision.
    #
    # Detect a genuine WIDTH change between the hidden conversion's own
    # resolved type and its wrapped operand's type and route it through the
    # same `mkConvIntWidth`/`declineIntWidthConv` machinery B2 built for the
    # explicit `nnkConv` case above. Every same-width hidden conversion
    # (subrange-strip, `nnkHiddenAddr`, or a spelling this engine does not
    # recognize as a plain fixed-width int) falls through to the original
    # identity pass-through, UNCHANGED.
    block:
      let isIndexConv = ctx.indexConvPending   # RFC-0005 S8i
      ctx.indexConvPending = false
      let wrapped = n[n.len - 1]
      # #163 regression fix (post-round-9 gate). Check the literal shape
      # BEFORE calling `classifyType` on anything: `tests/tsymex_phase15_
      # g10_smoke.nim`'s concept-constrained generic instantiation reaches
      # this arm with `wrapped` a plain `nnkIntLit` (`n.repr` is just `2`)
      # whose own type resolves fine (`wrapped.typeKind == ntyInt`), but
      # `n`'s (the conversion node's) `typeKind` reports `ntyNot` -- a
      # concept/typeclass type-EXPRESSION kind, not `ntyNone` -- so the
      # standing `typeKind != ntyNone` idiom this file uses everywhere else
      # to guard `classifyType` does NOT catch it: `classifyType(n)` still
      # crashes with "node has no type" (`dsl_typebridge.nim`'s
      # `getTypeInst` call) because `ntyNot` is exactly as unresolvable for
      # that call as `ntyNone` is, just spelled differently (confirmed via
      # an inline debug probe, not committed). This is a hard, non-catchable
      # macro-instantiation error that aborts the whole compile -- not an
      # exception this engine could degrade from even if it wanted to.
      #
      # A literal operand never needs `outerTy`/`innerTy` at all (see
      # `isIntLiteralNode` above): narrowing OR widening a literal is always
      # representation-safe, and `parseExpr`'s literal arm
      # (`mkIntLit(n.intVal)`) carries no width tag for downstream folding
      # to disagree with. Checking `isIntLiteralNode(wrapped)` first — before
      # `n` (or `wrapped`) is ever handed to `classifyType` — sidesteps the
      # crash entirely rather than trying to enumerate every unresolvable
      # `NimTypeKind` a generic/concept instantiation might produce.
      if isIntLiteralNode(wrapped):
        parseExpr(wrapped, preamble, ctx)
      else:
        let outerCls = classifyType(n)
        let innerCls = classifyType(wrapped)
        let outerTy = outerCls.ty
        let innerTy = innerCls.ty
        # #163 review (rev item 2 follow-up), soundness carve-out. A bare
        # reference to one of the CURRENT proc's own formal parameters
        # (`wrapped.kind == nnkSym and symKind(wrapped) == nskParam`) whose
        # classified type carries a proven range AND is signed is exactly the
        # shape `runtime.nim`'s `promoteSound` (issue #161) promotes at
        # top-level param entry to a Z3 UNBOUNDED Int (`svInt`) rather than a
        # fixed-width BV -- confirmed empirically
        # (`scratchpad/probe_163item2b_witness.nim`/`witness2.nim`, not
        # committed: both a narrow and a near-full-width SIGNED range-alias
        # PARAM already come back the correct `sxUnsat`, with no width
        # conversion inserted here at all). `mkConvIntWidth`'s walker
        # (`lowerConvIntWidth`, `runtime.nim`) hard-asserts its operand is
        # ALWAYS a raw BV -- true for every case it was built for (no
        # non-ranged fixed-width int, and no OBJECT FIELD/local of any int
        # type, is ever `promoteSound`-eligible), but NOT true for a
        # promoted param. Routing a promoted param through it anyway was
        # tried and regressed a correct `sxUnsat` to `sxUnknown`
        # (confirmed empirically the same way). Skip the fix for exactly
        # this carve-out -- identical to the untouched status quo, which
        # is independently sound here via `promoteSound` -- and apply it
        # everywhere else (object fields, locals, array/seq elements,
        # UNSIGNED ranged values, and any param whose range does not
        # qualify `promoteSound`), where no such promotion protects the
        # identity pass-through and the width truncation this fix targets
        # is real (confirmed: `scratchpad/probe_163item2b_witness3.nim`'s
        # range-typed OBJECT FIELD case came back a false `sxSat` before
        # this fix, witness `f = 0`, and the same real Nim expression is
        # false for every value 0..100).
        if not isIndexConv and
           n.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and
           outerTy.kind == itInt and innerTy.kind == itInt and
           outerCls.range.hasRange and
           not (innerCls.range.hasRange and
                innerCls.range.lo >= outerCls.range.lo and
                innerCls.range.hi <= outerCls.range.hi):
          # RFC-0005 S8i: the implicit conversion INTO a `range` type (`let
          # q: R = x`, `var n: Natural = x`, `K(n: x)`, `return x` from a
          # `Natural` proc, an argument to a `Natural` formal). Nim
          # range-checks it exactly as the explicit `R(x)` above (probed on
          # the pinned toolchain: each raises "value out of range: -1 notin
          # 0 .. 9223372036854775807"), unless the operand's own range lies
          # inside the target's -- then no check is emitted and none is
          # modelled. Before S8i this was the pass-through (or the width
          # route below): the out-of-range value flowed on unchecked.
          mkConvIntWidth(parseExpr(wrapped, preamble, ctx),
                         innerTy.width, innerTy.signed,
                         outerTy.width, outerTy.signed,
                         true, outerCls.range.lo, outerCls.range.hi)
        elif outerTy.kind == itInt and innerTy.kind == itInt and
           outerTy.width != innerTy.width and
           not isPromoteSoundEligibleParam(wrapped, innerTy):
          # This used to re-derive `srcWidth`/`tgtWidthV`/`srcSigned`/
          # `tgtSignedV` from a NAME-based lookup
          # (`isIntFamilyName(valueTypeName(...))`), which only recognizes the
          # closed `intTyNames` spelling set. `valueTypeName` reads
          # `getTypeInst`, which for a value whose DECLARED type is a named
          # `range[lo..hi]` alias or an `enum` reports that alias/enum NAME
          # (e.g. "SmallCount"), not a plain int spelling -- so the gate missed
          # both, falling back to the identity pass-through below for a
          # genuine width-changing hidden conversion on either shape.
          #
          # `outerTy`/`innerTy` are ALREADY the correct answer: `classifyType`
          # (`dsl_typebridge.nim`) resolves a range alias's base width/
          # signedness via `rangeBaseType` (issue #162) and an enum's lifted
          # representation via `enumOrdBitsNeeded` (issue #163 R2) -- both
          # stamped onto the `IRType` this block already computed above to
          # decide whether a width mismatch exists at all. Reading
          # `.width`/`.signed` directly off `outerTy`/`innerTy` instead of
          # re-deriving them from a second, name-based lookup closes the gap
          # without inventing a parallel type-resolution rule that could drift
          # from the classifier's own answer (the R11/R15/R16 failure mode).
          if outerTy.width > innerTy.width:
            mkConvIntWidth(parseExpr(wrapped, preamble, ctx),
                           innerTy.width, innerTy.signed,
                           outerTy.width, outerTy.signed)
          else:
            # An implicit NARROWING hidden conversion is not expected from
            # sound Nim typing (Nim widens implicitly; it does not implicitly
            # narrow), but decline rather than risk a silent truncation if
            # some toolchain shape ever produces one (Invariant 3 -- never a
            # crash, never a silent wrong verdict).
            declineIntWidthConv(n, preamble, ctx, "hidden narrowing",
                                 valueTypeName(wrapped), valueTypeName(n))
        elif outerTy.kind == itBitSet and innerTy.kind == itBitSet and
             bitSetDomain(outerTy.bsElemTy) != bitSetDomain(innerTy.bsElemTy):
          # RFC-0005 S8bq: a builtin set converted to one over another base
          # range has another bit layout; it is not modelled (it was never
          # reached: no set value classified before S8bq).
          preamble.add ctx.declineAtSite(feUnsupportedExprKind,
            "conversion of `" & wrapped.repr & "` from " & $innerTy & " to " &
              $outerTy & " is not modelled (feUnsupportedExprKind)",
            "builtin set conversion between base ranges " &
              "(feUnsupportedExprKind)")
          mkZeroValue(outerTy)
        else:
          parseExpr(wrapped, preamble, ctx)
  of nnkHiddenCallConv:
    # Issue #163 review (rev item 1). The compiler inserts `nnkHiddenCallConv`
    # for an implicit converter call. The one this engine actually needs to
    # parse is the `varargs[string, `$`]` element conversion `echo`/
    # `debugEcho`/etc. apply to every non-string argument: `echo(x)` for
    # `x: int` types the varargs array element as
    # `HiddenCallConv(Sym "$", Sym "x")` (confirmed via a `treeRepr` probe).
    # Without this arm, ANY SUT containing `echo(someInt)` failed to parse
    # at all (`feUnsupportedExprKind`), regardless of anything else in the
    # program.
    #
    # This is deliberately NOT a blind pass-through like the hidden-conversion
    # arm above: the result sits in a slot `classifyType` reports as
    # `itString` (here, an element of the `varargs[string]` array literal
    # feeding the opaque call) -- unwrapping to the bare int operand would
    # smuggle an itInt-typed IR value into a string-sorted slot, corrupting
    # whatever sort the walker allocates for it. Instead this reuses the SAME
    # `$`-conversion lowering the explicit `nnkPrefix`/`nnkCall` sites below
    # already apply (S10a/A7-S2: `iekIntToStr`/`iekRuneToStr`), so the result
    # is a genuinely string-typed IR value regardless of who consumes it --
    # sound even in the hypothetical where a hidden `$`-conversion's result
    # were actually used, not just handed to an opaque sink. Only the
    # well-understood `$`-conversion shape is handled; any OTHER implicit
    # converter (e.g. a user-defined `converter` proc) falls through to the
    # ordinary catch-all decline rather than being guessed at.
    # RFC-0005 S8c: ...except that a USER converter (or a user `$` the
    # compiler inserted) is a routine the parser can walk: it is a routine
    # call like any other, so it no longer declines, and a user `$` is no
    # longer mistaken for `system.$`.
    if n.len == 2 and isUserCallee(n[0]):
      return parseRoutineCallExpr(n, n[0], preamble, ctx)
    if n.len == 2 and n[0].kind == nnkSym and n[0].strVal == "$":
      if isRuneTyped(n[1]):
        mkStrOp(iekRuneToStr, "$rune", @[parseExpr(n[1], preamble, ctx)])
      else:
        let opndTy = classifyType(n[1]).ty.kind
        if opndTy == itInt:
          mkStrOp(iekIntToStr, "$", @[parseExpr(n[1], preamble, ctx)])
        elif opndTy in {itFloat32, itFloat64}:
          mkStrOp(iekStrUnsupported, "$float", @[])
        else:
          let dummyTy = classifyType(n).ty
          preamble.add ctx.declineAtSite(
            feUnsupportedExprKind,
            "CR-2a: unsupported expression kind " & $n.kind &
                   " -- hidden `$`-conversion of a " & $opndTy &
                   " operand in `" & n.repr &
                   "` (feUnsupportedExprKind)",
            "CR-2a: unsupported hidden `$`-" &
                                        "conversion operand (feUnsupportedExprKind)")
          let dummy = zeroValueForType(dummyTy)
          if dummy != nil: dummy else: mkIntLit(0)
    else:
      let dummyTy = classifyType(n).ty
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        "CR-2a: unsupported expression kind " & $n.kind & " in `" &
               n.repr & "` — not in the supported expression fragment",
        "CR-2a: unsupported expression kind " &
                                    $n.kind & " (feUnsupportedExprKind)")
      let dummy = zeroValueForType(dummyTy)
      if dummy != nil: dummy else: mkIntLit(0)
  of nnkAddr:
    # RFC-0005 S8ax: `addr x` of a routine's variable is its address cell.
    # Any other `addr` (a field, an element, a module-level variable) has
    # no cell: the catch-all's decline, message for message.
    let x = addrCellLocal(n)
    if x != nil:
      return lowerAddrCell(n, x, preamble, ctx)
    # RFC-0005 S8be: `addr s[i]` of a routine's seq is its element cell.
    let el = elemCellOf(n)
    if el.root != nil:
      return lowerElemCell(n, el.root, el.idx, preamble, ctx)
    let dummyTy = classifyType(n).ty
    preamble.add ctx.declineAtSite(
      feUnsupportedExprKind,
      "CR-2a: unsupported expression kind " & $n.kind & " in `" &
             n.repr & "` — not in the supported expression fragment",
      "CR-2a: unsupported expression kind " &
                                  $n.kind & " (feUnsupportedExprKind)")
    let dummy = zeroValueForType(dummyTy)
    if dummy != nil: dummy else: mkIntLit(0)
  of nnkDerefExpr, nnkHiddenDeref:
    # RFC-0005 S8ac: a `var` formal's own indirection is its value (the ref
    # itself for `var ref T`), not a heap read.
    if isVarIndirection(n):
      return parseExpr(n[0], preamble, ctx)
    # Phase 15 R1 (ADR-0010). `p[]` — a ref/ptr dereference. The typed AST emits
    # an explicit `nnkDerefExpr` (or a compiler-inserted `nnkHiddenDeref`) whose
    # operand `n[0]` is the ref/ptr expression. When that operand classifies as a
    # genuine `ref T`/`ptr T`, A-normalise into an `isDeref` stmt (the walker
    # lowers it to a GROUND `select(path.heaps[typeId], p)`); a fresh let binds
    # the dereffed value. (Before R1 a `nnkHiddenDeref` was a no-op unwrap because
    # ref/ptr were unwrapped to the pointee at classify time; Cluster R restores
    # the real indirection, so we must materialise the heap read here.)
    # Phase 15 R8b (ADR-0010). For a `var ref T` / `var ptr T` PARAMETER, the
    # deref `p[]` presents as `nnkDerefExpr(nnkHiddenDeref(sym))` — the inner
    # `nnkHiddenDeref` is the lvalue (`var`-ness) indirection, NOT a real ref
    # deref. `classifyType` of that hidden-deref unwraps to the POINTEE (int),
    # which would defeat the itRef detection below and route to the value-unwrap
    # `else` arm (yielding a bogus deref-temp). Strip that ONE var-level
    # hidden-deref so `operand` is the ref/ptr symbol whose classify is itRef.
    var operand = n[0]
    if operand.kind == nnkHiddenDeref and operand.len == 1 and
       classifyType(operand[0]).ty.kind in {itRef, itPtr}:
      operand = operand[0]
    let opCls = classifyType(operand)
    case opCls.ty.kind
    of itRef, itPtr:
      let isPtr = opCls.ty.kind == itPtr
      let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
      let ptrIR = parseExpr(operand, preamble, ctx)
      if wholeObjectPointee(pointeeTy):
        # RFC-0005 S8ar. `p[]` of an object is the object of its fields, each
        # read from its own field heap -- the cells `p.f` reads and writes.
        # A whole-pointee heap for an object would be a second, unrelated
        # store of the same fields.
        var elems: seq[IRExpr]
        for i, fname in pointeeTy.fieldNames:
          let synth = freshSynth(ctx, "deref")
          preamble.add mkFieldDeref(synth, ptrIR, pointeeTy.fields[i], pointeeTy,
                                    fname, isPtr)
          elems.add mkVar(synth)
        return mkTupleLit(elems, pointeeTy)
      let synth = freshSynth(ctx, "deref")
      let stmt = if isPtr: mkPtrDeref(synth, ptrIR, pointeeTy)
                 else:     mkDeref(synth, ptrIR, pointeeTy)
      preamble.add stmt
      mkVar(synth)
    else:
      # Not a ref/ptr operand (e.g. a compiler-inserted hidden deref over an
      # already-unwrapped value): preserve the pre-R unwrap behaviour.
      parseExpr(n[n.len - 1], preamble, ctx)
  of nnkCheckedFieldExpr:
    # `s.field` on a variant object — the runtime check is over the
    # discriminator; symex just lowers the inner dot-expr.
    parseExpr(n[0], preamble, ctx)
  of nnkInfix:
    # RFC-0005 S8c: an operator whose head resolved to a USER routine (`+` on
    # a `distinct int`, `==` on an object, `<` with custom semantics, ...) is
    # a routine call, not the builtin `binopForInfix` models by the operator's
    # spelling. The typed AST puts the resolved symbol at `n[0]` -- including
    # for `>`/`>=`/`!=`, which the compiler rewrites through the user's
    # `<`/`<=`/`==`. `{.borrow.}` operators stay on `borrowIntercept` below.
    if isUserCallee(n[0]):
      return parseRoutineCallExpr(n, n[0], preamble, ctx)
    # RFC-0005 S8bq (item 2): `+ - * <= < ==` on builtin sets (`>=`, `>`
    # and `!=` reach here as `<=`, `<` and `not ==`). Typed operators only:
    # an untyped operand (the isolation entry point) has no type to read.
    if n.len == 3 and n[0].kind == nnkSym and
       isBuiltinNamed(n[0], ["+", "-", "*", "<=", "<", "=="]) and
       n[1].typeKind != ntyNone and classifyType(n[1]).ty.kind == itBitSet:
      let setTy = classifyType(n[1]).ty
      let op = case n[0].strVal
               of "+": bsoUnion
               of "-": bsoDiff
               of "*": bsoInter
               of "<=": bsoLe
               of "<": bsoLt
               else: bsoEq
      let l = parseAtomicOperand(n[1], preamble, ctx)
      let mark = preamble.len
      let r = parseAtomicOperand(n[2], preamble, ctx)
      keepInlineRaiseOrder(l, n[1], mark, preamble, ctx)
      return mkBitSet(op, @[l, r], setTy)
    # Phase 15 S8: `&` string concatenation. Intercept BEFORE binopForInfix
    # (which has no `&` case and would error). Only fire when BOTH operands
    # classify as `itString` — `s & t`, `s & "lit"`, `"lit" & s`. This guard
    # leaves the seq-concat / any-other-type `&` path untouched (those operands
    # are not itString, so they fall through to binopForInfix as before).
    # Chained `a & b & c` is left-associative: the typed AST nests it as
    # `(a & b) & c`, so each `&` is its own binary node and recursion on the
    # operands handles the chain naturally.
    if n[0].strVal == "&" and
       classifyType(n[1]).ty.kind == itString and
       classifyType(n[2]).ty.kind == itString:
      let (lhs, rhs) = parseOperandPair(n[1], n[2], preamble, ctx)  ## A2a chokepoint (string-concat); RFC-0005 S8ax order
      return mkStrOp(iekStrConcat, "&", @[lhs, rhs])
    # Phase 15 G5: a `{.borrow.}` operator on a `distinct T`. In the typed AST
    # `m1 + m2` (with `proc \`+\`(a,b: Meters): Meters {.borrow.}`) is an
    # `nnkInfix` whose `n[0]` is the borrow proc SYMBOL. Detect it and route
    # through the borrow path (eject operands to base, apply base op, re-box
    # arithmetic) rather than `binopForInfix` + `mkBinop`. The base operator is
    # `binopForInfix(operatorName)`. A borrow proc has no real body, so it must
    # NOT be body-parsed.
    block borrowIntercept:
      if n[0].kind == nnkSym:
        let bi = borrowInfoFor(n[0])
        if bi.isBorrow:
          let bop = binopForInfix(n[0].strVal)
          let (l, r) = parseOperandPair(n[1], n[2], preamble, ctx)  ## A2a chokepoint (borrow intercept); RFC-0005 S8ax order
          return mkBorrowOp(bop, l, r, bi.returnsDistinct, bi.distinctTy)
    # Phase 15 R5 (Cluster R). A `nil` ref/ptr comparison `p == nil` / `nil == p`
    # (`==`/`!=`). One operand is an `nnkNilLit`; the OTHER is the ref/ptr whose
    # type supplies the pointee for the per-sort `nilConst`. Lower the nil side to
    # an `iekNil(pointee)` (built from the non-nil operand's classified `itRef`/
    # `itPtr` type) so the walker's `refEq` decides it as a ground `Ref_T`
    # equality. Intercept BEFORE `binopForInfix`+`parseExpr`, which has no
    # nnkNilLit arm.
    # Phase 16 D1a (CR-22 fix): Two-level classifier for nil comparisons so that
    # BOTH `p: ref int` / `p: ref Point` (inline ref params, itRef from
    # classifyType) AND `n.next` (a DotExpr that returns a ref-typed field value —
    # classifyType UNWRAPS `Node = ref object` to itTuple) are handled correctly.
    #
    # Level 1: `classifyType(refNode)` — the original classifier. Correctly returns
    # itRef/itPtr for INLINE ref params (`p: ref int`, `q: ref Point`). For a
    # NAMED `ref object` type (e.g. `type Node = ref object`), `classifyType`
    # UNWRAPS the alias to the object body, returning itTuple — not itRef.
    #
    # Level 2 (fallback, NON-bare-symbol only): `classifyFieldType(refNode.getTypeInst)`
    # — the ref-aware field classifier. Recognizes named `ref object` aliases and
    # returns itRef. Applied ONLY when the expression is NOT a bare symbol (i.e. a
    # derived expression like `n.next`). A bare symbol `n: Node` is VALUE-MODELLED
    # by the engine (classifyType returns itTuple deliberately — the walker allocates
    # it as svTuple, not svRef), so a nil comparison on a bare value-modelled param
    # is unsupported and must NOT generate a nil IR (it would crash at walk time when
    # comparing svTuple ≠ svRef). Non-symbol derived expressions (`n.next`, a
    # field-split heap lookup) are always svRef-typed and ARE safely comparable to nil.
    if n[0].strVal in ["==", "!="] and
       (n[1].kind == nnkNilLit or n[2].kind == nnkNilLit):
      let op = binopForInfix(n[0].strVal)
      let nilIsLhs = n[1].kind == nnkNilLit
      let refNode  = if nilIsLhs: n[2] else: n[1]
      # Level 1: classifyType — correct for inline ref params; unwraps named ref objects.
      var refCls = classifyType(refNode)
      # Level 2 fallback: only for derived (non-bare-symbol) expressions.
      # A bare nnkSym/nnkIdent that classifies as itTuple is value-modelled — skip.
      if refCls.ty.kind notin {itRef, itPtr} and
         refNode.kind notin {nnkSym, nnkIdent}:
        refCls = classifyFieldType(refNode.getTypeInst)
      if refCls.ty.kind in {itRef, itPtr}:
        let refIR = parseAtomicOperand(refNode, preamble, ctx)  ## A2a chokepoint (nil-compare, non-nil side)
        let nilIR = mkNil(refCls.ty)
        return (if nilIsLhs: mkBinop(op, nilIR, refIR)
                else:        mkBinop(op, refIR, nilIR))
      # RFC-0005 S8z: a proc value against `nil` (`f == nil` on a closure a
      # callee returned). The walker has no nil closure, so this is a scoped
      # decline on the path that reaches it, with a bool placeholder. Without
      # this arm `nil` fell to the generic unsupported-literal dummy (an int
      # 0), and the walker compared an `svClosure` against it: a
      # `weInternalWalkerFault` whenever the closure path was walked first.
      if refCls.ty.kind == itUninterp and refCls.ty.uninterpName == "__closure":
        preamble.add ctx.declineAtSite(
          ceUnsupportedHof,
          "a proc value compared with nil in `" & n.repr &
            "` is not modelled -- degraded to sxUnknown (ceUnsupportedHof)",
          "proc value compared with nil (ceUnsupportedHof)")
        return mkBoolLit(false)
    # v64 (§0 clause (b), chapulin round-3 natural-form probe): an infix the
    # DSL does not model — e.g. `a .. b` building an HSlice VALUE in a call-
    # argument position, which the bracket-slice interceptors never see —
    # used to fall into `binopForInfix`'s macro-time `error()`, aborting the
    # whole file's compilation (observed on the real `parseTftpUri`).
    # Degrade CR-2a-style instead: classified parse error (anchored at the
    # marker; RFC-0005 S9 reads it as a run taint only if a walked path
    # reaches the marker -- was the whole-run `capForcedUnknown`), an
    # `mkUnsupported` stmt for the SND-1 walker taint, and a typed zero
    # dummy so parsing continues.
    if n[0].strVal notin ["+", "-", "*", "div", "/", "mod", "==", "!=",
                          "<", "<=", ">", ">=", "and", "or", "xor",
                          "shl", "shr"]:
      let dummyTy = classifyType(n).ty
      preamble.add ctx.declineAtSite(
        feUnsupportedOp,
        "unsupported infix operator `" & n[0].strVal & "` in `" &
               n.repr & "` — degraded to sxUnknown (feUnsupportedOp)",
        "unsupported infix operator `" &
                                   n[0].strVal & "` (feUnsupportedOp)")
      let dummy = zeroValueForType(dummyTy)
      return (if dummy != nil: dummy else: mkIntLit(0))
    let op = binopForInfix(n[0].strVal)
    # Phase 16 D1c: model `and`/`or` short-circuit evaluation.
    # The LHS is always evaluated (hoisted into the outer preamble as usual).
    # The RHS is parsed into a SEPARATE scratch preamble; if that preamble is
    # non-empty (i.e. it contains defect-fork stmts — isVariantField, isIndex,
    # isDeref, …), we wrap the whole RHS block in a boolean-temp guard so the
    # RHS preamble only executes when the LHS value demands it:
    #   and: guard  = `if __sc:   …rhsPreamble…; __sc = rhsIR`
    #   or:  guard  = `if not __sc: …rhsPreamble…; __sc = rhsIR`
    # Fast path (rhsPreamble empty): zero IR overhead — emits the same
    # `mkBinop(bAnd/bOr, lhsIR, rhsIR)` as before D1c.
    # A2b (RFC-parser-normalization #146/#149, D2): classify-first
    # restructure. Pre-A2b this block parsed BOTH operands once, shared,
    # BEFORE branching on `classifyType(n).ty.kind != itBool` — so there was
    # no bitwise-only parse to reroute onto the chokepoint without also
    # touching the boolean short-circuit path. The boolean-vs-bitwise
    # decision needs only the typed surface node `n` (not either operand's
    # parse), so it is now made FIRST, and the two semantics get genuinely
    # separate parse paths below. Branch exclusivity then makes cross-branch
    # leakage — chokepoint atomization reaching a short-circuit operand, or
    # D1c's guard machinery reaching a bitwise one — structurally
    # impossible, satisfying constraint 1 by construction rather than by
    # a case-by-case check.
    #
    # UNTYPED carve-out: `classifyType` hard-errors ("node has no type") on
    # an untyped node. `dsl_parser.nim`'s own isolation entry point
    # (`parseExpr(n: NimNode): IRExpr`, ADR-0002, :4780, exercised by
    # `tsymex_phase1_dsl.nim`) feeds genuinely untyped AST fixtures straight
    # into this parser, so an untyped and/or node must route to the BOOLEAN
    # path below without ever calling `classifyType(n)` — the pre-v64
    # behavior for that isolation entry point, which owns no bitwise
    # fixtures and never sees short-circuit-unsound hoisting because that
    # path never calls `parseAtomicOperand`.
    #
    # DISAMBIGUATOR: NOT `n.typeKind == ntyNone` (the idiom `parseAtomicOperand`,
    # :1247, uses elsewhere) — probed empirically (`scratchpad/
    # probe_typekind.nim`/`probe_typekind2.nim`) and found UNSOUND
    # specifically for `and`/`or`: the compiler treats these as magic
    # boolean control-flow operators and assigns the untyped INFIX node
    # itself a bogus non-`ntyNone` `typeKind` (observed `ntyCString`) even
    # when genuinely unresolved — `n.typeKind != ntyNone` would (and,
    # pre-fix, did) let an untyped and/or node reach `classifyType(n)` and
    # hard-error, reproducing issue #156 rather than fixing it. The RELIABLE
    # signal is the OPERATOR node's own kind: `n[0]` (the `and`/`or` ident)
    # resolves to `nnkSym` only on the production (typed-macro) path, where
    # overload resolution has bound it to a concrete proc symbol (confirmed
    # `nnkSym`/`ntyProc` by probe); the untyped isolation path leaves it a
    # bare, unresolved `nnkIdent` (confirmed `nnkIdent`/`ntyNone` — `n[0]`
    # itself is NOT subject to the same bogus-typeKind anomaly as `n` or its
    # operands). `isBooleanShortCircuitInfix` now shares this SAME signal —
    # unified onto `isResolvedBoolAndOr` (M3, RFC #146 round 1) — so the
    # boolean-vs-bitwise question has exactly one sound answer across both
    # call sites; see that proc's doc comment for why the previously-dormant
    # `n.typeKind` precondition it carried was never actually reachable
    # through natural source, making this a hygiene unification rather than
    # a behavior fix.
    if op in {bAnd, bOr}:
      if isResolvedBitwiseAndOr(n):
        # BITWISE and/or (v64 chapulin catalog #3 residual: Nim spells the
        # BOOLEAN and BITWISE forms with the SAME identifiers, so `op in
        # {bAnd, bOr}` alone also matches an INT-typed infix, e.g.
        # `(hi shl 8) or lo` on uint16). Bitwise and/or has NO short-circuit
        # semantics in Nim — the RHS always evaluates — so both operands
        # atomize through the A2a chokepoint into the OUTER preamble
        # unconditionally: no short-circuit guard could ever apply, and this
        # is exactly the faithful lowering the pre-restructure
        # `preamble.add rhsPreamble` gave for this same family.
        let (l, r) = parseOperandPair(n[1], n[2], preamble, ctx)  ## A2b chokepoint (bitwise and/or); RFC-0005 S8ax order
        mkBinop(op, l, r)
      else:
        # A2b EXCLUSION (boolean and/or, constraint 1): itBool, or untyped —
        # carve-out above. D1c's short-circuit machinery, VERBATIM.
        # `parseAtomicOperand` MUST NEVER be used anywhere in this path —
        # plain `parseExpr` owns both operands, exactly as before this
        # restructure. Post-restructure, branch exclusivity with the
        # BITWISE arm above makes this exclusion structural, not incidental.
        #
        # RFC-0005 S8t: the whole same-operator chain is flattened and
        # lowered with ONE guard temporary whose guards nest
        # (`lowerShortCircuitParts`). Each operand is parsed into its own
        # scratch preamble, in source order. Fast path (every non-first
        # operand pure: nothing hoisted, no inline defect fork -- R16-2b's
        # iekConvFloatToInt, R16-3's bDiv/bMod): zero IR overhead, the flat
        # `mkBinop` chain as before D1c. Pre-S8t each binary node had its
        # own chained temporary, which forked 2^(n-1) paths over n operands.
        var operands: seq[NimNode]
        flattenShortCircuitChain(n, n[0].strVal, operands)
        var parts: seq[ShortCircuitPart]
        for o in operands:
          var pre: seq[IRStmt]
          let ir = parseExpr(o, pre, ctx)  ## A2b EXCLUSION (boolean and/or operand)
          parts.add (pre: pre, ir: ir)
        lowerShortCircuitParts(op, parts, preamble, ctx)
    else:
      # A2a chokepoint: the clean general infix family (comparisons,
      # arithmetic, shl/shr, xor — never bAnd/bOr, which are handled entirely
      # above in the `if op in {bAnd, bOr}` block and never fall through here;
      # constraint 1 is satisfied structurally by this branch's exclusivity).
      let (l, r) = parseOperandPair(n[1], n[2], preamble, ctx)  ## A2a chokepoint (general infix); RFC-0005 S8ax order
      mkBinop(op, l, r)
  of nnkPrefix:
    # RFC-0005 S8c: a user prefix operator (`-`/`not`/`$`/`@` on a user type)
    # is a routine call, not the builtin its spelling names.
    if isUserCallee(n[0]):
      return parseRoutineCallExpr(n, n[0], preamble, ctx)
    let op = n[0].strVal
    case op
    of "not":
      # A2a chokepoint, with constraint 1's uNot exclusion: eagerly hoisting
      # a boolean short-circuit `a and b`/`a or b` operand under `not` would
      # evaluate the RHS unconditionally — the exact D1c violation. Leave a
      # boolean and/or operand un-atomized (plain parseExpr, D1c's own
      # handling fires when `not`'s operand is walked); a bitwise not/neg
      # operand (or anything else) atomizes normally.
      let operand = n[1]
      if isBooleanShortCircuitInfix(operand):
        mkUnop(uNot, parseExpr(operand, preamble, ctx))  ## A2a exclusion (not-over-bAnd/bOr, constraint 1)
      else:
        mkUnop(uNot, parseAtomicOperand(operand, preamble, ctx))  ## A2a chokepoint (unary not)
    of "$":
      # Phase 15 S10a: `$n` (system.`$`) on an `itInt` operand → `iekIntToStr`
      # (Z3 `Z3_mk_int_to_str`). In the typed AST `$n` is an `nnkPrefix` (NOT an
      # nnkCall), so it is intercepted here. Only an int operand routes to the
      # conversion — `$float`/`$bool`/etc. are deferred (S10b / future).
      # Phase 16 A7-S2: `$r` where r: Rune → `iekRuneToStr` (UTF-8 byte string
      # via runeToUtf8Sym). Must intercept BEFORE the itInt check: after S1, Rune
      # classifies to itInt, so `classifyType(n[1]).ty.kind == itInt` is true for
      # BOTH a plain int and a Rune — the Rune case must be caught first by
      # checking the ACTUAL Nim type via isRuneTyped. A non-Rune distinct int
      # falls through to the itInt branch (decimal), never the Rune UTF-8 branch.
      if isRuneTyped(n[1]):
        return mkStrOp(iekRuneToStr, "$rune", @[parseExpr(n[1], preamble, ctx)])
      let opndTy = classifyType(n[1]).ty.kind
      if opndTy == itInt:
        mkStrOp(iekIntToStr, "$", @[parseExpr(n[1], preamble, ctx)])
      elif opndTy in {itFloat32, itFloat64}:
        # Phase 15 S10b: Z3 String theory has NO float↔string conversion, so
        # `$f` (a float stringified) routes to a classified `seUnsupportedStringOp`
        # → `sxUnknown` (reusing the S9 `iekStrUnsupported` mechanism with opName
        # "$float"; Invariant 3 — never a crash/silent UNSAT). The operand is
        # dropped (the residual `lower` arm raises the classified error).
        mkStrOp(iekStrUnsupported, "$float", @[])
      else:
        error("symex: `$` is only modeled for int operands (S10a); `$" &
              $classifyType(n[1]).ty & "` is deferred", n)
    of "-":
      # Phase 15 F2: fold `-<float-literal>` into a negated float literal at
      # parse time (covers -0.0 / -Inf) so the walker sees a literal, not uNeg.
      if n[1].kind in {nnkFloatLit, nnkFloat32Lit, nnkFloat64Lit}:
        mkFloatLit(-n[1].floatVal, if n[1].kind == nnkFloat32Lit: 32 else: 64)
      else:
        mkUnop(uNeg, parseAtomicOperand(n[1], preamble, ctx))  ## A2a chokepoint (unary minus)
    of "@":
      # Phase 15 C4: a seq literal `@[a, b, c]` (incl. empty `@[]`). The typed
      # form is `Prefix(Sym "@", Bracket)`. Lower to a CONCRETE-length `svSeq`
      # so a downstream HOF can take the bounded inline path. The element type
      # comes from the whole expression's `seq[T]` type (works for `@[]` too).
      if n[1].kind != nnkBracket:
        error("symex: unsupported `@` operand (expected a seq literal `@[..]`)", n)
      # RFC-0005 S8ax: elements filled in order (`orderOperands`).
      let elems = parseOrderedArgs(n[1], 0, preamble, ctx, omElements)
      # Recover the element IRType. Prefer the seq's own type; fall back to the
      # first element's classified type for a non-empty literal.
      let seqCls = classifyType(n)
      if seqCls.ty.kind != itSeq and n[1].len == 0:
        error("symex: cannot infer element type of empty `@[]`", n)
      let elemTy = if seqCls.ty.kind == itSeq: seqCls.ty.seqElemTy
                   else: classifyType(n[1][0]).ty
      mkSeqLit(elems, elemTy)
    else:
      error("symex: unsupported prefix operator `" & op & "`", n)
  of nnkBracket:
    # Static array literal `[a, b, c]`. The element type comes from
    # the first element; uniform homogeneity is enforced by Nim.
    # RFC-0005 S8ax: elements filled in order (`orderOperands`).
    let elems = parseOrderedArgs(n, 0, preamble, ctx, omElements)
    let elemCls = classifyType(n[0])
    mkArrayLit(elems, elemCls.ty)
  of nnkBracketExpr:
    # Tuple positional access (`t[0]`) or array index (`arr[i]`).
    # Decide via the LHS's classified type.
    let lhsCls = classifyType(n[0])
    # Round-6 N15: `classifyType(n[0])` classifies the receiver's STATIC Nim
    # type fresh — it does not carry the per-field `isUnsupportedFieldPlaceholder`
    # annotation `classifyObjectRecordFields` bakes into the OBJECT's own
    # field table, so `lhsCls.ty` can never be recognised as a placeholder
    # directly. Detect the decline the SAME way `declineUnsupportedFieldRead`
    # reports it: `parseExpr(n[0])`, below, already runs the correct
    # itTuple/itVariant/itMultiVariant field-placeholder dispatch (the
    # `nnkDotExpr` arm above) and, when the receiver is a declined
    # placeholder, hands back a fake empty-seq-literal stand-in as `objIR`
    # carrying `seqLitDeclinedPlaceholder: true` (the parse-time twin of
    # `SymVal.isUnsupportedFieldPlaceholder`) — inspect what `parseExpr`
    # RETURNED directly, no `ctx.parseErrors` side-channel diff needed.
    let objIR = parseExpr(n[0], preamble, ctx)
    if lhsCls.ty.kind == itSeq and objIR.kind == iekSeqLit and
       objIR.seqLitDeclinedPlaceholder:
      # The receiver read just declined — building `isIndex`/`mkSeqSlice`
      # walk-time IR OVER its fake literal would crash `lowerLeafInExpr`'s
      # side-effect-free-container assertion instead of reporting the SAME
      # classified kind every other placeholder-consuming form (`.len`, a
      # bare read) reports. Stop here: the decline is already recorded (one
      # `ctx.parseErrors` entry, one `mkUnsupported` preamble statement) —
      # hand back a dummy of THIS expression's own result type (the element
      # type for an index, `itSeq` for a slice) instead of consuming the
      # fake literal further.
      let dummy = zeroValueForType(classifyType(n).ty)
      return (if dummy != nil: dummy else: mkIntLit(0))
    case lhsCls.ty.kind
    of itTuple:
      # Index must be a static int literal at the AST level.
      let ixNode = n[1]
      if ixNode.kind notin {nnkIntLit, nnkInt8Lit, nnkInt16Lit,
                             nnkInt32Lit, nnkInt64Lit}:
        error("symex (Phase 4): tuple index must be a literal", ixNode)
      let ix = int(ixNode.intVal)
      let fname = if lhsCls.ty.fieldNames.len > ix:
                    lhsCls.ty.fieldNames[ix]
                  else: ""
      mkField(objIR, ix, fname)
    of itArray:
      # RFC-0005 S8i: Nim wraps the index in a hidden conversion to the
      # array's index type (`arr[i]` is `BracketExpr(arr, HiddenStdConv(i))`)
      # but checks it as an INDEX: `arr[7]` on an `array[5, int]` raises
      # IndexDefect "index 7 not in 0 .. 4", never RangeDefect (probed, c
      # and cpp). `isIndex` forks that; the conversion's range check must
      # not fire as well.
      let arrIR = liftIndexContainer(objIR, lhsCls.ty, preamble, ctx)
      ctx.indexConvPending = n[1].kind in {nnkHiddenStdConv, nnkHiddenSubConv}
      let idxIR = parseExpr(n[1], preamble, ctx)
      ctx.indexConvPending = false
      let synth = freshSynth(ctx, "idx")
      # RFC-0005 S8z: the array's first index (`array[1..3, T]`: 1). It was
      # dropped, so `a[1]` read position 1 -- the second element.
      preamble.add mkIndexStmt(synth, arrIR, idxIR, lhsCls.ty.elemTy, "",
                               arrayIndexLow(n[0]))
      mkVar(synth)
    of itSeq:
      # v67 (dev item 1) / round-6 B1: `data[a..b]` (slice, array-lambda
      # view `iekSeqSlice` UNLESS string-backed) / `data[i]` (index read,
      # A-normalised `isIndex` UNLESS string-backed) — dispatch collapsed
      # into the shared `parseSeqBracketAccess` helper (B1: this arm and
      # the call-form `` `[]`(data, idx) `` arm below can no longer
      # diverge).
      parseSeqBracketAccess(n, n[0], objIR, n[1], lhsCls.ty.seqElemTy,
                             preamble, ctx)
    of itString:
      # Phase 15 S3. `s[i]` (index read) / `s[a..b]` (slice) in bracket-expr
      # form. The slice index is an `nnkInfix(.., a, b)` / `nnkInfix(..<, a, b)`;
      # everything else is a single-byte index. Mirrors the `[]`-call handling
      # in the string-call guard (typed AST emits either shape depending on
      # context). Byte-faithful (ADR-0006): position == Nim byte index.
      let idxNode = n[1]
      if idxNode.kind == nnkInfix and idxNode.len == 3 and
         idxNode[0].kind in {nnkSym, nnkIdent} and
         isBuiltinNamed(idxNode[0], ["..", "..<"]):
        let loIR = parseStrSliceBound(idxNode[1], objIR, preamble, ctx)
        var hiIR = parseStrSliceBound(idxNode[2], objIR, preamble, ctx)
        if idxNode[0].strVal == "..<":
          hiIR = mkBinop(bSub, hiIR, mkIntLit(1))
        mkStrOp(iekStrSubstr, "[]", @[objIR, loIR, hiIR])
      else:
        let idxIR = parseExpr(idxNode, preamble, ctx)
        mkStrOp(iekStrAt, "[]", @[objIR, idxIR])
    else:
      # v65 (§0 clause (b)): `[]` on an unclassified/unmodeled receiver type
      # used to macro-`error()`, aborting the whole file. CR-2a-style
      # classified degrade instead (parse error + SND-1 taint + typed zero
      # dummy).
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        "`[]` on unsupported type " & $lhsCls.ty & " in `" & n.repr &
               "` — degraded to sxUnknown (feUnsupportedExprKind)",
        "`[]` on unsupported type " & $lhsCls.ty &
                                   " (feUnsupportedExprKind)")
      let dummy = zeroValueForType(classifyType(n).ty)
      return (if dummy != nil: dummy else: mkIntLit(0))
  of nnkDotExpr:
    # Phase 15 R6 (ADR-0010). `p.field` field READ through a `ref object` /
    # `ptr object`. The typed AST is `nnkDotExpr(nnkHiddenDeref(p), field)` (or
    # an explicit `nnkDerefExpr`). When the dereffed operand classifies as a
    # genuine `ref T` / `ptr T` whose pointee is an OBJECT (`itTuple`), lower to a
    # FIELD deref: `select(heap_<objTid>__<field>, p)` over the field-split heap.
    # This MUST run before the `classifyType(n[0])`-based tuple/variant routing
    # below (which would classify the hidden-deref's tuple value and lose the
    # ref address). Inherited fields fall out for free — the field-split heap is
    # keyed by field NAME (unique across the flat layout), and the field TYPE
    # comes from `classifyType(n)` on the whole access node (resolves base + own
    # fields), so no flat-offset arithmetic is needed.
    if n[0].kind in {nnkHiddenDeref, nnkDerefExpr} and n[0].len >= 1:
      let operand = n[0][0]
      var opCls = classifyType(operand)
      # Phase 15 R9 (ADR-0010). RECURSIVE ref-object field access. When the
      # operand is a DERIVED ref-valued expression (a nested `n.next` returning a
      # `Node` ref), `classifyType(n.next)` UNWRAPS to the recursive field's
      # placeholder VALUE type (it does not re-derive "this came from a ref
      # field" from a dot-expr node) — so we must re-classify via
      # `classifyFieldType` (the ref-aware field classifier) to recover the
      # `itRef`/`itPtr`.
      #
      # Cluster H Step C (ADR-0022) KEEPS the `operand.kind notin {nnkSym,
      # nnkIdent}` exclusion — NOT one of the carve-outs actually deleted.
      # Deleting it was considered (per the original H1 brief) but rejected:
      # `classifyType` now correctly classifies a BARE named-ref symbol at
      # Level 1 (itRef for a plain ref-object, itVariant — deliberately, ADR
      # sub-decision #1 — for a ref-VARIANT object), so this fallback is
      # already dead-but-harmless for that case (the `opCls.ty.kind notin
      # {itRef,itPtr}` half of the guard alone would skip it). But
      # `classifyFieldType`/`namedRefPlaceholder` is variant-BLIND (it
      # ref-wraps ANY object pointee, by design — a FIELD pointing to a
      # variant is a legitimate heap address the field-split heap already
      # supports for disc/plain-field reads, ADR-0013). Deleting the bare-sym
      # exclusion would let a bare `p: TreeRef` (`TreeRef = ref object; case
      # kind: …`) — value-modelled to `itVariant` by design — get
      # MISCLASSIFIED to `itRef` here, diverting `p.field` off the
      # already-correct value-modelled `itVariant` field-access arm below and
      # onto the field-split-heap path with an `svVariant` env value where an
      # `svRef` is expected (a Z3-sort-mismatch / walker-crash risk). A bare
      # symbol's classification is `classifyType`'s job alone; keeping this
      # exclusion is what preserves that authority.
      if opCls.ty.kind notin {itRef, itPtr} and operand.kind notin {nnkSym, nnkIdent}:
        let fieldCls = classifyFieldType(operand)
        if fieldCls.ty.kind in {itRef, itPtr}:
          opCls = fieldCls
      if opCls.ty.kind in {itRef, itPtr}:
        let isPtr = opCls.ty.kind == itPtr
        let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
        # `itTuple` → field-split heap deref. `itVariant`/`itMultiVariant` →
        # routed through the SAME field-deref IR (the field type is still
        # well-defined); the walker models the variant `dObjTy` on the
        # ADR-0013 per-arm heaps (a multi-variant per axis, RFC-0005 S8l).
        if pointeeTy.kind in {itTuple, itVariant, itMultiVariant}:
          let fieldName = n[1].strVal
          # The field's type: ref-aware (`classifyFieldType`) so a RECURSIVE
          # `next: Node` field resolves to `tRef(placeholder)` (a `Ref_T`-valued
          # field-split heap entry, R9), while a plain scalar field (e.g. `val`)
          # resolves to its value type as before.
          let fieldTy = classifyFieldType(n).ty
          let ptrIR = parseExpr(operand, preamble, ctx)
          let synth = freshSynth(ctx, "fderef")
          preamble.add mkFieldDeref(synth, ptrIR, fieldTy, pointeeTy,
                                    fieldName, isPtr)
          return mkVar(synth)
    let lhsCls = classifyType(n[0])
    let fieldName = n[1].strVal
    case lhsCls.ty.kind
    of itTuple:
      var ix = -1
      for i, fn in lhsCls.ty.fieldNames:
        if fn == fieldName:
          ix = i; break
      if ix < 0:
        # RFC-0005 S8bn: a field the classified type does not list (a
        # generic object's inherited field: its parent is not classified)
        # declines, where it failed the build.
        preamble.add ctx.declineAtSite(feUnsupportedExprKind,
          siteMsg(n, "field `" & fieldName & "` is not in the type the walk " &
                  "classified (" & $lhsCls.ty & ") (RFC-0005 S8bn; " &
                  "feUnsupportedExprKind)"),
          "a field the classified type does not list (feUnsupportedExprKind)")
        let dummy = zeroValueForType(classifyType(n).ty)
        return (if dummy != nil: dummy else: mkIntLit(0))
      let objIR = parseExpr(n[0], preamble, ctx)
      # Round-6 Bug #2: this field's DECLARED type is a scoped-decline
      # placeholder (`isUnsupportedFieldPlaceholder`) — decline THIS READ
      # instead of building a real accessor over an unmodeled field.
      if isUnsupportedFieldPlaceholder(lhsCls.ty.fields[ix]):
        return declineUnsupportedFieldRead(n, fieldName, lhsCls.ty.fields[ix],
                                           preamble, ctx)
      mkField(objIR, ix, fieldName)
    of itSeq:
      if isBuiltinNamed(n[1], ["len"]):   ## RFC-0005 S8c: not a user `len`
        # Round-6 B1: shared with the call-form `len`/`card` arm below —
        # `parseSeqLenAccess` chooses `iekStrLen` over `mkSeqLen` for a
        # string-backed receiver.
        let objIR = parseExpr(n[0], preamble, ctx)
        parseSeqLenAccess(n[0], objIR, ctx)
      else:
        error(&"symex (Phase 5): unsupported seq accessor `.{fieldName}`", n)
    of itVariant:
      # Phase 11. Three field-access shapes:
      #   * discriminator (cycle 3) → expression-level iekField
      #   * plain shared field (post-cycle-12) → expression-level
      #     iekField; the walker reads from the single shared
      #     SymVal — no fork, no FieldDefect risk.
      #   * arm-specific field (cycle 5) → A-normalised into an
      #     `isVariantField` statement so the walker can fork and
      #     `tFieldDefect` lands on the out-of-arm branch.
      let objIR = parseExpr(n[0], preamble, ctx)
      if fieldName == lhsCls.ty.vDiscName:
        mkField(objIR, 0, fieldName)
      elif fieldName in lhsCls.ty.vPlainFieldNames:
        # Round-6 Bug #2: a PLAIN (shared-across-arms) field can itself carry
        # the scoped-decline placeholder — same treatment as an arm-specific
        # field below.
        let pix = lhsCls.ty.vPlainFieldNames.find(fieldName)
        if isUnsupportedFieldPlaceholder(lhsCls.ty.vPlainFieldTypes[pix]):
          return declineUnsupportedFieldRead(n, fieldName,
            lhsCls.ty.vPlainFieldTypes[pix], preamble, ctx)
        mkField(objIR, 0, fieldName)
      else:
        var matchingTags: seq[int]
        var fieldTy: IRType = nil
        for arm in lhsCls.ty.vArms:
          let ix = arm.fieldNames.find(fieldName)
          if ix >= 0:
            matchingTags.add arm.tagOrdinal
            if fieldTy == nil:
              fieldTy = arm.fieldTypes[ix]
        if matchingTags.len == 0:
          error(&"symex Phase 11: field `{fieldName}` not present " &
                &"in any arm of `{lhsCls.ty}`", n)
        # Round-6 Bug #2: an ARM-SPECIFIC field whose declared type is the
        # scoped-decline placeholder — decline THIS READ (classified,
        # path-scoped taint) instead of emitting `isVariantField`. This is
        # the HONEST DEGRADE behavior: reading an unsupported field on
        # whichever arm(s) carry it degrades only the paths that actually
        # take this read; untouched arms/fields (the POISON-GONE behavior)
        # are unaffected because `allocateSym` never raises for the
        # placeholder (`runtime.nim`'s `itUninterp` arm).
        if isUnsupportedFieldPlaceholder(fieldTy):
          return declineUnsupportedFieldRead(n, fieldName, fieldTy, preamble, ctx)
        let synth = freshSynth(ctx, "vf")
        preamble.add mkVariantFieldStmt(
          synth, objIR, fieldName, fieldTy, matchingTags)
        mkVar(synth)
    of itMultiVariant:
      # Phase 14 cycle A1c slice 2. Axis-aware field access on an
      # itMultiVariant value. Three shapes:
      #   1. Plain shared field → expression-level iekField (no fork).
      #   2. Axis discriminator (matching a vDiscName) → iekField.
      #   3. Arm-specific field → walk each axis's arms, find the
      #      owning axis, emit `isVariantField` with that axis's tags
      #      as matchingTags. The walker resolves the axis at
      #      lowering time via `recv`'s svMultiVariant.
      let objIR = parseExpr(n[0], preamble, ctx)
      let plainIx = lhsCls.ty.mvPlainFieldNames.find(fieldName)
      var isDiscOrPlain = plainIx >= 0
      if not isDiscOrPlain:
        for ax in lhsCls.ty.mvAxes:
          if fieldName == ax.discName: isDiscOrPlain = true; break
      if isDiscOrPlain:
        # Round-6 Bug #2: a PLAIN (shared-across-axes) field can itself
        # carry the scoped-decline placeholder (a disc field never can —
        # always itInt). Same treatment as itVariant's plain-field arm above.
        if plainIx >= 0 and isUnsupportedFieldPlaceholder(lhsCls.ty.mvPlainFieldTypes[plainIx]):
          return declineUnsupportedFieldRead(n, fieldName,
            lhsCls.ty.mvPlainFieldTypes[plainIx], preamble, ctx)
        mkField(objIR, 0, fieldName)
      else:
        # Arm-specific: find the owning axis.
        var matchingTags: seq[int]
        var fieldTy: IRType = nil
        for ax in lhsCls.ty.mvAxes:
          for arm in ax.arms:
            let ix = arm.fieldNames.find(fieldName)
            if ix >= 0:
              matchingTags.add arm.tagOrdinal
              if fieldTy == nil:
                fieldTy = arm.fieldTypes[ix]
          if matchingTags.len > 0: break
        if matchingTags.len == 0:
          error("symex Phase 14: field `" & fieldName & "` not " &
                "present in any axis of `" & $lhsCls.ty & "`", n)
        # Round-6 Bug #2: mirrors itVariant's arm-specific decline above.
        if isUnsupportedFieldPlaceholder(fieldTy):
          return declineUnsupportedFieldRead(n, fieldName, fieldTy, preamble, ctx)
        let synth = freshSynth(ctx, "vf")
        preamble.add mkVariantFieldStmt(
          synth, objIR, fieldName, fieldTy, matchingTags)
        mkVar(synth)
    else:
      # v65 (§0 clause (b)): `.field` on an unclassified/unmodeled type —
      # e.g. an HSlice VALUE flowing into the inlined `system.[]` (`x.a`) on
      # a slice-as-value shape — used to macro-`error()`, aborting the
      # whole file (the "`.` on unsupported type uninterp[HSlice[int,int]]"
      # class). CR-2a-style classified degrade instead.
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        "`.` on unsupported type " & $lhsCls.ty & " in `" & n.repr &
               "` — degraded to sxUnknown (feUnsupportedExprKind)",
        "`.` on unsupported type " & $lhsCls.ty &
                                   " (feUnsupportedExprKind)")
      let dummy = zeroValueForType(classifyType(n).ty)
      return (if dummy != nil: dummy else: mkIntLit(0))
  of nnkCurly:
    # RFC-0005 S8bq (item 2): a set literal as a builtin set value. Any other
    # curly (a table constructor's `{k: v}` reaches its own arm first) is the
    # catch-all's decline.
    let setTy = if n.typeKind != ntyNone: classifyType(n).ty else: nil
    if setTy != nil and setTy.kind == itBitSet:
      return parseBitSetLit(n, setTy, preamble, ctx)
    let dummyTy = classifyType(n).ty
    preamble.add ctx.declineAtSite(
      feUnsupportedExprKind,
      "CR-2a: unsupported expression kind " & $n.kind & " in `" &
             n.repr & "` — not in the supported expression fragment",
      "CR-2a: unsupported expression kind " &
                                  $n.kind & " (feUnsupportedExprKind)")
    let dummy = zeroValueForType(dummyTy)
    if dummy != nil: dummy else: mkIntLit(0)
  of nnkCallStrLit:
    # RFC-0005 S8bq (item 3): `re"..."` / `rex"..."` outside a regex call.
    if regexCtorCall(n) != nil:
      return parseRegexCtor(n, preamble, ctx)
    let dummyTy = classifyType(n).ty
    preamble.add ctx.declineAtSite(
      feUnsupportedExprKind,
      "CR-2a: unsupported expression kind " & $n.kind & " in `" &
             n.repr & "` — not in the supported expression fragment",
      "CR-2a: unsupported expression kind " &
                                  $n.kind & " (feUnsupportedExprKind)")
    let dummy = zeroValueForType(dummyTy)
    if dummy != nil: dummy else: mkIntLit(0)
  of nnkCall:
    if isMarkerCall(n):
      error("symex: marker call `" & n[0].repr & "` used in expression " &
            "position; markers are statements only", n)
    if isProcFieldCall(n):
      return procFieldCallIR(n, preamble, ctx).e   ## RFC-0005 S8bn
    let calleeSym = n[0]
    if calleeSym.kind != nnkSym and calleeSym.typeKind == ntyProc:
      # RFC-0005 S8be: a call through a proc-valued expression that is not
      # a variable (`t.f()`, a closure in a returned tuple): bind the
      # closure to a temporary, as `let g = t.f; g()` does. It was a
      # compile-time error.
      let cIR = parseExpr(calleeSym, preamble, ctx)
      let tmp = freshSynth(ctx, "clo")
      preamble.add mkLet(tmp, classifyType(calleeSym).ty, cIR)
      # RFC-0005 batch 4: through S8bh's `closureCallIR`, so a `var` formal's
      # write and an `addr` actual take effect (they were dropped: S8bh's
      # item 1 through this arm, a false `sxSat`).
      return closureCallIR(n, calleeSym, tmp, preamble, ctx, ordered = true).e
    if calleeSym.kind != nnkSym:
      error(&"symex: cannot resolve callee `{n[0].repr}` in untyped " &
            "context; expression-position calls require the full macro flow.",
            n)
    # RFC-0005 S8c: resolve by SYMBOL before any builtin-by-name model below
    # gets a look. A user routine named `len`/`contains`/`$`/`parseInt`/
    # `abs`/... is not that builtin; it is walked like any other user call.
    if isUserCallee(calleeSym):
      return parseRoutineCallExpr(n, calleeSym, preamble, ctx)
    # RFC-0005 S8bq: a `re` / `rex` constructor, before
    # `ensureProcRegistered` walks it (see `parseRegexCtor`).
    if regexCtorCall(n) != nil:
      return parseRegexCtor(n, preamble, ctx)
    # RFC-0005 S8bi: the seq constructors, before `ensureProcRegistered`
    # gets the generic magic (see `parseSeqNew`).
    if n.len == 2 and isBuiltinNamed(calleeSym, seqNewBuiltins):
      let seqTy = classifyType(n).ty
      if seqTy.kind == itSeq:
        return parseSeqNew(calleeSym.strVal, n[1], seqTy, preamble, ctx)
    # Phase 15 E8: the two no-arg exception-query magic intrinsics. Recognised
    # by callee symbol name and intercepted BEFORE the user-proc fall-through
    # (`ensureProcRegistered`), which would otherwise try to parse their stdlib
    # bodies (`if currException == nil: ...`) and choke. They lower at walk time
    # against `w.frame.inFlightExn`, so no operands are carried here.
    if n.len == 1:
      case calleeSym.strVal
      of "getCurrentException":    return mkGetCurrentExn()
      of "getCurrentExceptionMsg": return mkGetCurrentExnMsg()
      else: discard
    # Round-6 A0: `low(T)`/`high(T)` int magics (RFC "Discovered en route (v69
    # round)"). Recognised BEFORE `earlyClosureCallDetect` below, whose
    # `calleeSym.getImpl`/`getTypeInst` probing of a magic-pragma system proc
    # is exactly what produced the discovered walker fault — `rLimb >
    # low(int32)` inside a symex target faulted while the literal spelling
    # proved clean — and before the generic user-proc fall-through
    # (`ensureProcRegistered`), which has no body to fetch for a `.magic`
    # intrinsic. A concrete int-family type argument (`intTyNames`) folds to
    # its literal bit pattern via `mkIntLit`, reusing every downstream
    # literal-width-inference path exactly as if the SUT had spelled the
    # literal directly. Any other argument — a non-int-family type, or a
    # VALUE rather than a type (`low(someArray)`, `typeNodeName` then
    # yielding the variable's own name, never a member of `intTyNames`) — is
    # out of A0's scope and declines cleanly instead of falling through to
    # the fault.
    # S3 adjudication (walker v116): `s.high` (`s: string`) desugars to the
    # SAME `high(s)` call shape A0 intercepts here, but it's a VALUE
    # argument (byte-faithful `len(s)-1`, ADR-0006), not a TYPE argument —
    # A0's `typeNodeName(n[1])` conflated the two (a bare `nnkSym` value
    # yields the VARIABLE's name, e.g. "s", which is trivially "non-int-
    # family" and fell into the decline branch below), permanently
    # occluding the S3-specific `.high` lowering further down this proc
    # (dead code: A0 always `return`ed first). Carve out exactly this
    # shape — string receiver, `high` (never `low`, `.low` on a string is
    # not a modeled op) — and let it fall through unhandled here to reach
    # its real handler; every OTHER low/high shape (type argument OR a
    # value of any other type) keeps A0's original decline-or-fold
    # behavior unchanged, including the fault-prevention this block exists
    # for (see the comment above).
    # Fix-slice item 1 (Critical): `n.len == 2` MUST be checked before ANY
    # `n[1]` touch — a zero-arg user proc named `high` (`proc high(): int`)
    # reaches this call shape with `n.len == 1`, and `n[1]` on it is an
    # out-of-bounds NimNode index at PARSE time (compile-time crash for the
    # whole SUT, not a walk-time decline). Nim's `and` short-circuits left
    # to right, so folding the length check in FIRST — never after —is what
    # makes this safe; the two field-access clauses to its right are only
    # ever evaluated once `n.len == 2` is already known true.
    let isStringHigh = calleeSym.strVal == "high" and n.len == 2 and
                        n[1].typeKind != ntyNone and
                        classifyType(n[1]).ty.kind == itString
    # Fix-slice item 6: `low(s)` (`s: string`) is byte-faithfully the
    # constant 0 (Nim strings/seqs are always 0-indexed) — the symmetric
    # carve-out to `isStringHigh` above. Same `n.len == 2`-first guard
    # against the same zero-arg-proc-named-`low` hazard. Folds directly to
    # a literal (mirrors A0's own `mkIntLit` idiom) rather than falling
    # through to the non-int-family decline below, which used to treat a
    # string receiver's `low` as out of scope even though it never varies.
    let isStringLow = calleeSym.strVal == "low" and n.len == 2 and
                       n[1].typeKind != ntyNone and
                       classifyType(n[1]).ty.kind == itString
    if isStringLow:
      return mkIntLit(0)
    # RFC-0005 S8am (S8z's remainder, item 4): `low(a)`/`high(a)` where `a`
    # is a VALUE of ARRAY type -- the symmetric carve-out to `isStringLow`/
    # `isStringHigh` above, for the OTHER container `A0` never covered
    # (`typeNodeName(n[1])` on an array VALUE yields the variable's own
    # name, never a member of `intTyNames`, so this fell into the
    # non-int-family decline below). Unlike a string's `len`, an array's
    # bounds are part of its TYPE and fixed at compile time (Nim rejects an
    # out-of-declared-range array index at compile time for a literal, and
    # every element lives at a position the walker already knows --
    # `classifyArrayBracket`/S8z), so both fold directly to a literal:
    # `low(a)` is the array's declared first index (`ty.lo`, S8am's own
    # `IRType.lo`), `high(a)` is `ty.lo + ty.size - 1`.
    let isArrayLowHigh = calleeSym.strVal in ["low", "high"] and n.len == 2 and
                         n[1].typeKind != ntyNone and
                         classifyType(n[1]).ty.kind == itArray
    if isArrayLowHigh:
      let arrTy = classifyType(n[1]).ty
      return mkIntLit(if calleeSym.strVal == "low": arrTy.lo
                       else: arrTy.lo + int64(arrTy.size) - 1)
    # RFC-0005 S8at: `zeroDefault(T)` -- what the compiler fills an omitted
    # field of an object constructor with (Nim 2, e.g. the injected
    # `bv: BV(kind: 0, a: zeroDefault(int))` of `BVH(n: n)`) -- and
    # `default(T)`: T's zero (`zeroValueForType`). Its `nnkType` argument
    # fell to the catch-all (`feUnsupportedExprKind`), so every constructor
    # omitting a case-object field declined. A type with no IR zero keeps
    # the fall-through.
    if calleeSym.strVal in ["zeroDefault", "default"] and n.len == 2 and
       n.typeKind != ntyNone and isStdlibDecl(calleeSym):
      let z = zeroValueForType(classifyType(n).ty)
      if z != nil: return z
    if calleeSym.strVal in ["low", "high"] and n.len == 2 and not isStringHigh:
      let tyName = typeNodeName(n[1])
      if tyName in intTyNames:
        return mkIntLit(lowHighIntLit(tyName, wantLow = calleeSym.strVal == "low"))
      else:
        preamble.add ctx.declineAtSite(
          feUnsupportedExprKind,
          siteMsg(n, "A0: `" & calleeSym.strVal & "` on a non-int-" &
                            "family type/value (" & tyName & ") is out of scope"),
          "A0: low/high on non-int-family type " &
                                      tyName & " (feUnsupportedExprKind)")
        # A TYPE-CORRECT literal dummy (CR-2a's own idiom, `dsl_parser.nim`
        # catch-all below), not an unbound-env `mkVar` reference: unlike the
        # P2b "unexpected shape" site this decline mirrors for its taint
        # mechanism, THIS site is genuinely reachable (`low`/`high` on a
        # non-int-family type is ordinary, legal Nim), so a dangling
        # `iekVar` here would be read at walk time and KeyError — exactly
        # the v69 SidecarExt const-fold bug shape this same slice's OTHER
        # fold fixes. SND-1's `isUnsupported` taint (registered above) still
        # forces the eventual verdict to `sxUnknown`; the literal only needs
        # to be well-typed, never correct.
        let dummyTy = classifyType(n).ty
        let dummy = zeroValueForType(dummyTy)
        return (if dummy != nil: dummy else: mkIntLit(0))
    # Phase 15 Cluster C (C2b). Detect a CLOSURE CALL through a proc-valued
    # variable/param (`f(...)` where `f`'s impl is NOT a routine def AND its
    # type is `nnkProcTy`) BEFORE the string-builtin / seq routing below. Those
    # routings call `classifyType(n[1])`, and a closure-call ARG that is itself a
    # closure call (`f(f(v))`) carries no resolvable `getTypeInst`, so classify
    # would raise a non-catchable "node has no type". Routing the closure call
    # here keeps that classify off the closure-arg path entirely. (Mirrors the
    # `closureCallDetect` block below, which now only catches statement-position
    # forms the expression path did not reach.)
    block earlyClosureCallDetect:
      let impl = calleeSym.getImpl
      if impl.kind notin routineShapedForClosureDetect:
        let ti = calleeSym.getTypeInst
        if ti.kind == nnkProcTy:
          # RFC-0005 S8bh: with its `var`/`addr` effects.
          return closureCallIR(n, calleeSym, calleeSym.strVal, preamble, ctx).e
    # Phase 15 C4 (Des-LOW-L3). DSL higher-order calls — `filter`/`map`/`fold`
    # over `seq[T]` taking a CLOSURE arg, dispatched to the walker's HOF
    # handlers (inline / axiom), NOT the generic isCall descent. The interception
    # is GUARDED on the callee's ORIGIN being `std/sequtils` (`owner.strVal ==
    # "sequtils"`): a user-defined same-named proc (e.g. a local `filter[T]`)
    # owns to ITS module and falls through to the normal isCall descent — the
    # regression guard. `foldl`/`foldr` are sequtils TEMPLATES expanded to a loop
    # before this point, so only `filter`/`map` (real procs) reach here in
    # practice; the `fold` op name is handled for a hypothetical closure-fold.
    block hofDispatch:
      if calleeSym.strVal in ["filter", "map", "fold"] and
         calleeSym.kind == nnkSym:
        let owner = calleeSym.owner
        if owner.kind == nnkSym and owner.strVal == "sequtils" and n.len >= 3:
          let seqIR = parseExpr(n[1], preamble, ctx)
          let closureIR = parseExpr(n[2], preamble, ctx)
          # Only a genuine closure arg (an iekLambda) drives the HOF path; a
          # non-lambda 2nd arg means an unexpected shape — fall through.
          if closureIR != nil and closureIR.kind == iekLambda:
            # Result element type: `map` → mapper return; `filter`/`fold` →
            # the input element type (filter preserves; fold accumulates).
            let retCls = classifyType(n)   ## the HOF result type
            let retElemTy =
              if retCls.ty.kind == itSeq: retCls.ty.seqElemTy
              else: retCls.ty   ## fold returns the accumulator scalar
            let initIR = if calleeSym.strVal == "fold" and n.len >= 4:
                           parseExpr(n[3], preamble, ctx)
                         else: nil
            return mkHofCall(calleeSym.strVal, seqIR, closureIR,
                             retElemTy, initIR)
    # Phase 15 Cluster S (S1): `itString`-receiver call routing. This guard
    # runs BEFORE the seq/Table/HashSet builtins so `s.len` on a `string` is
    # NOT mis-routed to `iekSeqLen` (which would lower a Z3String operand into
    # the seq-length path → sort-mismatch crash), and BEFORE the user-proc
    # fall-through (which crashes resolving `getImpl` on a built-in like `len`).
    # In S1 every recognised string op routes to a STUBBED `iekStr*` node that
    # lowers to a classified `seUnsupportedStringOp` (sxUnknown); S2–S11 give
    # each its real Z3 String/Seq/Regex lowering. An UNRECOGNISED string call
    # routes to `iekStrUnsupported` (same clean diagnostic) — never a crash.
    # Phase 15 S5: `xs.join(sep)` where `xs` is a `seq[string]` (e.g. the result
    # of `split`). The receiver type is `seq[string]`/`openArray[string]`, which
    # `classifyType` below rejects, so route `join` to `iekStrJoin` BEFORE the
    # itString-receiver classify. The receiver expr is parsed through the normal
    # path (a `split` receiver lowers to an svSeq[string]); the runtime asserts
    # the receiver is an svSeq[string] and concats with `sep` interleaved.
    if calleeSym.strVal == "join" and n.len == 3:
      let recvIR = parseExpr(n[1], preamble, ctx)
      let sepIR  = parseExpr(n[2], preamble, ctx)
      return mkStrOp(iekStrJoin, "join", @[recvIR, sepIR])
    # Phase 15 S10a: int↔string conversion. `$n` (system.`$`) on an `itInt`
    # operand → `iekIntToStr` (Z3 `Z3_mk_int_to_str`); `parseInt(s)` on an
    # `itString` operand → `iekStrToInt` (digits-path, Z3 `Z3_mk_str_to_int`).
    # Both intercept BEFORE the itString-receiver classify (their operand/result
    # types straddle int and string). `$` only routes here for an int operand —
    # `$float`/`$bool`/etc. fall through unchanged (deferred to S10b / future).
    # Phase 16 A7-S2: `$r` where r: Rune (call form: `` `$`(r) ``). Intercept
    # BEFORE the itInt check for the same reason as the nnkPrefix site above.
    if calleeSym.strVal == "$" and n.len == 2 and isRuneTyped(n[1]):
      return mkStrOp(iekRuneToStr, "$rune", @[parseExpr(n[1], preamble, ctx)])
    if calleeSym.strVal == "$" and n.len == 2 and
       classifyType(n[1]).ty.kind == itInt:
      return mkStrOp(iekIntToStr, "$", @[parseExpr(n[1], preamble, ctx)])
    # RFC-chapulin-hardening M2: `parseBiggestInt(s)` (std/strutils) is routed to
    # the SAME `iekStrToInt` IR as `parseInt(s)`. On this platform `BiggestInt` is
    # a 64-bit int — identical to `parseInt`'s result type — so the two are
    # semantically identical here; no new IR kind, no new runtime lowering. The
    # `strOp` label passes the REAL callee name (not hardcoded "parseInt") so
    # diagnostics/pretty-printing stay accurate; `iekStrToInt`'s runtime lowering
    # dispatches purely on `e.kind` (never reads `e.strOp`), so this is a pure
    # label change with zero effect on modeling. `canonicalize`'s cache key does
    # include `strOp`, so a `parseBiggestInt` SUT gets its OWN cache key distinct
    # from an otherwise-identical `parseInt` SUT — correct (they are different
    # source expressions), not a collision risk.
    if calleeSym.strVal in ["parseInt", "parseBiggestInt"] and n.len == 2 and
       classifyType(n[1]).ty.kind == itString:
      return mkStrOp(iekStrToInt, calleeSym.strVal, @[parseExpr(n[1], preamble, ctx)])
    if calleeSym.strVal == "parseFloat" and n.len == 2 and
       classifyType(n[1]).ty.kind == itString:
      # Phase 15 S10b: Z3 String theory has NO float↔string conversion (only the
      # int `str.to_int`/`int.to_str` pair). `parseFloat(s)` routes to a
      # classified `seUnsupportedStringOp` → `sxUnknown` (S9 `iekStrUnsupported`
      # mechanism, opName "parseFloat"; Invariant 3 — never a crash/silent UNSAT).
      # Fix-slice item 5: pass the call's own classified type (`float` ->
      # itFloat64) explicitly rather than relying on `degradeStrArm`'s
      # retired `e.strOp == "parseFloat"` name match — `strRetTy` is now the
      # single source of truth for the degrade placeholder's kind.
      return mkStrOp(iekStrUnsupported, "parseFloat", @[], retTy = classifyType(n).ty)
    # Phase 16 A8: radix formatting — toHex, toBin, toOct.
    # `toHex(x)` full-width and `toHex(x, len)` / `toBin(x, len)` with a
    # COMPILE-TIME LITERAL len. Only fixed-width int operands (int8/16/32/64,
    # uint8/16/32/64 — all map to Z3 BVs under ADR-0001) are supported.
    # `strOp` encodes `"<name>:<base>:<numDigits>"` so distinct combinations
    # content-address distinctly in the cache key.
    # DEGRADE → iekStrUnsupported for: toOct, symbolic len, non-int operand.
    if calleeSym.strVal == "toOct" and n.len >= 2:
      return mkStrOp(iekStrUnsupported, "toOct", @[])
    if calleeSym.strVal in ["toHex", "toBin"] and n.len in [2, 3]:
      let operandTy = classifyType(n[1]).ty
      if operandTy.kind == itInt:
        let bvWidth     = operandTy.width   ## 8, 16, 32, or 64
        let base        = if calleeSym.strVal == "toHex": 16 else: 2
        let bitsPerDigit = if base == 16: 4 else: 1
        var numDigits: int
        if n.len == 2:
          # Full-width form: numDigits = total bits / bits-per-digit.
          # `toBin` without a len is ambiguous (Nim requires len) → degrade.
          if calleeSym.strVal != "toHex":
            return mkStrOp(iekStrUnsupported, "toBin_no_len", @[])
          numDigits = bvWidth div bitsPerDigit
        else:
          # Has a len arg — must be a compile-time integer literal.
          # Unwrap any hidden conversion inserted by Nim's semantic analysis
          # when the formal type differs from int (e.g. toBin's len is Positive,
          # so `toBin(x, 8)` may have n[2] = nnkHiddenStdConv(Positive, 8)).
          var lenNode = n[2]
          if lenNode.kind in {nnkConv, nnkHiddenStdConv, nnkHiddenSubConv}:
            lenNode = lenNode[^1]
          if lenNode.kind notin {nnkIntLit, nnkInt8Lit, nnkInt16Lit,
                                  nnkInt32Lit, nnkInt64Lit,
                                  nnkUIntLit, nnkUInt8Lit, nnkUInt16Lit,
                                  nnkUInt32Lit, nnkUInt64Lit}:
            # Symbolic/non-literal len → sound degrade (Invariant 3).
            return mkStrOp(iekStrUnsupported,
                           calleeSym.strVal & "_dynamic_len", @[])
          numDigits = int(lenNode.intVal)
        let operandIR = parseExpr(n[1], preamble, ctx)
        # Encode base+numDigits in strOp so distinct configurations get distinct
        # cache keys (canonicalize already folds strOp in for StrOpKinds).
        let opStr = calleeSym.strVal & ":" & $base & ":" & $numDigits
        return mkStrOp(iekRadixFmt, opStr, @[operandIR])
      else:
        # Non-int operand (float, bool, …) → sound degrade.
        return mkStrOp(iekStrUnsupported, calleeSym.strVal & "_non_int", @[])
    # Phase 16 A7-S3: `runeLen(s)` / `s.runeLen` — UFCS or direct call.
    # Intercept BEFORE the string-receiver guard so the std/unicode body is never
    # walked. Origin guard (owner == "unicode") prevents hijacking a user-defined
    # proc of the same name (regression guard, mirrors the C4-4 sequtils guard).
    # Literal arg → concrete rune count (decoded in Nim at parse time).
    # Symbolic arg → seZ3StringIncomplete (sxUnknown, Invariant 3 — never a crash,
    # never a hang, never a silent wrong verdict).
    if calleeSym.strVal == "runeLen" and n.len == 2:
      let runeOwner = calleeSym.owner
      if runeOwner.kind == nnkSym and runeOwner.strVal == "unicode":
        let argNode = n[1]
        if argNode.kind in {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
          # Concrete literal: call Nim's own runeLen at parse time → numeral.
          # Trivially exact vs Nim (we ARE calling Nim — Invariant 3).
          let rLen = unicode.runeLen(argNode.strVal)
          return mkIntLit(int64(rLen))
        else:
          # Symbolic string: UTF-8 grouping over an unknown byte stream has no
          # quantifier-free Z3 encoding → classified seRuneDecodeSymbolic
          # (ADR-0017; RFC-0005 S5 split it off seZ3StringIncomplete: this site
          # FORCES the value `0` below -- dcSubstituted, not a fresh symbol).
          # We are inside `parseExpr` (returns IRExpr): add the classify-error to
          # ctx.parseErrors (drained to r.errors at runSymex boundary), emit an
          # mkUnsupported stmt into the preamble (sets sawUnknown=true in walker),
          # and return a dummy IRExpr so the enclosing expression is well-typed.
          # The dummy value is never reached (walker sees sawUnknown first).
          preamble.add ctx.declineAtSite(
            seRuneDecodeSymbolic,
            "A7-S3: runeLen(symbolic) — UTF-8 grouping over unknown byte " &
                   "stream; no quantifier-free Z3 encoding (ADR-0017)",
            "symex A7-S3: runeLen(symbolic) unsupported " &
                                       "(seRuneDecodeSymbolic)")
          return mkIntLit(0)   # unreachable: walker halts on sawUnknown from above
    # Phase 15 C2b: the receiver of a string-builtin must be type-classifiable.
    # A nested CLOSURE CALL (`f(f(v))` — `n[1]` is `f(v)`) carries NO semantic
    # type (`typeKind == ntyNone`), so `classifyType`'s `getTypeInst` would raise
    # a non-catchable "node has no type" compile error. Gate the string-receiver
    # classify on the node actually HAVING a type; an untyped receiver is not a
    # string op — fall through to the normal/closure-call dispatch below.
    if n.len >= 2 and n[1].typeKind != ntyNone:
      # v65 (char-needle family): `s.contains('@')` has NO strutils
      # (string, char) overload — Nim resolves it to system.contains(
      # openArray[T], T) through the string→openArray[char] implicit
      # conversion, so the receiver arrives as nnkHiddenStdConv(
      # openArray[char], s). That classifies non-string and used to fall
      # through to user-proc INLINING of the generic system.contains,
      # whose openArray formal aborts macro expansion ("node has no
      # type"). Unwrap the hidden conversion when the node BENEATH is a
      # string — element membership over a string's openArray[char] view
      # IS char containment, i.e. exactly `iekStrContains`.
      var recvNode = n[1]
      var recvCls0 = classifyType(recvNode)
      if recvCls0.ty.kind != itString and
         recvNode.kind == nnkHiddenStdConv and recvNode.len >= 1:
        let inner = recvNode[recvNode.len - 1]
        if inner.typeKind != ntyNone and classifyType(inner).ty.kind == itString:
          recvNode = inner
          recvCls0 = classifyType(inner)
      if recvCls0.ty.kind == itString:
        # Phase 15 S6b: regex calls. `s.match(re"…")` / `s.find(re"…")` /
        # `s.contains(re"…")` / `s.replace(re"…", repl)` from Nim's `std/re`.
        # In the typed AST a `re"…"` literal is an `nnkCallStrLit` whose callee
        # is `re`/`rex` and whose `[1]` is the raw pattern string-literal; the
        # surrounding call also carries a trailing default `start` int arg
        # (match/find/contains) which we drop. We must intercept BEFORE the
        # uniform `sArgs` parse below, which would choke on `nnkCallStrLit`.
        # Only a COMPILE-TIME literal pattern is extractable; a symbolic Regex
        # value can't be parsed at walk time → routes to `iekStrUnsupported`.
        block regexCall:
          # RFC-0005 S8ay: every `std/re` entry point taking a `Regex`, not
          # only match/find/contains/replace. The others (matchLen,
          # findBounds, findAll, split, replacef, the captures overloads and
          # the `=~` template's expansion) fell through to the uniform
          # argument parse and aborted the compile ("node has no type").
          if calleeSym.strVal notin regexEntryNames:
            break regexCall
          var reIdx = -1
          for i in 2 ..< n.len:
            if isRegexTyped(n[i]):
              reIdx = i
              break
          if reIdx < 0:
            break regexCall   # the string-argument overload: not a regex call
          let entry = calleeSym.strVal
          let (flag, rePat) = regexLiteralOfCtx(n[reIdx], ctx)
          # A rejected pattern raises `RegexError` (`object of ValueError`)
          # when `re` runs; an `except ValueError` handler must see it.
          ctx.userExnHierarchy["RegexError"] = "ValueError"
          let rejected = flag != "?" and
                         parsePcre(rePat, flag == "rex").status == psRejected
          # Arguments AFTER the pattern: `start` (an int), `by` (replace's
          # string) or a captures array. Nim evaluates arguments left to
          # right and `re` raises before any later argument runs, so a
          # rejected pattern lowers the receiver alone. RFC-0005 S8bb: the
          # receiver is parsed FIRST, so a temporary it hoists precedes the
          # later arguments' in the preamble (evaluation order).
          # RFC-0005 S8bb: `findBounds` lowers its receiver and `start`
          # twice (one `iekStrFindRe` per half), so a compound one is bound
          # to a fresh `let` -- lowered, and its raises deposited, once, in
          # evaluation order (the receiver's temporary before `start` is
          # parsed). Unconditional, also in a `while` guard: a guard
          # preamble routes the loop through the rotation
          # (`mkShortCircuitWhile`), which re-runs it every iteration.
          # S8ay declined the call instead (a fresh value).
          # RFC-0005 S8bb: a captures overload (a `matches` argument, the
          # one after the pattern that is neither `start` nor `by`) reads
          # its receiver and `start` again for each group it writes, so they
          # are bound once too.
          var capsNode: NimNode = nil
          if not rejected:
            for i in reIdx + 1 ..< n.len:
              if n[i].typeKind notin {ntyInt, ntyInt8, ntyInt16, ntyInt32,
                                      ntyInt64, ntyString}:
                capsNode = n[i]
          let bindTwice = (calleeSym.strVal == "findBounds" or
                           capsNode != nil) and not rejected
          proc bindOnce(ir: IRExpr; node: NimNode;
                        preamble: var seq[IRStmt]): IRExpr =
            if not bindTwice or (isAtomicIR(ir) and ir.kind != iekStrAt):
              return ir
            let tmp = freshSynth(ctx, "regexOperand")
            preamble.add mkLet(tmp, classifyType(node).ty, ir)
            mkVar(tmp)
          let recvIR = bindOnce(parseExpr(n[1], preamble, ctx), n[1],
                                preamble)
          var startIR: IRExpr = mkIntLit(0)
          var byIR: IRExpr = mkStrLit("")
          var captures = false
          if not rejected:
            for i in reIdx + 1 ..< n.len:
              let a = n[i]
              let k = a.typeKind
              if k in {ntyInt, ntyInt8, ntyInt16, ntyInt32, ntyInt64}:
                startIR = bindOnce(parseExpr(a, preamble, ctx), a, preamble)
              elif k == ntyString: byIR = parseExpr(a, preamble, ctx)
              else: captures = true   # `matches: var openArray[...]`
          template decline(retTy: IRType; what = entry): IRExpr =
            mkStrOp(iekStrUnsupported,
                    "regex:" & encodeRegexSpec(what, flag, rePat),
                    @[recvIR], retTy)
          var capLv: NimNode = nil
          var capTy: IRType = nil
          if captures:
            # RFC-0005 S8bb: the captures overloads write `matches` (see
            # `regex_parser.lowerCapture` for std/re's rule). Modelled when
            # the pattern is read (`psOk`: its group count is known), the
            # argument is an `array[N, string]` / `seq[string]` lvalue whose
            # location no expression in it can move (`regexCapturesLvalue`)
            # and the call is one that reports a match. Otherwise the call
            # declines as S8ay's did (seUnsupportedRegex, ⊤): the write is
            # never dropped.
            capLv = capsNode
            while capLv.kind in {nnkHiddenStdConv, nnkHiddenAddr,
                                 nnkHiddenDeref, nnkHiddenSubConv} and
                  capLv.len >= 1:
              capLv = capLv[^1]
            if regexCapturesLvalue(capLv) and capLv.typeKind != ntyNone:
              let t = classifyType(capLv).ty
              let el =
                if t.kind == itArray: t.elemTy
                elif t.kind == itSeq: t.seqElemTy
                else: nil
              # `findBounds`' bounds overload: `tuple[first, last: int]`.
              if el != nil and (el.kind == itString or
                  (entry == "findBounds" and el.kind == itTuple and
                   el.fields.len == 2 and el.fields[0].kind == itInt and
                   el.fields[1].kind == itInt)):
                capTy = t
            if capTy == nil or flag == "?" or
               entry notin ["match", "matchLen", "find", "contains",
                            "findBounds"] or
               parsePcre(rePat, flag == "rex").status != psOk:
              return decline(classifyType(n).ty, entry & "Captures")
          proc plainCall(): IRExpr =
            case entry
            of "match", "contains":
              mkStrOp(iekStrMatch, encodeRegexSpec(entry, flag, rePat),
                      @[recvIR, startIR])
            of "find", "matchLen":
              mkStrOp(iekStrFindRe, encodeRegexSpec(entry, flag, rePat),
                      @[recvIR, startIR], tInt())
            else:
              # RFC-0005 S8bb: (-1, 0) on a bad offset with captures.
              mkTupleLit(@[
                mkStrOp(iekStrFindRe,
                        encodeRegexSpec("findBoundsFirstCap", flag, rePat),
                        @[recvIR, startIR], tInt()),
                mkStrOp(iekStrFindRe,
                        encodeRegexSpec("findBoundsLast", flag, rePat),
                        @[recvIR, startIR], tInt())], classifyType(n).ty)
          if capTy != nil:
            # The call, then each group's element (`iekStrCaptureRe`: the
            # element after the call, from its value before), stored into
            # a copy of `matches` that is then written back -- in Nim the
            # writes follow the match, and nothing in the call can move the
            # lvalue (`regexCapturesLvalue`), so copy-out is exact. A seq's
            # element `g - 1` exists only when `g <= len`.
            let callTmp = freshSynth(ctx, "regexCall")
            preamble.add mkLet(callTmp, classifyType(n).ty, plainCall())
            let arrTmp = freshSynth(ctx, "regexMatches")
            preamble.add mkLet(arrTmp, capTy, parseExpr(capLv, preamble, ctx))
            let isArr = capTy.kind == itArray
            let elTy = (if isArr: capTy.elemTy else: capTy.seqElemTy)
            let lenIR =
              if isArr: mkIntLit(int64(capTy.size))
              else: mkSeqLen(mkVar(arrTmp))
            let groups = parsePcre(rePat, flag == "rex").groups
            let upTo = (if isArr: min(groups, capTy.size) else: groups)
            for g in 1 .. upTo:
              let old = freshSynth(ctx, "regexOld")
              let pos = mkIntLit(int64(g - 1))
              var body: seq[IRStmt]
              body.add mkIndexStmt(old, mkVar(arrTmp), pos, elTy, siteLoc(n))
              proc spec(what: string): string =
                encodeRegexSpec(what & "|" & entry & "|" & $g, flag, rePat)
              let v =
                if elTy.kind == itString:
                  mkStrOp(iekStrCaptureRe, spec("capture"),
                          @[recvIR, startIR, lenIR, mkVar(old)])
                else:
                  mkTupleLit(@[
                    mkStrOp(iekStrFindRe, spec("captureFirst"),
                            @[recvIR, startIR, lenIR, mkField(mkVar(old), 0)],
                            elTy.fields[0]),
                    mkStrOp(iekStrFindRe, spec("captureLast"),
                            @[recvIR, startIR, lenIR, mkField(mkVar(old), 1)],
                            elTy.fields[1])], elTy)
              body.add mkIndexAssignStmt(arrTmp, pos, v, siteLoc(n))
              if isArr:
                for b in body: preamble.add b
              else:
                preamble.add mkIf(@[mkBranch(
                  mkBinop(bGe, mkSeqLen(mkVar(arrTmp)), mkIntLit(int64(g))),
                  mkBlock(body))])
            var wbPre: seq[IRStmt]
            let w = parseAsgn(nnkAsgn.newTree(capLv, newEmptyNode()),
                              mkVar(arrTmp), wbPre, ctx)
            for b in wbPre: preamble.add b
            preamble.add w
            return mkVar(callTmp)
          case entry
          of "match", "contains":
            return mkStrOp(iekStrMatch, encodeRegexSpec(entry, flag, rePat),
                           @[recvIR, startIR])
          of "startsWith", "endsWith":
            return mkStrOp(iekStrMatch, encodeRegexSpec(entry, flag, rePat),
                           @[recvIR])
          of "find", "matchLen":
            return mkStrOp(iekStrFindRe, encodeRegexSpec(entry, flag, rePat),
                           @[recvIR, startIR], tInt())
          of "findBounds":
            # (first, last): two lowerings over the same receiver and start,
            # both atoms (`bindOnce` above).
            return mkTupleLit(@[
              mkStrOp(iekStrFindRe,
                      encodeRegexSpec("findBoundsFirst", flag, rePat),
                      @[recvIR, startIR], tInt()),
              mkStrOp(iekStrFindRe,
                      encodeRegexSpec("findBoundsLast", flag, rePat),
                      @[recvIR, startIR], tInt())], classifyType(n).ty)
          of "replace":
            return mkStrOp(iekStrReplaceRe, encodeRegexSpec(entry, flag, rePat),
                           @[recvIR, byIR])
          else:
            # findAll, split, replacef, multiReplace: declined
            # (seZ3StringIncomplete, a fresh value of the call's type).
            return decline(classifyType(n).ty)
        # Phase 15 S3: `s[i]` (index read) and `s[a..b]` (slice) arrive as a
        # `[]` call on the string. The slice argument is an `nnkInfix(.., a, b)`
        # / `nnkInfix(..<, a, b)` which is NOT a scalar IR expr — handle both
        # shapes before the uniform arg parse below.
        if calleeSym.strVal == "[]" and n.len == 3:
          let recvIR = parseExpr(n[1], preamble, ctx)
          # v66 (round-4 Slice A, soundness): the slice argument can arrive
          # WRAPPED — a let/var-RHS `s[0 ..< i]` reaches here as
          # `nnkHiddenStdConv(HSlice[int, int], infix)` — and the former
          # shape-only `nnkInfix` test fell through to the CHAR path for it:
          # the binding mis-lowered as the `s[lowered-dummy]` BV8 char, every
          # downstream string op degraded (requireStr), and TWO such
          # mis-lowered slices would have compared as first-char equality —
          # a wrong-verdict hazard. Unwrap hidden wrappers first (inline
          # `unwrapHidden` — that helper is declared later in this file),
          # then dispatch on the unwrapped node's TYPE, never on shape alone.
          # `nnkStmtListExpr` included: the `..<` TEMPLATE expansion arrives
          # as `StmtListExpr(Empty, Infix("..", lo, pred(hi, 1)))` — the same
          # wrapper shape Q1 documented for the `!=` desugar; `pred(hi, 1)`
          # then lowers via the v64 pred/succ arithmetic passthrough.
          var idxNode = n[2]
          while idxNode.kind in {nnkHiddenDeref, nnkHiddenAddr,
                                 nnkHiddenStdConv,
                                 nnkStmtListExpr} and idxNode.len >= 1:
            idxNode = idxNode[idxNode.len - 1]
          if idxNode.kind == nnkInfix and idxNode.len == 3 and
             idxNode[0].kind in {nnkSym, nnkIdent} and
             isBuiltinNamed(idxNode[0], ["..", "..<"]):
            # `s[a..b]` (inclusive) / `s[a..<b]` (exclusive). Lower to
            # `iekStrSubstr` carrying [recv, lo, hi] — the runtime computes the
            # Z3 (seq.extract recv lo (hi-lo+1)) length-arg form, with hi being
            # `b` for `..` and `b-1` for `..<`.
            let loIR = parseStrSliceBound(idxNode[1], recvIR, preamble, ctx)
            var hiIR = parseStrSliceBound(idxNode[2], recvIR, preamble, ctx)
            if idxNode[0].strVal == "..<":
              hiIR = mkBinop(bSub, hiIR, mkIntLit(1))
            return mkStrOp(iekStrSubstr, "[]", @[recvIR, loIR, hiIR])
          elif idxNode.typeKind != ntyNone and
               classifyType(idxNode).ty.kind == itInt:
            # `s[i]` single-byte index read → char via at->toCode->BV8 bridge.
            # The int-type gate (not an else-fallthrough) is what makes the
            # char path UNREACHABLE for any slice-shaped index.
            let idxIR = parseExpr(idxNode, preamble, ctx)
            return mkStrOp(iekStrAt, "[]", @[recvIR, idxIR])
          else:
            # Non-int, non-recognizable-range index (e.g. an HSlice VALUE
            # bound to a name — bounds not statically extractable). CR-2a
            # classified degrade; never a char mis-read (§0 clause (b)/(c)).
            preamble.add ctx.declineAtSite(
              feUnsupportedExprKind,
              "string `[]` index is neither int-typed nor a " &
                     "recognizable range literal (kind " & $idxNode.kind &
                     ") in `" & n.repr &
                     "` — degraded to sxUnknown (feUnsupportedExprKind)",
              "string `[]` with unrecognized index (feUnsupportedExprKind)")
            let dummy = zeroValueForType(classifyType(n).ty)
            return (if dummy != nil: dummy else: mkStrLit(""))
        # Phase 15 S3: `s.high` is byte-faithfully `len(s) - 1` (ADR-0006) —
        # NOT unsupported. Build it directly from `iekStrLen`.
        if calleeSym.strVal == "high" and n.len == 2:
          let recvIR = parseExpr(n[1], preamble, ctx)
          let lenIR = mkStrOp(iekStrLen, "len", @[recvIR])
          return mkBinop(bSub, lenIR, mkIntLit(1))
        # Phase 15 S9 / Phase 16 A9: case-folding ops.
        # `toLower`/`toUpper` (std/unicode) — no Z3 native full-Unicode fold
        # primitive — stay `iekStrUnsupported` → classified `seUnsupportedStringOp`
        # (sxUnknown, Invariant 3 — never a silent UNSAT, never a crash).
        # `toLowerAscii`/`toUpperAscii` (std/strutils) are now modeled via a
        # quantifier-free BV18-ITE seqMap (ADR-0015, A9) and route to the new
        # `iekStrToLower`/`iekStrToUpper` IR kinds. An explicit guard (rather than
        # relying on the `getStdlibModelFor` else-fallthrough) keeps the
        # classification intentional and carries the real surface op name.
        if calleeSym.strVal in
             ["toLower", "toUpper", "toLowerAscii", "toUpperAscii"] and
           n.len >= 2:
          var caseArgs: seq[IRExpr]
          for i in 1 ..< n.len:
            caseArgs.add parseExpr(n[i], preamble, ctx)
          case calleeSym.strVal
          of "toLowerAscii": return mkStrOp(iekStrToLower, calleeSym.strVal, caseArgs)
          of "toUpperAscii": return mkStrOp(iekStrToUpper, calleeSym.strVal, caseArgs)
          else:              return mkStrOp(iekStrUnsupported, calleeSym.strVal, caseArgs)
        # Round-4 Slice B (ADR-0026): `strutils.strip(s[, leading[,
        # trailing[, chars]]])` with LITERAL flags and a LITERAL char set →
        # `iekStrStrip` (decomposition constraints, runtime_strings.nim).
        # Everything must be compile-time extractable — the flags select the
        # decomposition SHAPE and the chars build the finite regex union; a
        # non-literal spec degrades CLASSIFIED here rather than falling into
        # `getImpl` inlining of strip's while-loop body (exactly the Q2
        # unprovable shape this slice replaces). The typed AST materializes
        # defaulted args, so all arities land here.
        if calleeSym.strVal == "strip" and n.len >= 2:
          let recvIR = parseExpr(n[1], preamble, ctx)
          var leading = true
          var trailing = true
          var chars = " \t\v\r\n\f"     # strutils.Whitespace (the default)
          var literalOk = true
          proc boolLit(b: NimNode, into: var bool): bool =
            case b.kind
            of nnkIntLit:
              into = b.intVal != 0
              true
            of nnkSym, nnkIdent:
              if b.strVal == "true": into = true; true
              elif b.strVal == "false": into = false; true
              else: false
            else: false
          if n.len >= 3 and not boolLit(n[2], leading): literalOk = false
          if n.len >= 4 and not boolLit(n[3], trailing): literalOk = false
          if literalOk and n.len >= 5:
            var curly = n[4]
            while curly.kind in {nnkHiddenStdConv, nnkStmtListExpr} and
                  curly.len >= 1:
              curly = curly[curly.len - 1]
            if curly.kind == nnkCurly:
              chars = ""
              for el in curly:
                if el.kind == nnkCharLit:
                  chars.add char(el.intVal and 0xFF)
                elif (el.kind == nnkRange and el.len == 2 and
                      el[0].kind == nnkCharLit and el[1].kind == nnkCharLit):
                  for code in el[0].intVal .. el[1].intVal:
                    chars.add char(code and 0xFF)
                elif (el.kind == nnkInfix and el.len == 3 and
                      el[0].kind in {nnkSym, nnkIdent} and
                      el[0].strVal == ".." and
                      el[1].kind == nnkCharLit and el[2].kind == nnkCharLit):
                  for code in el[1].intVal .. el[2].intVal:
                    chars.add char(code and 0xFF)
                else:
                  literalOk = false
            else:
              literalOk = false
          if literalOk:
            let flags = (if leading and trailing: "LT"
                         elif leading: "L"
                         elif trailing: "T"
                         else: "-")
            return mkStrOp(iekStrStrip, flags & ":" & chars, @[recvIR])
          preamble.add ctx.declineAtSite(
            seUnsupportedStringOp,
            "strip with a non-literal flag/char-set spec in `" &
                   n.repr & "` is not modeled (ADR-0026 covers literal " &
                   "specs) — degraded to sxUnknown (seUnsupportedStringOp)",
            "strip with non-literal spec (seUnsupportedStringOp)")
          return mkStrLit("")
        let sm = getStdlibModelFor(calleeSym.strVal, itString)
        # Phase 15 G8: a call whose FIRST arg is an `itString` is NOT necessarily
        # a string OPERATION — it may be an ordinary USER PROC (or FUNC) whose
        # first parameter happens to be `string` (`proc foo(a: string, …)`).
        # The string-op guard must only claim calls it actually models; an
        # `smkUnregistered` name that resolves to a real user `nnkProcDef`/
        # `nnkFuncDef` falls THROUGH to the user-proc call path below (without
        # this, e.g. `solo(s)` was mis-classified `seUnsupportedStringOp` →
        # sxUnknown). RFC-parser-normalization N0: widened alongside the
        # `borrowInfoFor`/C3 sites — a `func` callee's `getImpl.kind` is
        # `nnkFuncDef`, so the bare `== nnkProcDef` comparison previously
        # missed every `func` here too (same false-degrade shape as `solo`,
        # just for `func` instead of an unresolved impl). A genuinely-
        # unsupported stdlib string call (no user impl) still routes to
        # `iekStrUnsupported` (Invariant 3 — never a silent UNSAT).
        # RFC-parser-normalization N2: the `getImpl` + kind-check step is
        # now `resolveRoutineImpl`.
        if sm.kind == smkUnregistered and
           calleeSym.kind == nnkSym and
           resolveRoutineImpl(calleeSym) != nil:
          discard   ## user proc — fall through to the user-proc call path
        else:
          var sArgs: seq[IRExpr]
          # v65: parse the (possibly conversion-unwrapped) receiver node —
          # `recvNode`, not `n[1]` — so the openArray-conv contains shape
          # lowers its actual string receiver.
          sArgs.add parseExpr(recvNode, preamble, ctx)
          for i in 2 ..< n.len:
            sArgs.add parseExpr(n[i], preamble, ctx)
          let irKind = case sm.kind
            of smkStrLen:        iekStrLen
            of smkStrIndex:      iekStrAt
            of smkStrAt:         iekStrAt
            of smkStrSubstr:     iekStrSubstr
            of smkStrFind:       iekStrFind
            of smkStrRfind:      iekStrRfind
            of smkStrContains:   iekStrContains
            of smkStrStartsWith: iekStrStartsWith
            of smkStrEndsWith:   iekStrEndsWith
            of smkStrReplaceAll: iekStrReplaceAll
            of smkStrSplit:      iekStrSplit
            of smkStrJoin:       iekStrJoin
            of smkStrMatch:      iekStrMatch
            else:                iekStrUnsupported
          # Fix-slice item 5: the `else` (unrecognized stdlib string-method
          # name) branch above is the genuinely AMBIGUOUS `iekStrUnsupported`
          # shape — unlike every other name-keyed `iekStrUnsupported` site in
          # this file, an unrecognized method name carries no implied return
          # type at all (could be int/bool/seq/anything), so `degradeStrArm`
          # (runtime.nim) previously always guessed `svString`, crashing when
          # the real callee returned e.g. int/bool. Threading the call
          # expression's own classified type here (correct for the OTHER
          # `irKind` branches too, though they never read it — their result
          # kind is already implied by `e.kind` alone) closes the gap.
          return mkStrOp(irKind, calleeSym.strVal, sArgs, retTy = classifyType(n).ty)
    # RFC-0005 S8at: the stdlib's `initTable` / `initHashSet`.
    block:
      let initIR = parseInitContainer(n, calleeSym, preamble, ctx)
      if initIR != nil: return initIR
    # Stdlib builtins recognised by name (Phase 5+):
    # `len(c)` on seq/Table/HashSet → iekSeqLen (semantic: "container
    # cardinality", lowered against the right counter at runtime).
    # RFC-0005 S8bq (item 2): `card(s)` / `len(s)` of a builtin set.
    if n.len == 2 and isBuiltinNamed(calleeSym, ["len", "card"]) and
       n[1].typeKind != ntyNone and classifyType(n[1]).ty.kind == itBitSet:
      return mkBitSet(bsoCard, @[parseExpr(n[1], preamble, ctx)],
                      classifyType(n[1]).ty)
    if calleeSym.strVal in ["len", "card"] and n.len == 2:
      let argCls = classifyType(n[1])
      if argCls.ty.kind in {itSeq, itTable, itSet}:
        # Round-6 B1: shared with the `nnkDotExpr` `.len` arm above —
        # `parseSeqLenAccess` chooses `iekStrLen` over `mkSeqLen` for a
        # string-backed `itSeq` receiver (never true for itTable/itSet).
        return parseSeqLenAccess(n[1], parseExpr(n[1], preamble, ctx), ctx)
    # `contains(c, k)` and `hasKey(c, k)` on a Table/HashSet → iekContains.
    # N14 (RFC-chapulin-hardening bucket-2): WIDENED to `itSeq` too — `x in
    # mySeq`/`mySeq.contains(x)` PRE-N14 fell through this `if` entirely
    # (itSeq was never in the receiver-kind set) into ordinary callee
    # resolution, attempting to WALK system's generic `contains(openArray)`
    # body — a genuine COMPILE-TIME CRASH (`dsl_typebridge.nim:413 "node has
    # no type"`, the A5 hard-crash class), confirmed via direct repro before
    # this fix (`v in xs` on a bare `seq[int]` parameter). `iekContains`'s
    # OWN runtime dispatch (`runtime.nim`) already declines cleanly
    # (`feUnsupportedOp`) for any receiver kind other than svTable/svSet —
    # only the PARSE-TIME gate was missing the itSeq route into it. `itSet`
    # is Nim's `HashSet` (already routed); a static `array[N, T]` classifies
    # `itArray`, a SEPARATE receiver kind this fix does not touch (no crash
    # repro found for it — out of this slice's scope, left as a future
    # finding if one surfaces).
    # RFC-0005 S8bi: `k in {..}` / `k notin {..}` over a set LITERAL of
    # constants (`notin` is `not contains(..)`); see `parseSetLitMember`.
    if n.len == 3 and isBuiltinNamed(calleeSym, ["contains"]):
      let member = parseSetLitMember(n[1], n[2], preamble, ctx)
      if member != nil: return member
      # RFC-0005 S8bq (item 2): `k in s` on a builtin set value. The key's
      # conversion to `T` is parsed with it, so it is range-checked (probe:
      # `x in rs` for `rs: set[range[0..9]]` and `x = 20` raises
      # `RangeDefect`; only a literal's key is not checked).
      if calleeSym.kind == nnkSym and n[1].typeKind != ntyNone and
         classifyType(n[1]).ty.kind == itBitSet:
        let setTy = classifyType(n[1]).ty
        let sIR = parseAtomicOperand(n[1], preamble, ctx)
        let mark = preamble.len
        let kIR = parseAtomicOperand(n[2], preamble, ctx)
        keepInlineRaiseOrder(sIR, n[1], mark, preamble, ctx)
        return mkBitSet(bsoContains, @[sIR, kIR], setTy)
    if (calleeSym.strVal == "contains" or calleeSym.strVal == "hasKey") and
       n.len == 3:
      var containsRecvNode = n[1]
      var recvCls = classifyType(containsRecvNode)
      # N14 follow-up: `system.contains[T](a: openArray[T], item: T)` takes
      # its seq argument through an implicit seq->openArray conversion — the
      # SAME `nnkHiddenStdConv` shape the `[]` slice arm above already
      # unwraps (its own comment: "the bare receiver classify sees
      # openArray, not itSeq"). Without this, `classifyType` never resolves
      # itSeq here and the widened `itSeq` branch below silently never
      # fires, falling through to the generic-callee-resolution crash this
      # fix exists to close.
      if recvCls.ty.kind != itSeq and
         containsRecvNode.kind == nnkHiddenStdConv and containsRecvNode.len >= 1:
        let inner = containsRecvNode[containsRecvNode.len - 1]
        if inner.typeKind != ntyNone and classifyType(inner).ty.kind == itSeq:
          containsRecvNode = inner
          recvCls = classifyType(inner)
      if recvCls.ty.kind in {itTable, itSet, itSeq}:
        let recvIR = parseExpr(containsRecvNode, preamble, ctx)
        let keyIR  = parseExpr(n[2], preamble, ctx)
        return mkContains(recvIR, keyIR)
    # N14 (RFC-chapulin-hardening bucket-2): `mySeq.pop()` → A-normalised
    # `isSeqPop` (mirrors the Table `[]` A-normalisation just below: a fresh
    # synth temp bound in the preamble, `mkVar(synth)` returned in the
    # expression's place). Unlike `del`/`insert` (recognized only as bare
    # STATEMENTS further below, in `parseStmt`'s own `nnkCall` dispatch) or
    # `.add` (also statement-only, void return), `.pop()` is used in
    # EXPRESSION position (`let last = mySeq.pop()`) and must recurse through
    # `parseExpr`, so it is recognized HERE rather than there. Only a bare
    # `nnkSym` receiver is recognized (matching every other seq-mutation
    # site's scope in this file — a computed/temporary receiver has no
    # stable name to rebind).
    if calleeSym.strVal == "pop" and n.len == 2:
      let recvCls = classifyType(n[1])
      if recvCls.ty.kind == itSeq:
        let recv = unwrapHidden(n[1])
        if recv.kind == nnkSym:
          let synth = freshSynth(ctx, "pop")
          preamble.add mkSeqPopStmt(recv.strVal, synth, siteLoc(n),
                                    recvCls.ty.seqElemTy)   # RFC-0005 S8ba
          return mkVar(synth)
    block:
      # RFC-0005 S8bl (item 1): `move(x)`.
      let mvIR = parseMoveExpr(n, calleeSym, preamble, ctx)
      if mvIR != nil: return mvIR
    # RFC-0005 S8bc: `getOrDefault(t, k[, d])` on a Table is the present
    # value, else `d` (or `default(V)`). It walked the stdlib body before,
    # whose `hashes.Hash` locals the model does not classify (a decline, and
    # a walker fault under `and`).
    block:
      let godIR = parseGetOrDefault(n, calleeSym, preamble, ctx)
      if godIR != nil: return godIR
    # `[](t, k)` on a Table → A-normalised isIndex (runtime dispatches
    # on receiver kind for select-from-tabData semantics).
    if calleeSym.strVal == "[]" and n.len == 3:
      let recvCls = classifyType(n[1])
      if recvCls.ty.kind == itTable:
        let recvIR = liftIndexContainer(parseExpr(n[1], preamble, ctx),
                                        recvCls.ty, preamble, ctx)
        let keyIR  = parseExpr(n[2], preamble, ctx)
        let synth = freshSynth(ctx, "tget")
        preamble.add mkIndexStmt(synth, recvIR, keyIR, recvCls.ty.tabValTy)
        return mkVar(synth)
      # v67 (dev item 1): system's slice `[]` overload takes an OPENARRAY
      # receiver — `data[a..b]` therefore arrives as
      # `[]`(nnkHiddenStdConv(openArray[T], data), HSlice…) and the bare
      # receiver classify sees openArray, not itSeq. Unwrap the hidden
      # conversion when a seq sits beneath (the `contains`-via-openArray
      # precedent, v65).
      var sliceRecvNode = n[1]
      var sliceRecvCls = recvCls
      if sliceRecvCls.ty.kind != itSeq and
         sliceRecvNode.kind == nnkHiddenStdConv and sliceRecvNode.len >= 1:
        let inner = sliceRecvNode[sliceRecvNode.len - 1]
        if inner.typeKind != ntyNone and classifyType(inner).ty.kind == itSeq:
          sliceRecvNode = inner
          sliceRecvCls = classifyType(inner)
      if sliceRecvCls.ty.kind == itSeq:
        # v67 (dev item 1): the call-form seq slice — `[]`(data, HSlice…) —
        # previously fell through to `getImpl` INLINING of system's `[]`
        # (whose body macro-aborted on `len`). Round-6 B1: dispatch shared
        # with the bracket-expr arm above via `parseSeqBracketAccess` (the
        # RFC's explicit "cannot diverge" requirement for the two
        # previously-DUPLICATE slice/index sites).
        # Round-6 N15: same field-sourced-placeholder chokepoint as the
        # bracket-expr arm above (`classifyType` never carries the per-field
        # placeholder annotation — detect the decline directly off what
        # `parseExpr` RETURNED: `seqLitDeclinedPlaceholder: true` on a
        # `iekSeqLit` result, the parse-time twin of
        # `SymVal.isUnsupportedFieldPlaceholder`). Building `isIndex`/
        # `mkSeqSlice` over the declined receiver's fake empty-seq stand-in
        # would crash `lowerLeafInExpr`'s side-effect-free-container
        # assertion instead of reporting the classified kind every other
        # placeholder-consuming form reports.
        let recvIR = parseExpr(sliceRecvNode, preamble, ctx)
        if recvIR.kind == iekSeqLit and recvIR.seqLitDeclinedPlaceholder:
          let dummy = zeroValueForType(classifyType(n).ty)
          return (if dummy != nil: dummy else: mkIntLit(0))
        return parseSeqBracketAccess(n, sliceRecvNode, recvIR, n[2],
                                      sliceRecvCls.ty.seqElemTy,
                                      preamble, ctx)
    # Phase 15 F6: std/math float ops + FP predicates. The modeled and the
    # deferred names are both routed to iekMathCall — the runtime lowers the
    # modeled ones to Z3-FP-native asts and the deferred ones to a classified
    # `feUnsupportedOp` error (Invariant 3 — never a silent UNSAT). We only
    # intercept when the FIRST argument is float-typed, so e.g. integer `abs`
    # or `min`/`max` on ints fall through to their existing handling.
    block mathInterception:
      let cn = calleeSym.strVal
      if n.len >= 2:
        let firstCls = classifyType(n[1])
        if firstCls.ty.kind in {itFloat32, itFloat64}:
          # Known modeled/deferred names always route to iekMathCall. Any
          # OTHER float-receiver call into the Nim stdlib (e.g. `ln`, `sin`)
          # is an unmodeled std/math op — also route it so the runtime emits
          # `feUnsupportedOp` rather than failing `getImpl` resolution or
          # walking a transcendental's body (Invariant 3 — never silent UNSAT).
          if cn in mathFpModeledOps or cn in mathFpDeferredOps or
             isStdMathProc(calleeSym):
            var mArgs: seq[IRExpr]
            for i in 1 ..< n.len:
              mArgs.add parseExpr(n[i], preamble, ctx)
            return mkMathCall(cn, mArgs)
    # A7 (ADR-0017 Path B): `ord(r)` where `r` classifies as tInt (Rune → tInt).
    # `ord` is a magic intrinsic with no parseable body; for a type already
    # classified to tInt (e.g. Rune after A7 intercept), `ord` is the identity
    # ONLY when its argument's own classified width already matches `ord`'s
    # declared return type.
    #
    # Issue #163 (found during the round-9 range-alias review, fixed here).
    # `ord`'s declared signature is `proc ord*[T](x: T): int` — its RESULT is
    # always native (64-bit signed) `int`, regardless of `T`. This arm used
    # to `return parseExpr(n[1], ...)` unconditionally: an identity
    # pass-through at the ARGUMENT's own classified width, not `ord`'s
    # declared return width. For a plain `int`/Rune argument the two
    # coincide (both 64-bit), so no bug was visible there — but an ENUM
    # argument classifies to `itInt` at its own lifted, narrow width
    # (`enumOrdBitsNeeded`, e.g. 2 bits for a 3-member enum), and a `char`
    # argument classifies at 8 bits (`dsl_typebridge.nim`'s `"char"` arm).
    # Reproduced empirically (`scratchpad/probe_163ord_*.nim`, not
    # committed): `proc f(c: Color) = if ord(c) > 3_000_000_000:
    # symexTarget("hit")` for a 3-member `Color` enum returned `sxSat` with
    # witness `cGreen` — real Nim's `ord(cGreen)` is 1, never close to three
    # billion. `treeRepr`/`getTypeInst` confirm the compiler wraps the whole
    # `ord(c)` CALL in an `nnkHiddenStdConv` for the surrounding comparison,
    # but that wrapper's own `getTypeInst` (`int64`) already matches the
    # Call node's OWN `getTypeInst` (`int`, from `ord`'s declared return
    # type) — so the generic `nnkHiddenStdConv` widening arm above (issue
    # #163 rev items 2/2-followup) sees no width mismatch at that level and
    # recurses straight into this `nnkCall` "ord" handling, where the bug
    # actually lived: re-deriving the result's width from the ARGUMENT
    # (`n[1]`, e.g. `Color`) discarded the correct native-`int` answer the
    # Call node's own type already carried one level up.
    #
    # Fix: read both widths off `classifyType`, exactly as the
    # `nnkHiddenStdConv` arm already does — `outerTy` from the CALL node `n`
    # itself (which resolves `ord`'s declared `int` return type, always
    # native width) and `innerTy` from the argument `n[1]` (the enum's own
    # lifted width via `enumOrdBitsNeeded`, or a range alias's own width via
    # `rangeBaseType`). A genuine width change routes through the same
    # `mkConvIntWidth` widening machinery the two landed hidden-conversion
    # fixes use, with the identical `isPromoteSoundEligibleParam` carve-out:
    # `ord` of a bare reference to the current proc's own signed, ranged,
    # top-level param must stay an untouched identity pass-through, because
    # `promoteSound` (issue #161) already promoted that param to an
    # unbounded Z3 Int with no BV modulus to wrap against — and
    # `mkConvIntWidth`'s walker hard-asserts a raw BV operand, so routing a
    # promoted param through it regressed a correct `sxUnsat` to `sxUnknown`
    # the same way it did for the hidden-stdconv arm (confirmed empirically
    # for that arm; not re-tried here since the shape and the wall are
    # identical).
    if calleeSym.strVal == "ord" and n.len == 2 and
       n[1].typeKind != ntyNone and
       classifyType(n[1]).ty.kind == itInt:
      let outerTy = classifyType(n).ty
      let innerTy = classifyType(n[1]).ty
      if outerTy.kind == itInt and outerTy.width != innerTy.width and
         not isPromoteSoundEligibleParam(n[1], innerTy):
        if outerTy.width > innerTy.width:
          return mkConvIntWidth(parseExpr(n[1], preamble, ctx),
                                 innerTy.width, innerTy.signed,
                                 outerTy.width, outerTy.signed)
        else:
          return declineIntWidthConv(n, preamble, ctx, "hidden narrowing",
                                      valueTypeName(n[1]), valueTypeName(n))
      return parseExpr(n[1], preamble, ctx)
    # v64 (chapulin catalog #pred): `pred(x[, k])` / `succ(x[, k])` are magic
    # intrinsics with no parseable body, and `a ..< b` lowers via a template
    # to `a .. pred(b)` — so `pred` sits on the hot path of every `..<`
    # slice/range a SUT writes (chapulin: `rest[1 ..< closeBracket]` failed
    # to compile with "unsupported infix operator `..`" precisely because
    # the pred-rewritten bound had no case here; the literal-infix `..<`
    # match stays the fast path for shapes the compiler leaves unexpanded).
    # For an int-classified operand they are plain arithmetic: pred → `-`,
    # succ → `+`, with the default step 1 when the typed AST omits it.
    if calleeSym.strVal in ["pred", "succ"] and n.len in [2, 3] and
       n[1].typeKind != ntyNone and
       classifyType(n[1]).ty.kind == itInt:
      let base = parseAtomicOperand(n[1], preamble, ctx)  ## A2a chokepoint (pred/succ)
      let mark = preamble.len
      let step = if n.len == 3: parseAtomicOperand(n[2], preamble, ctx)  ## A2a chokepoint (pred/succ)
                 else: mkIntLit(1)
      keepInlineRaiseOrder(base, n[1], mark, preamble, ctx)
      return mkBinop(if calleeSym.strVal == "pred": bSub else: bAdd,
                     base, step)
    # A7 (ADR-0017 Path B): borrow comparison ops (==, !=, <, <=, >, >=) on
    # types that classify as tInt (e.g. Rune → tInt) arriving as nnkCall.
    # The nnkInfix borrowIntercept already handles infix-form writes; this block
    # covers the nnkCall form that the compiler may emit for borrow shims.
    block runeCompareIntercept:
      if calleeSym.strVal notin ["==", "!=", "<", "<=", ">", ">="]: break runeCompareIntercept
      if n.len != 3: break runeCompareIntercept
      if n[1].typeKind == ntyNone: break runeCompareIntercept
      if classifyType(n[1]).ty.kind != itInt: break runeCompareIntercept
      ## RFC-parser-normalization N2: `getImpl` + kind-check -> `resolveRoutineImpl`.
      let ci = resolveRoutineImpl(calleeSym)
      if ci == nil or not hasBorrowPragma(ci): break runeCompareIntercept
      let (lhs, rhs) = parseOperandPair(n[1], n[2], preamble, ctx)  ## A2a chokepoint (rune-compare); RFC-0005 S8ax order
      return mkBinop(binopForInfix(calleeSym.strVal), lhs, rhs)
    # RFC-0005 S8c: every builtin-by-name model above has had its chance
    # (and, since the user-callee gate at the top of this arm, sees only
    # stdlib-declared callees). What is left is an ordinary routine call.
    parseRoutineCallExpr(n, calleeSym, preamble, ctx)
  of nnkIfExpr:
    # RFC-chapulin-hardening M5 (walker v50->51): an if-EXPRESSION used as a
    # SUB-EXPRESSION (e.g. `(if c: 1 else: 2) + 1`, or the direct RHS of a
    # `let`) previously fell through to the CR-2a catch-all below. Model it
    # via synthetic let+read A-normalisation (the same idiom CR-1b/M4 use):
    # hoist a fresh temp, emit the if AS A STATEMENT into `preamble` whose
    # each arm's tail expression is bound to that temp via `mkLet` (each
    # branch only ever executes on its OWN forked path — runtime.nim's
    # `isIf` walker forks `paths` per-arm before running the arm body, so
    # rebinding the same name in sibling arms cannot collide), then return a
    # read of the temp. Nim only accepts an if-EXPRESSION when every arm's
    # type unifies (and requires an `else`), so `classifyType(n).ty` yields
    # one common type shared by all arms.
    #
    # This also — with NO further code — makes `min`/`max` on ints work:
    # `system.min`/`system.max`'s int overloads have a real (non-empty) body
    # `if x <= y: x else: y` despite the `{.magic.}` pragma, so `getImpl`
    # resolves it; `parseCalleeImpl`'s single-`result = expr` rewrite (the
    # `resultRhs` helper) detects the whole body as one expression and calls
    # `parseExpr` directly on its `nnkIfExpr` — routing straight through this
    # arm via ordinary proc-inlining (confirmed against `system/comparisons.nim`
    # in the toolchain image; the float overloads are intercepted earlier, by
    # `mathInterception`, and never reach here).
    let resultTy = classifyType(n).ty
    let tmp = freshSynth(ctx, "ifexpr")
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    for arm in n:
      case arm.kind
      of nnkElifBranch, nnkElifExpr:
        var condPre: seq[IRStmt]
        let condIR = parseExpr(arm[0], condPre, ctx)
        for cs in condPre: preamble.add cs
        var bodyPre: seq[IRStmt]
        let bodyIR = parseExpr(arm[1], bodyPre, ctx)
        bodyPre.add mkLet(tmp, resultTy, bodyIR)
        branches.add mkBranch(condIR,
          if bodyPre.len == 1: bodyPre[0] else: mkBlock(bodyPre))
      of nnkElse, nnkElseExpr:
        var bodyPre: seq[IRStmt]
        let bodyIR = parseExpr(arm[0], bodyPre, ctx)
        bodyPre.add mkLet(tmp, resultTy, bodyIR)
        elseBody = if bodyPre.len == 1: bodyPre[0] else: mkBlock(bodyPre)
      else:
        error(&"symex M5: unexpected if-expr arm kind {arm.kind}", arm)
    preamble.add mkIf(branches, elseBody)
    mkVar(tmp)
  of nnkTupleConstr:
    # RFC-chapulin-hardening P1 (walker v51->52): a general N-ary tuple
    # constructor `(a, b, c)` / named `(x: a, y: b)` used as an EXPRESSION
    # (e.g. `let t = (a, b)`, `return (a, b, c)`) — previously only the
    # narrow `yield (e1,e2)` special-case (`parseIterBodyStmt` above) handled
    # `nnkTupleConstr`; any OTHER occurrence fell through to the CR-2a
    # catch-all below, degrading the whole run to `sxUnknown` (SND-1 taint on
    # the dummy). Build an `iekTupleLit` node, reusing the ALREADY-BUILT
    # itTuple/svTuple witness/runtime machinery (used today for
    # variant/object values) — this slice is purely the CONSTRUCTION path.
    #
    # `classifyType(n)` resolves via `n.getTypeInst` (dsl_typebridge.nim:89),
    # which for a tuple-constructor EXPRESSION node yields the tuple's TYPE
    # node — `nnkTupleConstr` for an anonymous tuple, `nnkTupleTy` for a named
    # one — and dsl_typebridge's existing structural-match arms (lines
    # 129-146) already turn either into a correctly-shaped
    # `tTuple(fields, names)` (field names populated for the named-tuple
    # case, all-"" for the anonymous case). So the type side needs no new
    # code; only the runtime `iekTupleLit` construction is net-new.
    #
    # Each element is parsed via the ORDINARY `parseExpr` recursion — no
    # special-casing per element. A still-unsupported field expression
    # (`cast`, `objConstr`, …) independently hits the CR-2a catch-all below,
    # which emits `mkUnsupported` into `preamble`; SND-1's taint on
    # `isUnsupported` demotes `Path.uncertain` regardless of where in the
    # tuple construction it originates, so a tuple with one unsupported field
    # degrades the WHOLE run to `sxUnknown` — it can never manufacture a
    # false `sxSat` from the unsupported field's dummy zero-value
    # (Invariant 3).
    #
    # A named tuple constructor `(x: a, y: b)` presents each field as an
    # `nnkExprColonExpr[name, valueExpr]` child; unwrap to the value.
    let tupleTy = classifyType(n).ty
    # RFC-0005 S8ax: elements filled in order (`orderOperands`).
    let elems = parseOrderedArgs(n, 0, preamble, ctx, omElements)
    mkTupleLit(elems, tupleTy)
  of nnkObjConstr:
    # RFC-chapulin-hardening P2a (walker v52->53): a value-object (non-ref)
    # constructor `Point(x: a, y: b)` used as an EXPRESSION (`let p =
    # Point(x: a, y: b)`, an object `return`). Previously `nnkObjConstr` was
    # recognised ONLY inside `nnkRaiseStmt`'s `newException(T, msg)` shape
    # (above); any OTHER value-object construction fell through to the CR-2a
    # catch-all below, tainting the whole run to `sxUnknown` (SND-1).
    #
    # A value object's `IRType` is `itTuple`-shaped: `classifyType`
    # (`dsl_typebridge.nim`'s nominal-object plain-record path, already
    # exercised today by object-typed SUT PARAMETERS — see
    # `tsymex_phase4_tuple.nim`'s `Point` case) resolves an `nnkObjConstr`
    # EXPRESSION node's `getTypeInst` to the object's type symbol, yielding
    # `tTuple(fields, fieldNames, objectName = "Point")` — the SAME shape
    # `nnkTupleConstr` (P1, just above) produces, just with `objectName`
    # populated. So this slice REUSES `iekTupleLit`/`mkTupleLit`/
    # `lowerTupleLit` wholesale (no new IR kind): the itTuple/svTuple
    # witness/runtime machinery already renders objects correctly (they
    # appear as SUT params today) and every existing `iekTupleLit` dispatch
    # site (emitExpr, abstraction.nim, probeProto, canonicalize, …)
    # transfers for free. Reading a field (`p.x`) was ALREADY supported
    # (`nnkDotExpr`'s `itTuple` arm above) — the gap was only construction.
    #
    # Unlike a tuple, `nnkObjConstr` fields may be (a) in ANY order and (b)
    # OMITTED, so we cannot just walk `n`'s children positionally. Build a
    # name -> value-node map from the present fields (skip `n[0]`, the type
    # symbol — fields start at index 1, each an `nnkExprColonExpr[name,
    # valueExpr]`; Nim's object-constructor syntax has no positional form),
    # then walk `objTy.fieldNames` — the TYPE's declared order — filling in
    # each element in that order. A present field parses via the ORDINARY
    # `parseExpr` recursion (same soundness argument as P1: an individually-
    # unsupported field, e.g. `cast[int32](x)`, independently hits the CR-2a
    # catch-all and taints the whole run via SND-1 — Invariant 3, never a
    # false `sxSat`).
    #
    # An OMITTED field is genuinely, soundly zero-initialised by Nim (this is
    # NOT a degrade-to-dummy — it is the real value a running program would
    # observe), so we synthesise it via CR-2a's `zeroValueForType` on the
    # field's OWN `IRType` (mirrors the catch-all's dummy-construction idiom
    # just below, reused here for a genuinely-sound purpose rather than an
    # unsupported-shape fallback). If a field's declared type has NO clean
    # zero-value encoding (`zeroValueForType` returns `nil` — e.g. a nested
    # seq/tuple/variant/ref-typed field), guessing would be UNSOUND, so this
    # degrades that one field the same way the CR-2a catch-all degrades an
    # unsupported node: register a classified `feUnsupportedExprKind` error
    # and emit `mkUnsupported` into the preamble, which taints the whole run
    # to `sxUnknown` via SND-1 — never a false `sxSat` from a guessed zero.
    #
    # RFC-chapulin-hardening P2b (walker v53->54, ADR-0021): `ref object`
    # construction as an expression (`let p = Node(val: x, next: nil)`,
    # `Node = ref object`). `classifyType` UNWRAPS a NAMED `ref object` alias
    # to its VALUE shape EXACTLY like a plain value object (both build the
    # SAME `tTuple(fields, fieldNames, objectName)` — see `dsl_typebridge.nim`
    # "#136: unwrap ref T / ptr T" ~195-205), so this arm is UNCONDITIONALLY
    # reached for ref-object constructors too, already, with NO branch needed
    # to detect "is this a ref object" — P2a's shipped code silently already
    # took this path for `Node(...)`. Empirically confirmed (RFC investigation
    # 2026-07-22): a synthesised `isNew` + field-split-heap-write preamble (the
    # RFC's original sketch) is NOT viable here and was rejected — `let p =
    # new(Node)` for a NAMED ref-object alias crashes TODAY at walk time
    # (`field 'refPointeeTy' is not accessible for type 'IRType' using 'kind =
    # itTuple'`) because Phase 16 D1a deliberately VALUE-MODELS every BARE
    # symbol of a named ref-object-alias type (`classifyType` doesn't unwrap
    # based on how the symbol was bound — a `let`-bound temp is classified
    # IDENTICALLY to a formal param). Any `svRef` a heap-based construction
    # minted would be invisible to every later BARE read of `p.field`
    # elsewhere in the SUT (those reads independently re-derive `p`'s type
    # from the AST, always landing `itTuple`) — see ADR-0021 for the full
    # writeup. So P2b's real (and narrower-than-sketched) new capability is:
    # teach THIS existing value-tuple construction arm to handle ref/ptr-typed
    # FIELDS soundly — `nil` literals, omitted-field nil-init, and a safe
    # degrade for a field value that doesn't resolve to a genuine ref/ptr
    # address. This applies uniformly to value-object AND ref-object
    # constructors alike (a plain `object` can also declare a `next: Node`
    # field), so there is deliberately no ref-vs-value branch here.
    #
    # GUARD (P2b): a VARIANT object constructor (`itVariant`/`itMultiVariant`
    # — `case` fields) reaching this arm would otherwise CRASH — the code
    # below unconditionally reads `objTy.fieldNames`/`.fields`, fields that
    # simply do not exist on those `IRType` kinds (a Nim object-variant
    # `FieldDefect`, empirically confirmed as a hard MACRO-EXPANSION error:
    # `VNode(kind: true, a: x)` for a `case`-fielded `VNode` fails to compile
    # the SUT at all today — a P2a gap this retroactively hardens). Variant
    # ref-object construction was EXCLUDED here (round-2 decision) until
    # RFC-0005 S8l, which builds it on the heap (the `isRefCtor` path below);
    # a VALUE multi-variant constructor still declines. Degrade soundly: register the classified error and
    # return a reference to a FRESH, DELIBERATELY-UNBOUND synthetic var name
    # (never `mkLet`/`mkAssign`-bound). This is the SAFE degrade shape — env
    # is `OrderedTable[string, SymVal]`, so any consumer's later `env[name]`
    # lookup (whether via a `let`-bound witness, a nested field access, …)
    # raises `KeyError` (`CatchableError`), caught by the CR-1c safety net
    # (`weInternalWalkerFault` → `sxUnknown`). A type-MISMATCHED dummy (e.g.
    # `mkIntLit(0)` bound under a name whose declared type is `itVariant`)
    # would be UNSAFE instead: a later variant-field access on a
    # wrongly-kinded-but-PRESENT `SymVal` hits `isVariantField`'s
    # `doAssert false` — an uncatchable `Defect`, a genuine process crash, not
    # merely an unmodeled construct.
    #
    # Cluster H Step C (ADR-0022 Round-2) FOLDS IN H4's core here: once
    # `classifyType` flips a NAMED ref-object alias to `itRef`/`itPtr(full
    # pointee)` (dsl_typebridge.nim), THIS constructor node classifies to
    # `itRef`/`itPtr` too — so the P2b value-tuple arm below is superseded by
    # REAL heap construction (`mkNewT` + per-PRESENT-field
    # `mkFieldDerefWrite`) for a ref-object constructor, while a plain
    # (non-ref) `object` constructor keeps the ORIGINAL P2a/P2b value-tuple
    # path unchanged. This MUST land in the SAME change as the classifyType
    # flip (field-read routing has no runtime fallback — see the H1 handoff:
    # leaving construction on `mkTupleLit` would regress P2b-1..8 to
    # `sxUnknown` the instant `classifyType` flips).
    let objTyFull = classifyType(n).ty
    case objTyFull.kind
    of itVariant:
      # Round-6 A1 (ADR-0029). SPLIT from the former combined `of itVariant,
      # itMultiVariant:` decline arm (round-2 architect review — un-split,
      # an implementer editing one shared case arm silently changes
      # behavior for both kinds). A LITERAL-discriminant constructor now
      # builds a real `svVariant` (`iekVariantLit`, see its doc comment in
      # `types.nim` for the full design); `itMultiVariant` gets its own
      # retained decline arm below. Two shapes stay excluded here too —
      # neither is this slice's job:
      #   * a ref-ALIASED variant constructor (`VNode = ref object; case
      #     kind: ...`) was declined here until RFC-0005 S8l
      #     (`ctorIsRefAliasedVariant`): it now classifies to `itRef` and is
      #     built on the heap by the `isRefCtor` path below.
      #   * a SYMBOLIC discriminant — A3's fork-per-tag
      #     `isVariantConstructSym` job, not an `iek*` (a value-producing
      #     expression cannot fork paths; see the `iekVariantLit` doc
      #     comment).
      var byNameDisc = initTable[string, NimNode]()
      for k in 1 ..< n.len:
        let child = n[k]
        if child.kind == nnkExprColonExpr:
          byNameDisc[child[0].strVal] = child[1]
      if not byNameDisc.hasKey(objTyFull.vDiscName):
        # Structurally shouldn't happen — Nim requires the discriminant in
        # a case-object constructor — but decline rather than crash.
        preamble.add ctx.declineAtSite(
          feUnsupportedExprKind,
          siteMsg(n, "A1: variant object constructor missing its " &
                            "discriminant field `" & objTyFull.vDiscName & "`"),
          "A1: variant constructor missing " &
                                      "discriminant (feUnsupportedExprKind)")
        # #163 regression fix (post-round-9 gate): a BOUND, type-correct
        # dummy (mirrors `declineIntWidthConv`'s "never an unbound `mkVar`"
        # precedent) -- NOT a dangling `mkVar(freshSynth(...))` reference
        # into an env slot no LET statement ever binds. Confirmed via
        # `tests/tsymex_r6_a1_variantlit.nim`'s A1-5 (the `itMultiVariant`
        # sibling arm below): reading a dangling fresh-synth name used to
        # raise `KeyError` at walk time, silently swallowed by the known
        # C-backend nested-`walkBlock` exception-loss quirk (SND-3/ADR-0023)
        # -- masked, not sound, and #163's `iekVar` global-read fix
        # (`runtime.nim`) closed that swallow, which then surfaced the
        # dangling reference as a genuine crash one level further down
        # (`isVariantField` reading a wrongly-kinded substitute).
        return unsupportedFieldPlaceholder(objTyFull)
      # Try the static-tag path first — same `parseExpr` + `iekIntLit`
      # test the `nnkAsgn`/`isVariantReassign` static-tag path already
      # uses (mirrored deliberately, not reinvented).
      let tagIR = discTagLit(parseExpr(byNameDisc[objTyFull.vDiscName],
                                       preamble, ctx))
      if tagIR.kind != iekIntLit:
        # Round-6 A3 (ADR-0029): SYMBOLIC discriminant — fork-per-tag
        # construction (`isVariantConstructSym`), not A1's `iekVariantLit`
        # (a value-producing expression cannot fork paths). Nim itself only
        # accepts a non-constant discriminant in constructor syntax when NO
        # arm-specific field is set (it cannot prove which arm's storage is
        # safe to initialise otherwise) — so every OTHER key in
        # `byNameDisc` MUST be a shared/plain field; an arm-specific key
        # here is a shape Nim's own compiler already forbids, but we decline
        # defensively rather than guess which arm it was meant for.
        var badField = ""
        for k in byNameDisc.keys:
          if k != objTyFull.vDiscName and k notin objTyFull.vPlainFieldNames:
            badField = k
            break
        if badField.len > 0:
          preamble.add ctx.declineAtSite(
            feUnsupportedExprKind,
            siteMsg(n, "A3: symbolic-discriminant variant constructor " &
                              "sets `" & badField & "`, which is not a " &
                              "shared/plain field — Nim itself only accepts " &
                              "a non-constant discriminant when no arm-" &
                              "specific field is initialised"),
            "A3: symbolic-discriminant " &
                                        "constructor with an arm-specific " &
                                        "field unmodeled (feUnsupportedExprKind)")
          # #163 regression fix (post-round-9 gate): bound dummy, not a
          # dangling `mkVar` -- see the missing-discriminant arm's comment
          # above.
          return unsupportedFieldPlaceholder(objTyFull)
        # Parse-time `case`-branch tag-set NARROWING (ADR-0029): consult the
        # INNERMOST `ctx.procScoped.caseNarrow` entry (searched from the top of the
        # stack — the most tightly-scoped enclosing `case`) whose subject
        # matches this discriminant expression's `.repr`; fall back to
        # every declared non-else arm's ordinal when nothing narrows it.
        let discNode = byNameDisc[objTyFull.vDiscName]
        var tagSet: seq[int] = @[]
        var narrowed = false
        for i in countdown(ctx.procScoped.caseNarrow.high, 0):
          if ctx.procScoped.caseNarrow[i].subjectRepr == scopedRepr(discNode):  ## RFC-0005 S8e
            for t in ctx.procScoped.caseNarrow[i].tags:
              var isRealArm = false
              for arm in objTyFull.vArms:
                if not arm.isElse and arm.tagOrdinal == t: isRealArm = true; break
              if isRealArm and t notin tagSet: tagSet.add t
            narrowed = true
            break
        if not narrowed:
          for arm in objTyFull.vArms:
            if not arm.isElse: tagSet.add arm.tagOrdinal
        var plainFieldExprsSym: seq[IRExpr]
        for i, fieldName in objTyFull.vPlainFieldNames:
          plainFieldExprsSym.add parseVariantCtorField(
            fieldName, objTyFull.vPlainFieldTypes[i], byNameDisc, n, preamble, ctx)
        let resultVar = freshSynth(ctx, "a3VariantConstruct")
        preamble.add mkVariantConstructSym(resultVar, objTyFull, tagIR, tagSet,
                                            plainFieldExprsSym, siteLoc(n))
        return mkVar(resultVar)
      let tagOrd = int(tagIR.ival)
      var activeArm: VariantArm
      var foundArm = false
      for arm in objTyFull.vArms:
        if not arm.isElse and arm.tagOrdinal == tagOrd:
          activeArm = arm; foundArm = true; break
      # RFC-0005 S8u: a literal no explicit arm names selects the `else` arm
      # (Nim's `case` is exhaustive, so a well-typed literal that misses
      # every `of` is one the `else` covers). The discriminator is the
      # literal's own ordinal; `lowerVariantLit` makes the else arm (key -1)
      # the active one. Before S8u this declined (`feUnsupportedExprKind`).
      var tagName = activeArm.tagName
      if not foundArm:
        for arm in objTyFull.vArms:
          if arm.isElse:
            activeArm = arm; foundArm = true
            tagName = ""
            for t in objTyFull.vDiscTags:
              if t.ord == tagOrd: tagName = t.name; break
            break
      if not foundArm:
        # A genuinely bad ordinal (no arm names it and there is no `else`):
        # Nim rejects such a constructor, so this is unreachable; decline.
        preamble.add ctx.declineAtSite(
          feUnsupportedExprKind,
          siteMsg(n, "A1: variant construction with a tag not " &
                            "covered by an explicit (non-else) arm is out " &
                            "of scope"),
          "A1: else-covered/unresolved-tag " &
                                      "variant constructor unmodeled " &
                                      "(feUnsupportedExprKind)")
        # #163 regression fix (post-round-9 gate): bound dummy, not a
        # dangling `mkVar` -- see the missing-discriminant arm's comment above.
        return unsupportedFieldPlaceholder(objTyFull)
      # Shared per-field extraction for BOTH the active arm's fields and
      # the always-present plain fields — `parseVariantCtorField` mirrors
      # the itTuple constructor path's byName-based field handling
      # (P2a/P2b) just below, minimized to what A1's corpus needs (the
      # ref-field nil/degrade nuances carry over so `field: nil`/omitted-
      # ref fields stay sound, not merely "not yet a crash"). A top-level
      # proc, not a closure, taking `preamble`/`ctx` explicitly: a nested
      # proc here would capture `preamble: var seq[IRStmt]` by reference,
      # which Nim rejects as a memory-safety violation.
      var armFieldExprs: seq[IRExpr]
      for i, fieldName in activeArm.fieldNames:
        armFieldExprs.add parseVariantCtorField(fieldName, activeArm.fieldTypes[i],
                                                 byNameDisc, n, preamble, ctx)
      var plainFieldExprs: seq[IRExpr]
      for i, fieldName in objTyFull.vPlainFieldNames:
        plainFieldExprs.add parseVariantCtorField(fieldName, objTyFull.vPlainFieldTypes[i],
                                                   byNameDisc, n, preamble, ctx)
      return mkVariantLit(objTyFull, tagOrd, tagName,
                           armFieldExprs, plainFieldExprs)
    of itMultiVariant:
      # RFC-0005 S8p: every discriminator a literal naming an explicit
      # (non-else) arm of its axis builds a real `svMultiVariant`
      # (`iekMultiVariantLit`, A1's literal construction once per axis).
      # Before S8p every multi-variant constructor took the decline below,
      # whose int stand-in reached `retBindEq` as a kind mismatch when a
      # callee returned it (`weInternalWalkerFault`).
      var byNameMV = initTable[string, NimNode]()
      for k in 1 ..< n.len:
        if n[k].kind == nnkExprColonExpr:
          byNameMV[n[k][0].strVal] = n[k][1]
      var mvTags: seq[int]
      var mvFields: seq[seq[IRExpr]]
      var mvOk = true
      for ax in objTyFull.mvAxes:
        if not byNameMV.hasKey(ax.discName): mvOk = false; break
        let tagIR = discTagLit(parseExpr(byNameMV[ax.discName], preamble, ctx))
        if tagIR.kind != iekIntLit: mvOk = false; break
        var found = false
        # RFC-0005 S8u: a literal no explicit arm of this axis names selects
        # its `else` arm, as in the single-case arm above.
        var namesExplicit = false
        for arm in ax.arms:
          if not arm.isElse and arm.tagOrdinal == int(tagIR.ival):
            namesExplicit = true
        for arm in ax.arms:
          if (if namesExplicit: not arm.isElse and arm.tagOrdinal == int(tagIR.ival)
              else: arm.isElse):
            var fs: seq[IRExpr]
            for i, fieldName in arm.fieldNames:
              fs.add parseVariantCtorField(fieldName, arm.fieldTypes[i],
                                           byNameMV, n, preamble, ctx)
            mvTags.add int(tagIR.ival)
            mvFields.add fs
            found = true
            break
        if not found: mvOk = false; break
      if mvOk:
        var mvPlain: seq[IRExpr]
        for i, fieldName in objTyFull.mvPlainFieldNames:
          mvPlain.add parseVariantCtorField(fieldName, objTyFull.mvPlainFieldTypes[i],
                                            byNameMV, n, preamble, ctx)
        return mkMultiVariantLit(objTyFull, mvTags, mvFields, mvPlain)
      # Round-6 A1: retained decline, split into its OWN arm (see the
      # `of itVariant:` comment above for why un-splitting is a named DoD
      # item, not an assumed side effect). Message updated to cite
      # ADR-0029's explicit non-goal instead of P2b's now-superseded
      # "variant construction needs its own ADR" framing. RFC-0005 S8p:
      # now only a symbolic or else-covered discriminator reaches it.
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        siteMsg(n, "itMultiVariant (multi-case) object constructor " &
                          "is out of scope — ADR-0029 ships multi-case " &
                          "construction as its own slice only if a " &
                          "consumer needs it first"),
        "itMultiVariant object constructor " &
                                    "unmodeled (feUnsupportedExprKind)")
      # #163 regression fix (post-round-9 gate): a BOUND, type-correct dummy
      # (mirrors `declineIntWidthConv`'s "never an unbound `mkVar`"
      # precedent) -- NOT a dangling `mkVar(freshSynth(...))` reference into
      # an env slot no LET statement ever binds. Confirmed via
      # `tests/tsymex_r6_a1_variantlit.nim`'s A1-5: `let t = <this decline>`
      # bound `t` to a reference to a never-defined fresh name; reading it
      # via `t.a1` at walk time raised `KeyError`, silently swallowed by the
      # known C-backend nested-`walkBlock` exception-loss quirk (SND-3/
      # ADR-0023) -- masked, not sound, and #163's `iekVar` global-read fix
      # (`runtime.nim`) closed that swallow, which then surfaced the
      # dangling reference as a genuine crash one level further down
      # (`isVariantField` hitting a wrongly-kinded `svBV64` substitute
      # instead of raising cleanly on the missing key).
      return unsupportedFieldPlaceholder(objTyFull)
    of itTuple, itRef, itPtr:
      discard   ## handled below
    else:
      # Defensive: an `nnkObjConstr` node should only ever classify to one of
      # the shapes above. Degrade soundly rather than crash on an unforeseen
      # shape (never reached today — belt-and-suspenders).
      preamble.add ctx.declineAtSite(
        feUnsupportedExprKind,
        siteMsg(n, "P2b: object constructor classified to an " &
                          "unexpected shape " & $objTyFull.kind),
        "P2b: unexpected object-constructor shape " &
                                    "(feUnsupportedExprKind)")
      # #163 regression fix (post-round-9 gate): bound dummy, not a
      # dangling `mkVar` -- see the missing-discriminant arm's comment above.
      return unsupportedFieldPlaceholder(objTyFull)

    let isRefCtor = objTyFull.kind in {itRef, itPtr}
    let isPtrCtor = objTyFull.kind == itPtr
    # `objTy` is always the FULL-fielded object shape: for a ref/ptr
    # constructor it's the pointee (`objTyFull.refPointeeTy`/`.ptrPointeeTy`,
    # built by `classifyObjectRecordFields`); for a plain value object it's
    # `objTyFull` itself (unchanged from pre-H1).
    let objTy = if isRefCtor:
                  (if isPtrCtor: objTyFull.ptrPointeeTy else: objTyFull.refPointeeTy)
                else: objTyFull

    var byName = initTable[string, NimNode]()
    for k in 1 ..< n.len:
      let child = n[k]
      if child.kind == nnkExprColonExpr:
        byName[child[0].strVal] = child[1]

    if isRefCtor:
      # H1 (folds in H4's core): REAL heap construction. `mkNewT` allocates a
      # fresh `Ref_T`; each PRESENT field is written via `mkFieldDerefWrite`.
      # Omitted fields are NOT written here — the universal `isNew`
      # zero-write (`runtime_heap.nim`) zero-initialises EVERY field of a
      # freshly allocated object, so a separate omitted-field zero-write here
      # would be redundant (ADR-0022 Round-2: "H4's separate omitted-field
      # zero-write is DROPPED").
      let tmp = freshSynth(ctx, "p2bNew")
      if objTy.kind in {itVariant, itMultiVariant}:
        # RFC-0005 S8l: a REF-variant constructor (`VB(k: bkB, b: x)` with
        # `VB = ref object case ...`, or `VRef(kind: ...)` with `VRef = ref
        # VObj`) -- real heap construction, as a plain ref object's above.
        # `isNew` zeroes the whole cell (discriminator ordinal 0, every plain
        # and arm field zero); the discriminator is then written (`init`: an
        # initialisation, exempt from the heap disc write's branch-change
        # `FieldDefect` check), and each
        # PRESENT field is written through the ADR-0013 field-split heap (an
        # arm field's write checks its arm against the discriminator just
        # stored, so it never forks a FieldDefect here). Nim accepts a
        # non-constant discriminator only when no arm field is set, so the
        # stored value is always a legal tag. Before S8l this constructor was
        # a recorded decline (ADR-0029), because the named ref variant was
        # value-modelled.
        # A multi-variant (`MRef(a: akY, y: v, b: bkQ)` with `MRef = ref
        # MV`) is the same per axis: each axis's discriminator, then the
        # plain fields, then each axis's present arm fields.
        var axes: seq[VariantAxis]
        var plainNames: seq[string]
        var plainTypes: seq[IRType]
        if objTy.kind == itVariant:
          axes.add VariantAxis(discName: objTy.vDiscName, discTy: objTy.vDiscTy,
                               arms: objTy.vArms)
          plainNames = objTy.vPlainFieldNames
          plainTypes = objTy.vPlainFieldTypes
        else:
          axes = objTy.mvAxes
          plainNames = objTy.mvPlainFieldNames
          plainTypes = objTy.mvPlainFieldTypes
        preamble.add mkNewT(tmp, objTyFull)
        for ax in axes:
          if byName.hasKey(ax.discName):
            var tagIR = discTagLit(parseExpr(byName[ax.discName], preamble, ctx))
            # A `bool` discriminator's constant reaches the typed AST folded
            # to an int literal (`kind: true` is `1`); the heap stores a Bool.
            if ax.discTy.kind == itBool and tagIR.kind == iekIntLit:
              tagIR = mkBoolLit(tagIR.ival != 0)
            preamble.add mkFieldDerefWrite(mkVar(tmp), tagIR, ax.discTy,
                                           objTy, ax.discName, isPtrCtor,
                                           init = true)
        for i, fieldName in plainNames:
          if not byName.hasKey(fieldName): continue
          let fty = plainTypes[i]
          preamble.add mkFieldDerefWrite(mkVar(tmp),
            parseVariantCtorField(fieldName, fty, byName, n, preamble, ctx),
            fty, objTy, fieldName, isPtrCtor)
        var armDone: seq[string]
        for ax in axes:
          for arm in ax.arms:
            for i, fieldName in arm.fieldNames:
              if not byName.hasKey(fieldName) or fieldName in armDone: continue
              armDone.add fieldName
              let fty = arm.fieldTypes[i]
              preamble.add mkFieldDerefWrite(mkVar(tmp),
                parseVariantCtorField(fieldName, fty, byName, n, preamble, ctx),
                fty, objTy, fieldName, isPtrCtor)
        return mkVar(tmp)
      preamble.add mkNewT(tmp, objTyFull)
      let inOrder = parseCtorFieldsInOrder(n, objTy, preamble, ctx)  ## RFC-0005 S8ax
      for i, fieldName in objTy.fieldNames:
        if isClosureFieldTy(objTy.fields[i]) and byName.hasKey(fieldName):
          # RFC-0005 S8bn (item 6): a proc field's shadow code
          # (`procFieldCallIR`); `new` stored 0 (nil) for an omitted one.
          let valNode = byName[fieldName]
          let code = pfCode(pfObjKey(n) & "." & fieldName, valNode)
          if code == -1:
            preamble.add mkLet(freshSynth(ctx, "procFieldInit"),
                               objTy.fields[i], parseExpr(valNode, preamble, ctx))
          preamble.add mkFieldDerefWrite(mkVar(tmp), mkIntLit(code),
            tInt(64, signed = true), objTy, "@pf_" & fieldName, isPtrCtor)
          continue
        if not byName.hasKey(fieldName): continue
        let fty = objTy.fields[i]
        let isRefField = fty.kind in {itRef, itPtr}
        let valNode = byName[fieldName]
        var valIR: IRExpr
        if isRefField and valNode.kind == nnkNilLit:
          # `next: nil` — bare `parseExpr` has no general `nnkNilLit` arm
          # (only the `==`/`!=` comparison special-case above) — lower
          # directly via `mkNil` using the FIELD's OWN declared type.
          valIR = mkNil(fty)
        elif isRefField and refExprClassify(valNode).ty.kind notin {itRef, itPtr}:
          # A ref-typed field initialised from an expression that does NOT
          # resolve to a genuine ref/ptr address (e.g. an unsupported
          # sub-expression). Under H1 a bare named-ref symbol (`next:
          # otherNode`) DOES resolve to `itRef` here (classifyType no longer
          # value-unwraps it) and takes the `else` arm below — real aliasing.
          # This branch is now the narrower genuinely-unresolvable case.
          # Degrade THIS FIELD ONLY (SND-1 taints the whole run to
          # `sxUnknown`) and fill with a type-COMPATIBLE `nil` — never a
          # shape-mismatched value.
          preamble.add ctx.declineAtSite(
            feUnsupportedExprKind,
            "P2b: ref-typed field `" & fieldName & "` initialised from `" &
                   valNode.repr & "`, which does not resolve to a genuine " &
                   "ref/ptr address — this expression shape is out of scope",
            "P2b: recursive ref-field construction " &
                                        "from an unresolvable expression " &
                                        "(feUnsupportedExprKind)")
          valIR = mkNil(fty)
        elif inOrder.hasKey(fieldName):
          valIR = inOrder[fieldName]
        else:
          valIR = parseExpr(valNode, preamble, ctx)
        preamble.add mkFieldDerefWrite(mkVar(tmp), valIR, fty, objTy,
                                       fieldName, isPtrCtor)
      return mkVar(tmp)

    # P2a / P2b (pre-H1 shape, UNCHANGED): a plain (non-ref) value-object
    # constructor still builds a positional `itTuple` literal.
    var elems: seq[IRExpr]
    let inOrder = parseCtorFieldsInOrder(n, objTy, preamble, ctx)  ## RFC-0005 S8ax
    for i, fieldName in objTy.fieldNames:
      let fty = objTy.fields[i]
      let isRefField = fty.kind in {itRef, itPtr}
      if byName.hasKey(fieldName):
        let valNode = byName[fieldName]
        if isRefField and valNode.kind == nnkNilLit:
          # P2b: `next: nil` — bare `parseExpr` has no general `nnkNilLit` arm
          # (only the `==`/`!=` comparison special-case, ~1104-1146 above) —
          # lower directly via `mkNil` using the FIELD's OWN declared type,
          # matching Nim's real "next is genuinely nil" semantics.
          elems.add mkNil(fty)
        elif isRefField and refExprClassify(valNode).ty.kind notin {itRef, itPtr}:
          # P2b: a ref-typed field initialised from an expression that does
          # NOT resolve to a genuine ref/ptr address. Degrade THIS FIELD ONLY
          # (SND-1 taints the whole run to `sxUnknown`) and fill with a
          # type-COMPATIBLE `nil` — never a shape-mismatched value.
          preamble.add ctx.declineAtSite(
            feUnsupportedExprKind,
            "P2b: ref-typed field `" & fieldName & "` initialised from `" &
                   valNode.repr & "`, which does not resolve to a genuine " &
                   "ref/ptr address — this expression shape is out of scope",
            "P2b: recursive ref-field construction " &
                                        "from an unresolvable expression " &
                                        "(feUnsupportedExprKind)")
          elems.add mkNil(fty)
        elif inOrder.hasKey(fieldName):
          elems.add inOrder[fieldName]
        else:
          elems.add parseExpr(valNode, preamble, ctx)
      elif isRefField:
        # P2b: an OMITTED ref-typed field is genuinely, soundly nil-initialised
        # by Nim (`mkNil`; `zeroValueForType` agrees since RFC-0005 S8m).
        elems.add mkNil(fty)
      else:
        let zv = zeroValueForType(fty)
        if zv != nil:
          elems.add zv
        else:
          preamble.add ctx.declineAtSite(
            feUnsupportedExprKind,
            "P2a: omitted field `" & fieldName & "` of type " &
                   $fty.kind & " in `" & n.repr &
                   "` has no clean zero-value encoding",
            "P2a: omitted field `" & fieldName &
                                        "` zero-value unmodeled " &
                                        "(feUnsupportedExprKind)")
          # R8 (deferred LOW finding): a KIND-correct placeholder, never a
          # bare `mkIntLit(0)` that would mistype a non-scalar field and
          # crash downstream with an unclassified `weInternalWalkerFault`
          # (see `unsupportedFieldPlaceholder`'s doc comment). The taint
          # emitted just above already forces `sxUnknown` regardless of this
          # placeholder's content.
          elems.add unsupportedFieldPlaceholder(fty)
    mkTupleLit(elems, objTy)
  else:
    # RFC-chapulin-hardening CR-2a (walker v44): expression-position catch-all
    # safety net. Previously `error()`ed at MACRO-EXPANSION time on any
    # NimNode `kind` not covered by the arms above, aborting compilation
    # outright — strictly worse than `sxUnknown` (the SUT couldn't be
    # analysed at all). Convert to the established mkUnsupported degrade
    # idiom (precedent above: A7-S3 `runeLen(symbolic)`): register a
    # classified `sevError` parseError, emit `mkUnsupported` into the
    # preamble, and return a type-correct dummy resolved from the typed AST
    # via `classifyType(n).ty` — resolvable regardless of `n.kind`.
    # Soundness: `of isUnsupported` taints `Path.uncertain` (SND-1), so any
    # witness produced downstream of this dummy is demoted to `sxUnknown` at
    # the chokepoints — the dummy can NEVER produce a false witness. It also
    # registers a `sevError` (Class-A), anchored at the marker: RFC-0005 S9
    # deleted the `capForcedUnknown` backstop that read it, and joins it with
    # the walk's reach record instead (an unreached one is a diagnostic). This is the
    # catch-all for the whole expression-position macro-error class
    # (M2/M5/P1/P2a shapes).
    let dummyTy = classifyType(n).ty
    preamble.add ctx.declineAtSite(
      feUnsupportedExprKind,
      "CR-2a: unsupported expression kind " & $n.kind & " in `" &
             n.repr & "` — not in the supported expression fragment",
      "CR-2a: unsupported expression kind " &
                                  $n.kind & " (feUnsupportedExprKind)")
    let dummy = zeroValueForType(dummyTy)
    if dummy != nil: dummy
    else: mkIntLit(0)  # unreachable: SND-1 taint halts the walker before
                        # this value is ever read (dummyTy has no clean
                        # zero-value encoding, e.g. seq/tuple/variant/ref)

# ---- Statement parser --------------------------------------------------------

proc unsafeCastReason(n: NimNode): string =
  ## Phase 15 R11 (ADR-0010, RFC §R11 — Open Question 7 CLOSED). Classify an RHS
  ## expression as an unsafe POINTER MATERIALISATION when it is unmodelable in
  ## the logical-heap model (the heap is keyed by an abstract `Ref_T` value, not
  ## a raw machine address). Returns a non-empty `ucReason` string when `n` is
  ## such a pattern, "" otherwise. The detection is CONSERVATIVE — it keys ONLY
  ## on the two unambiguous pointer-materialisation node shapes:
  ##
  ##   * `nnkCast` whose TARGET type node is a `ptr T` (`cast[ptr T](...)`).
  ##     `nnkPtrTy` is the typed-AST node for a `ptr` cast target. A `cast`
  ##     between non-pointer VALUE types (if ever reached) is NOT matched here.
  ##   * `nnkAddr` (`addr x` / `unsafeAddr x` — both lower to `nnkAddr` in the
  ##     typed AST) — taking the address of a local materialises a raw pointer.
  ##
  ## Anything else returns "" and parses as before (the guard never fires on
  ## ordinary value expressions, so a no-cast SUT is unaffected — Invariant: no
  ## over-trigger).
  case n.kind
  of nnkCast:
    if n.len >= 1 and n[0].kind == nnkPtrTy:
      "cast[ptr T]"
    else:
      ""
  of nnkAddr:
    # `addr x` and `unsafeAddr x` are indistinguishable in the typed AST (both
    # `nnkAddr`); the reason string names the pointer-taking operation.
    "addr"
  else:
    ""

# ---- A3 (ADR-0014): closure/inline iterator inlining -------------------------
#
# A `for x in it(args):` whose iterable is a direct call to a user-defined
# iterator is desugared at parse time by INLINING the iterator body — exactly
# as the Nim compiler expands an inline iterator. The transform produces only
# existing IR (isWhile/isIf/isLet/…), reuses the whole walker (including the
# `isWhile` bounded-unroll), and needs no new IR node.
#
# Only direct calls qualify in A3-S1. First-class resumable iterators (stored
# in a var, passed as a param) remain sxUnknown (D6, out of A3-S1 scope).
#
# Pre-scans (D2 step 0) mechanize all degradation promises so no unsound path
# is ever silently mis-modeled (Invariant 3).

proc hasYieldShallow(n: NimNode): bool =
  ## True iff `n` contains ≥1 `nnkYieldStmt` outside nested routine
  ## definitions. Used for pre-scan 0(a): require at least one surface yield
  ## so a post-transf state-machine lowering (which removes yield leaves) is
  ## caught and degraded (ADR-0014 D2-0a, CRIT-4).
  case n.kind
  of nnkYieldStmt: return true
  of nestedRoutineScanBoundary: return false  ## don't cross routine boundary
  else:
    for c in n:
      if hasYieldShallow(c): return true
    false

proc hasReturnShallow(n: NimNode): bool =
  ## True iff `n` contains a `nnkReturnStmt` outside nested routines.
  ## Pre-scan 0(b): a bare iterator `return` (early-finish) inlines to a
  ## proc-`return` which either drops the path or leaves a caller `retSym`
  ## unconstrained → false positive (CRIT-1, ADR-0014 D4-3).
  case n.kind
  of nnkReturnStmt: return true
  of nestedRoutineScanBoundary: return false
  else:
    for c in n:
      if hasReturnShallow(c): return true
    false

proc hasKindShallow(n: NimNode, kinds: set[NimNodeKind]): bool =
  ## Shared walk behind `hasBreakContinueShallow`/`hasContinueShallow`: true
  ## iff `n` contains a node whose kind is in `kinds`, outside nested loops
  ## or routines (both stop the descent at the same boundary kinds — only
  ## the matched-kind set differs between the two callers).
  if n.kind in kinds: return true
  case n.kind
  of nnkWhileStmt, nnkForStmt: return false     ## nested loop owns break/continue
  of nestedRoutineScanBoundary: return false
  else:
    for c in n:
      if hasKindShallow(c, kinds): return true
    false

proc hasBreakContinueShallow(n: NimNode): bool =
  ## True iff `n` (the raw for-body) contains `break`/`continue` outside
  ## nested loops or routines. Pre-scan 0(c): for a finite (straight-yield)
  ## iterator the inlined body has no enclosing while, so `break` hits
  ## loopStack.len==0 → path dropped while later inlined yields still run →
  ## wrong surviving state → false positive (CRIT-2/SF-1, ADR-0014 D4-2).
  hasKindShallow(n, {nnkBreakStmt, nnkContinueStmt})

proc sameSym(a, b: NimNode): bool =
  ## RFC-chapulin-hardening R6 (ADR-0025 hardening). True iff `a` and `b` are
  ## BOTH `nnkSym` nodes denoting the SAME BINDING (true symbol identity), not
  ## merely the same printed name. Two distinct symbols that happen to share a
  ## base name (e.g. a gensym'd template-injected `i` shadowing an outer loop
  ## `i`) must compare false here.
  ##
  ## Empirically confirmed (probe against this Nim version, 2.2.10): the
  ## stdlib `macros.==(a, b: NimNode): bool` (magic `EqNimrodNode`) compares
  ## SYMBOL IDENTITY for `nnkSym` nodes — two references to the same binding
  ## compare `true`; two distinct same-named bindings in disjoint scopes
  ## compare `false`. This is exactly the semantics needed here, so `==` is
  ## used directly rather than a hand-rolled key (e.g. `.strVal` comparison,
  ## which the R6 finding identified as unsound — it matches on the printed
  ## name only).
  a.kind == nnkSym and b.kind == nnkSym and a == b

proc containsSym(syms: seq[NimNode], n: NimNode): bool =
  ## Round-6 R4 (findings W1/N8/N2, design lens). `ctx.procScoped.stringBackedParams`/
  ## `ctx.procScoped.intOffsetLiteralLocals` used to be `HashSet[string]` keyed on the
  ## qualifying symbol's PRINTED NAME — sound only as long as no other
  ## binding in scope ever shares that name. N2 confirmed a narrow
  ## same-proc collision (an unrelated same-named local in a different
  ## lexical scope inheriting the classification) and W1 confirmed a
  ## cross-proc one (an unrelated callee's same-named param inheriting the
  ## ENTRY proc's classification, since the ambient set was never scoped
  ## around a callee's recursive parse — see `ensureProcRegistered`'s own
  ## fix). Both are the same design flaw: matching by NAME where the
  ## intended semantics is "this exact BINDING". `sameSym` (R6, above) is
  ## the codebase's own established true-identity comparator for `nnkSym`
  ## nodes; `containsSym` is the linear membership test built on it — the
  ## sets involved are always small (a handful of params/locals per proc),
  ## so a linear `sameSym` scan costs nothing measurable and avoids the
  ## unsoundness a hash-of-signature proxy key (`macros.signatureHash`,
  ## considered and rejected) would reintroduce: `signatureHash` derives
  ## from a symbol's TYPE/SIGNATURE, not its binding identity, so two
  ## distinct same-typed `seq[byte]` locals would still hash identically —
  ## exactly the collision this fix exists to close.
  for s in syms:
    if sameSym(s, n): return true
  false

proc refersToSym(n: NimNode, sym: NimNode): bool =
  ## RFC-chapulin-hardening R2 (ADR-0025). True iff `n`'s subtree contains any
  ## `nnkSym` reference to the SAME BINDING as `sym` (via `sameSym`, i.e. true
  ## symbol identity — R6). Used to reject a scan-idiom match whose `bound`
  ## expression is NOT loop-invariant (reads the loop counter itself, e.g.
  ## `while i < (n - i) and ...: inc i`) — the closed-form rewrite evaluates
  ## `bound` ONCE at loop entry, so a bound that depends on `i` would silently
  ## change the program's semantics (a false-SAT/false-witness class bug).
  if sameSym(n, sym): return true
  for c in n:
    if refersToSym(c, sym): return true
  false

proc unwrapHidden(n: NimNode): NimNode =
  ## Strips compiler-inserted PASSTHROUGH wrapper nodes — `nnkHiddenAddr`,
  ## `nnkHiddenDeref`, `nnkHiddenStdConv` — to reach the underlying semantic
  ## operand, e.g. to see past a `var`/`sink` formal's lvalue wrapping or an
  ## auto-converted argument when what's needed is the RAW node shape or
  ## symbol identity (bracket-expr recognition, `sameSym` receiver matching,
  ## augmented-assignment LHS extraction, and similar).
  ##
  ## This is a BLIND, unconditional peel: unlike the dedicated one-level
  ## unwraps beside the `nnkDerefExpr`/`nnkHiddenDeref` arms of `parseExpr`
  ## and the `nnkAsgn`/`nnkDotExpr` write arms (Phase 15 R1/R3/R6/R8b,
  ## ADR-0010), it does NOT distinguish a REAL ref/ptr dereference from the
  ## `var`-ness lvalue indirection the compiler wraps around a by-ref formal
  ## — collapsing that distinction there would defeat the itRef/itPtr
  ## detection those sites depend on. Only use this helper where the result
  ## feeds a NAME/SHAPE match and any residual ref/ptr semantics of the
  ## innermost `nnkHiddenDeref` are irrelevant to that match.
  result = n
  while result.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv} and
        result.len >= 1:
    result = result[result.len - 1]

proc boundIsScannedLen(boundNode, sNode: NimNode): bool =
  ## Round-6 N7 (design-cleanup slice). True iff `boundNode` is
  ## syntactically the scanned receiver `sNode`'s own `.len` / `len(sNode)`
  ## — B0's soundness discipline: every count-dispatched scan recognizer's
  ## closed form evaluates its bound ONCE at loop entry, so the rewrite is
  ## only valid when the bound provably tracks the receiver's true length,
  ## never a caller-supplied alias that could diverge from it mid-loop.
  ## Extracted from FOUR verbatim-identical copies (one per recognizer —
  ## Q1/B0's `tryMatchScanIdiomShape`, B3's `tryMatchScanPairIdiomShape`,
  ## B4's `tryMatchAccumulatingScanIdiomShape`, B6's
  ## `tryMatchPairLoopIdiomShape`), the review ledger's Q3-class finding
  ## applied to this file's OTHER (non-collector) duplicated sub-shape: the
  ## bound-is-len fact every recognizer in the family independently
  ## re-derives about "what does this loop's bound MEAN", now asked once as
  ## a named predicate instead of re-inlined at each site.
  let boundCore = unwrapHidden(boundNode)
  if boundCore.kind in {nnkCall, nnkCommand} and boundCore.len == 2 and
     boundCore[0].kind == nnkSym and isBuiltinNamed(boundCore[0], ["len"]) and
     sameSym(unwrapHidden(boundCore[1]), sNode):
    return true
  if boundCore.kind == nnkDotExpr and boundCore.len == 2 and
     boundCore[1].kind in {nnkSym, nnkIdent} and
     isBuiltinNamed(boundCore[1], ["len"]) and
     sameSym(unwrapHidden(boundCore[0]), sNode):
    return true
  false

proc counterAdvancesByOne(stmt, iNode: NimNode): bool =
  ## Round-6 N7 (design-cleanup slice). True iff `stmt` is exactly
  ## `inc <iNode>` (default step, or an explicit literal step of `1`) or
  ## `<iNode> = <iNode> + 1` — the two spellings every count-dispatched
  ## scan recognizer accepts for "this loop's own counter advances by
  ## exactly one per iteration", the other half of what makes the bound
  ## comparison above a sound loop-trip-count fact. Extracted from THREE
  ## verbatim-identical copies (Q1/B0, B3, B4's shape matchers) — B6's own
  ## counter advance is a genuinely DIFFERENT shape (`<i> = <p2>`, assigned
  ## from a chained helper call's own return, not a literal +1), so its
  ## shape matcher does not consult this predicate; the family's true
  ## "advance form" fact has exactly two members, not four, and this
  ## predicate names precisely that.
  if stmt.kind in {nnkCall, nnkCommand} and stmt.len in {2, 3} and
     stmt[0].kind == nnkSym and isBuiltinNamed(stmt[0], ["inc"]):
    let recv = unwrapHidden(stmt[1])
    let stepOk = stmt.len == 2 or
                 (stmt[2].kind == nnkIntLit and stmt[2].intVal == 1)
    return stepOk and sameSym(recv, iNode)
  elif stmt.kind == nnkAsgn and stmt.len == 2:
    let lhs = unwrapHidden(stmt[0])
    # #163 review R28: for a `range[lo..hi]`-typed `<iNode>`, `<i> + 1`
    # computes as plain `int` and Nim's typed AST wraps the WHOLE RHS in an
    # `nnkHiddenStdConv` narrowing it back to the declared range for the
    # assignment (the same range-check conversion `isAssign`'s plain-assign
    # arm already carries) -- confirmed empirically: `stmt[1]` is
    # `HiddenStdConv(Infix("+", i, 1))`, not a bare `nnkInfix`, whenever
    # `iNode` is ranged. Unwrap it before inspecting its shape. The
    # `<i>` OPERAND inside the `+` gets its OWN separate widening wrap for
    # the same reason the comparison operand above does, so it needs
    # unwrapping too.
    let rhs = unwrapHidden(stmt[1])
    return sameSym(lhs, iNode) and
           rhs.kind == nnkInfix and rhs.len == 3 and isBuiltinNamed(rhs[0], ["+"]) and
           sameSym(unwrapHidden(rhs[1]), iNode) and
           rhs[2].kind == nnkIntLit and rhs[2].intVal == 1
  false

type ScanShapeMatch = tuple[iNode, boundNode, sNode, litNode: NimNode]

proc tryMatchScanIdiomShape(n: NimNode): Option[ScanShapeMatch] =
  ## Round-6 B1 (ADR-0028 Leg 1) extraction. The STRUCTURAL half of the
  ## canonical scan-idiom shape check —
  ##   while <i> < <bound> and <s>[<i>] != <lit>: inc <i>
  ## (or the `<i> = <i> + 1` body spelling), with `<bound>` syntactically
  ## `<s>`'s own `.len`/`len(<s>)` and LOOP-INVARIANT (does not reference
  ## `<i>`) — shared VERBATIM by `tryRecognizeScanIdiom` (the closed-form
  ## RECOGNIZER below, itString-receiver-gated, behavior unchanged from
  ## Q1/B0) and `collectStringBackedByteSeqParams` (B1a's `seq[byte]`
  ## CLASSIFIER, itSeq[byte]-receiver-gated) — the RFC's "the classifier
  ## and recognizer are ONE predicate by construction": both consult this
  ## ONE shape check and can never diverge on what counts as "the scan
  ## shape". Deliberately receiver/literal-TYPE AGNOSTIC: returns the raw
  ## `<i>`/`<bound>`/`<s>`/`<lit>` nodes unevaluated (no `classifyType`
  ## dispatch on the receiver, no literal-kind gate) — each caller applies
  ## its own type gate on the returned `sNode`/`litNode`. `none` on ANY
  ## shape mismatch, mirroring the existing "when in doubt, none" doctrine.
  if n.kind != nnkWhileStmt or n.len != 2: return none(ScanShapeMatch)
  let cond = n[0]
  let body = n[1]

  # ---- guard shape: `<i> < <bound> and <s>[<i>] != <lit>` (and-shaped,
  # short-circuit order: the bound check FIRST) ----
  if cond.kind != nnkInfix or cond.len != 3 or not isBuiltinNamed(cond[0], ["and"]):
    return none(ScanShapeMatch)
  let ltPart = cond[1]
  if ltPart.kind != nnkInfix or ltPart.len != 3 or not isBuiltinNamed(ltPart[0], ["<"]):
    return none(ScanShapeMatch)
  # `!=` desugars (via a template) to
  # `StmtListExpr(Empty, Prefix("not", Infix("==", lhs, rhs)))` in the typed
  # AST (confirmed empirically via a `treeRepr` dump) — NOT a plain
  # `nnkInfix "!="`. Unwrap the StmtListExpr wrapper, then match the
  # not(==) shape; also accept a literal `nnkInfix "!="` defensively in case
  # a different desugaring reaches here (e.g. a future compiler version).
  var nePart = cond[2]
  while nePart.kind == nnkStmtListExpr and nePart.len >= 1:
    nePart = nePart[nePart.len - 1]
  var idxExprRaw: NimNode
  var litNodeRaw: NimNode
  if nePart.kind == nnkInfix and nePart.len == 3 and isBuiltinNamed(nePart[0], ["!="]):
    idxExprRaw = nePart[1]
    litNodeRaw = nePart[2]
  elif nePart.kind == nnkPrefix and nePart.len == 2 and isBuiltinNamed(nePart[0], ["not"]) and
       nePart[1].kind == nnkInfix and nePart[1].len == 3 and isBuiltinNamed(nePart[1][0], ["=="]):
    idxExprRaw = nePart[1][1]
    litNodeRaw = nePart[1][2]
  else:
    return none(ScanShapeMatch)

  # #163 review R28: a `range[lo..hi]`-typed counter compared against a
  # plain-`int` bound (`<s>.len`) is NOT syntactically bare here -- Nim's
  # typed AST wraps it in an `nnkHiddenStdConv` widening the subrange to its
  # base `int` for the generic `<` to resolve (confirmed empirically: a
  # plain `var i = 0` counter reaches this point as a bare `nnkSym`, a
  # `var i: range[0..N]` counter does not). Without unwrapping first, the
  # very next `iNode.kind != nnkSym` check rejected EVERY ranged counter
  # before ever reaching the type gate -- the recognizer could not fire at
  # all for the shape R28 describes. `unwrapHidden` is the same blind,
  # identity-preserving peel `sNode`/`idxExpr` already get in this
  # function; it does not change which shapes are accepted, only lets the
  # existing `itInt` gate (which already tolerates `hasRange`, see below)
  # see past a passthrough wrapper to the real underlying symbol.
  let iNode = unwrapHidden(ltPart[1])
  let boundNode = ltPart[2]
  if iNode.kind != nnkSym or classifyType(iNode).ty.kind != itInt:
    return none(ScanShapeMatch)
  if classifyType(boundNode).ty.kind != itInt:
    return none(ScanShapeMatch)
  # R2 (CRITICAL soundness fix): the closed form evaluates `bound` ONCE at
  # loop entry, so it is only a valid rewrite of the guard when `bound` is
  # LOOP-INVARIANT. The body shape checked below constrains the loop's ONLY
  # mutated variable to be `i` itself, so `bound` is loop-invariant iff it
  # does not reference `i` at all (e.g. `while i < (n - i) and ...: inc i`
  # has a REAL guard of `2*i < n`, not the fixed `bound = n` the closed form
  # would fabricate — a false witness / wrong verdict, not just imprecision).
  if refersToSym(boundNode, iNode):
    return none(ScanShapeMatch)

  let idxExpr = unwrapHidden(idxExprRaw)
  if idxExpr.kind != nnkBracketExpr or idxExpr.len != 2:
    return none(ScanShapeMatch)
  let sNode = idxExpr[0]
  let idxInBracket = idxExpr[1]
  if sNode.kind != nnkSym:
    return none(ScanShapeMatch)
  # #163 review (R29, investigated and INERT — no code change here). This
  # `sameSym` compares `idxInBracket` raw, unlike the structurally identical
  # checks in `tryMatchScanPairIdiomShape`/`tryMatchAccumulatingScanIdiomShape`,
  # which wrap the same comparison in `unwrapHidden`. That asymmetry does not
  # cost this recognizer a ranged counter: Nim's `[]` on a string/seq/array is
  # compiler-magic accepting any Ordinal receiver directly, so a ranged `i`
  # reaches here as a bare `nnkSym`, with no `nnkHiddenStdConv` wrapper the
  # way the GENERIC `<` comparison above needs one (the `iNode` unwrap a few
  # lines up exists for exactly that reason). `tsymex_163rev_scan_counter_range`'s
  # idiom-1 case exercises a ranged counter through this exact recognizer and
  # asserts a positive `sxRaised(RangeDefect)`, which could not pass if this
  # site failed to match a ranged `idxInBracket`.
  if not sameSym(idxInBracket, iNode):
    return none(ScanShapeMatch)

  # B0 (walker v70, round-6 — LIVE soundness fix, found by the round-1
  # architect review): Z3's `str.indexOf` NEVER raises — it returns -1 for
  # an out-of-range start, indistinguishable from "delimiter absent" — so
  # lifting a loop whose bound can exceed `s.len` reported a clean
  # fall-through (false sxUnsat under tIndexError) where the real loop
  # raises IndexDefect at i == s.len. Only a bound that is SYNTACTICALLY
  # the scanned string's own `.len` is accepted; any other bound falls
  # through unrecognized to the k-unroll path, whose SND-4 index reads
  # deposit honest OOB forks. (The negative-start half of the same gap is
  # closed by the entry-read probe emitted below.)
  if not boundIsScannedLen(boundNode, sNode):
    return none(ScanShapeMatch)

  let litNode = unwrapHidden(litNodeRaw)

  # ---- body shape: EXACTLY `inc <i>` (default step) or `<i> = <i> + 1` ----
  # The typed AST materialises `inc i`'s default step explicitly as a 3rd
  # child (`Command(Sym "inc", Sym "i", IntLit 1)`), not an implicit 2-child
  # form — confirmed empirically via a treeRepr dump. Accept either arity, but a
  # 3rd child MUST be the literal `1` (an explicit non-1 step, e.g. `inc(i,
  # 2)`, is scope-narrowing: NOT the canonical idiom).
  # A single-statement while body is NOT always wrapped in `nnkStmtList` —
  # for a bare `inc i` the typed AST's `n[1]` IS the `Command` node directly
  # (confirmed empirically). Accept both shapes; a genuine
  # multi-statement body (`nnkStmtList` with len != 1) is out of scope.
  let stmt =
    if body.kind == nnkStmtList:
      if body.len != 1: return none(ScanShapeMatch)
      body[0]
    else:
      body
  if not counterAdvancesByOne(stmt, iNode):
    return none(ScanShapeMatch)
  some((iNode: iNode, boundNode: boundNode, sNode: sNode, litNode: litNode))

proc tryRecognizeScanIdiom(n: NimNode, preamble: var seq[IRStmt],
                            ctx: ParseCtx): Option[IRStmt] =
  ## RFC-chapulin-hardening Q1 (ADR-0025, walker v60). Recognizes ONLY the
  ## canonical bounded forward scan-to-literal-delimiter idiom:
  ##   while <i> < <bound> and <s>[<i>] != <lit>: inc <i>
  ## (body may also be the equivalent `<i> = <i> + 1`) and rewrites it to the
  ## closed form
  ##   <i> = (let p = <s>.find($<lit>, <i>);
  ##          if p == -1 or p >= <bound>: <bound> else: p)
  ## eliminating the loop — a finite k-unroll cannot decide a SYMBOLIC trip
  ## count, but Sequence-theory `indexOf` can. `<i>`'s CURRENT value (read
  ## as-is, whatever it was bound/rebound to) is used as the find start, so a
  ## LATER scan whose `var j = i + 1` binding derives from an EARLIER scan's
  ## result composes for free — no special-casing needed for dependent
  ## chains (RFC's finding #6, Q1's headline capability).
  ##
  ## Deliberately NARROW (a decidability-boundary recognizer, not a general
  ## loop solver): `==`-guards (skip-while), char-class/predicate scans
  ## (`s[i] in {'0'..'9'}`, `isDigit(s[i])`), backward scans, non-`inc`
  ## bodies, bodies with extra statements, and non-char delimiters are all
  ## OUT of scope and must fall through UNRECOGNIZED to the caller's
  ## unchanged `mkWhile` k-unroll path. When in doubt this returns `none` —
  ## a false-positive recognition would be UNSOUND (silently changes the
  ## program's semantics), which is strictly worse than leaving the loop as
  ## a clean `sxUnknown` degrade.
  ##
  ## `n` is the raw (untouched) `nnkWhileStmt` node, inspected BEFORE any
  ## `parseExpr`/`parseStmt` call on its `cond`/`body` children — both call
  ## sites (this proc's own `nnkWhileStmt` handling below, and
  ## `parseStmtInner`'s) invoke this FIRST. On a match, any synthetic
  ## lets/ifs the closed form needs are appended to `preamble` (caller-owned,
  ## merged exactly like any other preamble contribution) and the final
  ## `i = ...`-equivalent statement is returned as the whole loop's
  ## replacement; on `none`, the caller falls through to `mkWhile` untouched.
  ##
  ## Round-6 B1: the structural shape match now lives in
  ## `tryMatchScanIdiomShape` (shared with the byte-seq classifier); this
  ## proc applies its OWN two type gates on top — itString receiver, char-
  ## literal delimiter — exactly as before (pure refactor, no behavior
  ## change).
  let shapeOpt = tryMatchScanIdiomShape(n)
  if shapeOpt.isNone: return none(IRStmt)
  let (iNode, boundNode, sNode, litNode) = shapeOpt.get
  # Round-6 B7-rider: receiver gate widened to string-backed seq[byte]
  # receivers (BLOCKER A) — see `scanReceiverOk`'s own doc comment.
  let (recvOk, byteBacked) = scanReceiverOk(sNode, ctx)
  if not recvOk:
    return none(IRStmt)
  let litCharOpt = scanDelimiterChar(litNode, byteBacked)
  if litCharOpt.isNone:
    return none(IRStmt)

  # ---- shape matched: emit the closed form ----
  # `sIR`/`boundIR` are pure (a string param/local and an int expression with
  # no side effects reachable through this restricted symex fragment), so
  # reusing them twice below (once in the `p>=bound` comparison, once in the
  # `bound`-clamp branch) is semantically exact — identical to the original
  # loop guard re-evaluating `<bound>` on every iteration check.
  let sIR = parseExpr(sNode, preamble, ctx)
  let iIR = parseExpr(iNode, preamble, ctx)
  let boundIR = parseExpr(boundNode, preamble, ctx)
  # #163 review R28: this closed form calls `mkAssign` directly for `<i>`'s
  # counter write, bypassing the normal assignment dispatch that resolves
  # `IRStmt.isAssign.aty` (R27) -- so a `range[lo..hi]`-typed counter's
  # RangeDefect fork (`forkAssignRangeCheck`) never ran here. Resolve `aty`
  # the same way R27's three normal-dispatch sites do: `classifyType` on
  # `iNode`'s true symbol, non-nil only when it is a ranged `itInt`.
  let scanCounterCls = classifyType(iNode)
  let scanCounterTy = if scanCounterCls.ty.kind == itInt and scanCounterCls.ty.hasRange:
                        scanCounterCls.ty
                      else: nil
  # B0 (v70): the ENTIRE closed form is guarded by loop entry (`i < bound`).
  # A zero-iteration loop (entry index already at/past the bound) leaves
  # `i` UNTOUCHED in real Nim — the pre-v70 unguarded clamp overwrote it
  # with `bound` (round-6 review finding: after a not-found first scan a
  # chained second scan seeded at `s.len + 1` was silently reset to
  # `s.len`, a value divergence any later exact comparison observes).
  # Inside the guard, in loop order:
  #   1. entry-read PROBE — the real loop's first action is reading
  #      `s[i]`; one iekStrAt read deposits the SND-4 OOB fork a NEGATIVE
  #      start genuinely raises (with bound pinned to `s.len` above,
  #      i >= 0 survivors can never read out of range mid-scan);
  #   2. the find + clamp dispatch, exactly as before.
  let probeName = freshSynth(ctx, "scanEntryRead")
  let litChar = litCharOpt.get
  let litIR = mkStrLit($litChar)
  let findIR = mkStrOp(iekStrFind, "find", @[sIR, litIR, iIR])
  let p = freshSynth(ctx, "scanFind")
  let noMatchCond = mkBinop(bOr,
    mkBinop(bEq, mkVar(p), mkIntLit(-1)),
    mkBinop(bGe, mkVar(p), boundIR))
  some(mkIf(
    @[mkBranch(mkBinop(bLt, iIR, boundIR),
               mkBlock(@[
                 mkLet(probeName, tInt(8),
                       mkStrOp(iekStrAt, "[]", @[sIR, iIR])),
                 mkLet(p, tInt(64), findIR),
                 mkIf(
                   @[mkBranch(noMatchCond, mkAssign(iNode.strVal, boundIR, scanCounterTy))],
                   mkAssign(iNode.strVal, mkVar(p), scanCounterTy))]))],
    nil))

type ScanPairShapeMatch = tuple[iNode, boundNode, sNode, litNode, retNode: NimNode]

proc tryMatchScanPairIdiomShape(n: NimNode): Option[ScanPairShapeMatch] =
  ## Round-6 B3 (ADR-0028 Leg 1, int-result sibling). The structural shape
  ## check for the OTHER canonical scan idiom chapulin's twins use — an
  ## early-return-on-match scan, rather than Q1/B0's skip-while-and-clamp
  ## shape:
  ##   while <i> < <bound>:
  ##     if <s>[<i>] == <lit>:
  ##       return <expr>          # <expr> may reference <i>
  ##     inc <i>                  # (or <i> = <i> + 1)
  ## with `<bound>` syntactically `<s>`'s own `.len`/`len(<s>)` and
  ## LOOP-INVARIANT (mirrors `tryMatchScanIdiomShape`'s R2 fix verbatim —
  ## the closed form evaluates `bound` once at loop entry). Deliberately a
  ## SEPARATE predicate from `tryMatchScanIdiomShape`, not a widening of it:
  ## the guard is UN-and-shaped (no inline `!=` delimiter check — the match
  ## test lives in the body's `if`) and the body carries the early exit, so
  ## sharing one shape-check would multiply branches inside a single proc
  ## the ADR's own soundness doctrine keeps deliberately small. `none` on
  ## ANY mismatch, mirroring the "when in doubt, none" doctrine — a
  ## false-positive lift would be unsound. A body with a THIRD statement
  ## between the `if` and the `inc` (e.g. an accumulator `.add`, B4's
  ## shape) does not match here BY CONSTRUCTION (body.len != 2 rejects it)
  ## — B3 and B4's future sibling can never fire on the same loop.
  if n.kind != nnkWhileStmt or n.len != 2: return none(ScanPairShapeMatch)
  let cond = n[0]
  let body = n[1]

  # ---- guard shape: `<i> < <bound>` (plain, NOT and-shaped) ----
  # Round-2 note (standing DoD clause (d)): every check below is PURELY
  # STRUCTURAL (NimNode kind/shape only) — deliberately ordered BEFORE any
  # `classifyType` call. A plain `<` guard is not restricted to the
  # canonical scan idiom (e.g. an iterator's own `while i < n: yield ...;
  # inc i` matches this guard shape too), and `classifyType` on such a
  # node can hit the SAME "node has no type" class A5 fixed (a nested
  # routine's own loop, walked at a point where full semcheck hasn't
  # resolved every operand) — structural rejection via the BODY shape
  # (below) narrows to genuine candidates first, and the `typeKind !=
  # ntyNone` guard on every `classifyType` call site is the belt-and-
  # suspenders backstop per clause (d), applied regardless.
  if cond.kind != nnkInfix or cond.len != 3 or not isBuiltinNamed(cond[0], ["<"]):
    return none(ScanPairShapeMatch)
  # #163 review R28: unwrap a `range[lo..hi]` counter's `nnkHiddenStdConv`
  # widening to `int` before the identity check below -- see
  # `tryMatchScanIdiomShape`'s sibling comment for the full empirical
  # rationale (a ranged counter reaches this point wrapped; a plain `int`
  # one does not).
  let iNode = unwrapHidden(cond[1])
  let boundNode = cond[2]
  if iNode.kind != nnkSym:
    return none(ScanPairShapeMatch)

  # ---- body shape: EXACTLY two statements — `if <s>[<i>] == <lit>: return
  # <expr>` then `inc <i>` / `<i> = <i> + 1` ----
  if body.kind != nnkStmtList or body.len != 2:
    return none(ScanPairShapeMatch)
  let ifStmt = body[0]
  let incStmt = body[1]

  if ifStmt.kind != nnkIfStmt or ifStmt.len != 1:
    return none(ScanPairShapeMatch)
  let elifBranch = ifStmt[0]
  if elifBranch.kind != nnkElifBranch or elifBranch.len != 2:
    return none(ScanPairShapeMatch)
  let ifCond = elifBranch[0]
  var thenStmt = elifBranch[1]
  if thenStmt.kind == nnkStmtList:
    if thenStmt.len != 1: return none(ScanPairShapeMatch)
    thenStmt = thenStmt[0]
  if thenStmt.kind != nnkReturnStmt:
    return none(ScanPairShapeMatch)

  if ifCond.kind != nnkInfix or ifCond.len != 3 or not isBuiltinNamed(ifCond[0], ["=="]):
    return none(ScanPairShapeMatch)
  let idxExpr = unwrapHidden(ifCond[1])
  let litNodeRaw = ifCond[2]
  if idxExpr.kind != nnkBracketExpr or idxExpr.len != 2:
    return none(ScanPairShapeMatch)
  let sNode = idxExpr[0]
  if sNode.kind != nnkSym:
    return none(ScanPairShapeMatch)
  if not sameSym(unwrapHidden(idxExpr[1]), iNode):
    return none(ScanPairShapeMatch)

  # ---- NOW the type gates (structural candidacy already established) ----
  if iNode.typeKind == ntyNone or classifyType(iNode).ty.kind != itInt:
    return none(ScanPairShapeMatch)
  if boundNode.typeKind == ntyNone or classifyType(boundNode).ty.kind != itInt:
    return none(ScanPairShapeMatch)
  if refersToSym(boundNode, iNode):
    return none(ScanPairShapeMatch)

  # B0 discipline, reused verbatim: only a bound that is SYNTACTICALLY the
  # scanned receiver's own `.len` is accepted.
  if not boundIsScannedLen(boundNode, sNode):
    return none(ScanPairShapeMatch)

  let litNode = unwrapHidden(litNodeRaw)

  if not counterAdvancesByOne(incStmt, iNode):
    return none(ScanPairShapeMatch)

  some((iNode: iNode, boundNode: boundNode, sNode: sNode, litNode: litNode,
        retNode: thenStmt))

proc tryRecognizeScanPairIdiom(n: NimNode, preamble: var seq[IRStmt],
                                ctx: ParseCtx): Option[IRStmt] =
  ## Round-6 B3 (ADR-0028, int-result sibling of Q1/B0's
  ## `tryRecognizeScanIdiom`). Recognizes the early-return scan idiom
  ## `tryMatchScanPairIdiomShape` matches and rewrites it to the SAME
  ## closed-form primitive Q1 uses (`iekStrFind`'s 3-arg `indexOf`, symbolic
  ## start), with the not-found/OOB split B0 established:
  ##   if <i> < <bound>:                       # B0: guard by loop entry —
  ##                                            # a zero-iteration loop
  ##                                            # leaves <i> untouched
  ##     <entry-read probe: <s>[<i>]>           # B0: deposits the real
  ##                                            # IndexDefect fork a
  ##                                            # negative start raises
  ##     let p = <s>.find($<lit>, <i>)
  ##     if p == -1 or p >= <bound>:
  ##       <i> = <bound>                        # not found: the real loop
  ##                                            # ran to completion: whatever
  ##                                            # statement follows the
  ##                                            # while in the SUT (a raise,
  ##                                            # typically) executes
  ##                                            # unaffected, exactly as
  ##                                            # before
  ##     else:
  ##       <i> = p
  ##       <original `return <expr>`>           # found: <expr> is
  ##                                            # RE-PARSED (not
  ##                                            # syntactically substituted)
  ##                                            # against the just-updated
  ##                                            # `<i> = p` binding, so a
  ##                                            # `return (<i>, <i>+1)`
  ##                                            # correctly yields the FOUND
  ##                                            # position, not the entry
  ##                                            # one
  ## The `return` inside the found branch terminates that path (the walker's
  ## normal `isReturn` semantics — `walkBlock` stops on a statement that
  ## returns zero live paths); only NOT-found paths fall through to whatever
  ## the caller placed after this loop, unaffected.
  ##
  ## Same "when in doubt, none" doctrine and same two type gates as Q1's
  ## sibling — itString receiver, char-literal delimiter. Round-6 B7-rider:
  ## WIDENED to a string-backed `seq[byte]` receiver via the shared
  ## `scanReceiverOk`/`scanDelimiterChar` (closes BLOCKER A — B1's own scope
  ## note deferred this, no slice picked it up until now).
  let shapeOpt = tryMatchScanPairIdiomShape(n)
  if shapeOpt.isNone: return none(IRStmt)
  let (iNode, boundNode, sNode, litNode, retNode) = shapeOpt.get
  let (recvOk, byteBacked) = scanReceiverOk(sNode, ctx)
  if not recvOk:
    return none(IRStmt)
  let litCharOpt = scanDelimiterChar(litNode, byteBacked)
  if litCharOpt.isNone:
    return none(IRStmt)

  let sIR = parseExpr(sNode, preamble, ctx)
  let iIR = parseExpr(iNode, preamble, ctx)
  let boundIR = parseExpr(boundNode, preamble, ctx)
  # #163 review R28: same gap as `tryRecognizeScanIdiom` above -- resolve
  # `aty` by true symbol identity, same as R27's three normal-dispatch
  # sites, so this closed form's direct `mkAssign` calls carry the
  # counter's declared range type instead of defaulting to `nil`.
  let scanPairCounterCls = classifyType(iNode)
  let scanPairCounterTy = if scanPairCounterCls.ty.kind == itInt and
                              scanPairCounterCls.ty.hasRange:
                             scanPairCounterCls.ty
                           else: nil
  let probeName = freshSynth(ctx, "scanPairEntryRead")
  let litChar = litCharOpt.get
  let litIR = mkStrLit($litChar)
  let findIR = mkStrOp(iekStrFind, "find", @[sIR, litIR, iIR])
  let p = freshSynth(ctx, "scanPairFind")
  let noMatchCond = mkBinop(bOr,
    mkBinop(bEq, mkVar(p), mkIntLit(-1)),
    mkBinop(bGe, mkVar(p), boundIR))
  let foundBody = mkBlock(@[
    mkAssign(iNode.strVal, mkVar(p), scanPairCounterTy),
    parseStmt(retNode, ctx)])
  some(mkIf(
    @[mkBranch(mkBinop(bLt, iIR, boundIR),
               mkBlock(@[
                 mkLet(probeName, tInt(8),
                       mkStrOp(iekStrAt, "[]", @[sIR, iIR])),
                 mkLet(p, tInt(64), findIR),
                 mkIf(
                   @[mkBranch(noMatchCond, mkAssign(iNode.strVal, boundIR, scanPairCounterTy))],
                   foundBody)]))],
    nil))

type AccScanShapeMatch = tuple[iNode, boundNode, sNode, litNode, accNode,
                                retNode: NimNode]

proc tryMatchAccumulatingScanIdiomShape(n: NimNode): Option[AccScanShapeMatch] =
  ## Round-6 B4 (ADR-0028 Leg 1, accumulating-string sibling). Structural
  ## shape check for the THIRD canonical scan idiom chapulin's twins use —
  ## the `readCString` family: B3's early-return-on-match shape with a THIRD
  ## body statement that ACCUMULATES the pre-terminator bytes into a string
  ## as the loop advances:
  ##   while <i> < <bound>:
  ##     if <s>[<i>] == <lit>:
  ##       return <expr>              # <expr> may reference <acc>/<i>
  ##     <acc>.add(char(<s>[<i>]))    # or bare <s>[<i>] if already char-typed
  ##     inc <i>                      # (or <i> = <i> + 1)
  ## `<bound>` syntactically `<s>`'s own `.len`/`len(<s>)`, LOOP-INVARIANT
  ## (B0/B3's R2 fix, reused verbatim). DELIBERATELY a separate predicate
  ## from `tryMatchScanPairIdiomShape`, not a widening of it — B3's body is
  ## EXACTLY 2 statements (`if`, `inc`) and this shape is EXACTLY 3 (`if`,
  ## `add`, `inc`), so the two can never cross-fire on the same loop (B3's
  ## own doc comment records this as the future-proofing reason its body
  ## check is `!= 2`, not `>= 2`). `none` on ANY mismatch — "when in doubt,
  ## none".
  if n.kind != nnkWhileStmt or n.len != 2: return none(AccScanShapeMatch)
  let cond = n[0]
  let body = n[1]

  # ---- guard shape: `<i> < <bound>` (plain, NOT and-shaped) — structural
  # checks first, per standing DoD clause (d) / B3's N3 lesson: a plain `<`
  # guard also matches an iterator's own loop, and `classifyType` on such a
  # node can hit the "node has no type" crash class A5 fixed. ----
  if cond.kind != nnkInfix or cond.len != 3 or not isBuiltinNamed(cond[0], ["<"]):
    return none(AccScanShapeMatch)
  # #163 review R28: unwrap a `range[lo..hi]` counter's `nnkHiddenStdConv`
  # widening to `int` before the identity check below -- see
  # `tryMatchScanIdiomShape`'s sibling comment for the full empirical
  # rationale.
  let iNode = unwrapHidden(cond[1])
  let boundNode = cond[2]
  if iNode.kind != nnkSym:
    return none(AccScanShapeMatch)

  # ---- body shape: EXACTLY three statements — if-return, acc.add, inc ----
  if body.kind != nnkStmtList or body.len != 3:
    return none(AccScanShapeMatch)
  let ifStmt = body[0]
  let addStmt = body[1]
  let incStmt = body[2]

  if ifStmt.kind != nnkIfStmt or ifStmt.len != 1:
    return none(AccScanShapeMatch)
  let elifBranch = ifStmt[0]
  if elifBranch.kind != nnkElifBranch or elifBranch.len != 2:
    return none(AccScanShapeMatch)
  let ifCond = elifBranch[0]
  var thenStmt = elifBranch[1]
  if thenStmt.kind == nnkStmtList:
    if thenStmt.len != 1: return none(AccScanShapeMatch)
    thenStmt = thenStmt[0]
  if thenStmt.kind != nnkReturnStmt:
    return none(AccScanShapeMatch)

  if ifCond.kind != nnkInfix or ifCond.len != 3 or not isBuiltinNamed(ifCond[0], ["=="]):
    return none(AccScanShapeMatch)
  let idxExpr = unwrapHidden(ifCond[1])
  let litNodeRaw = ifCond[2]
  if idxExpr.kind != nnkBracketExpr or idxExpr.len != 2:
    return none(AccScanShapeMatch)
  let sNode = idxExpr[0]
  if sNode.kind != nnkSym:
    return none(AccScanShapeMatch)
  if not sameSym(unwrapHidden(idxExpr[1]), iNode):
    return none(AccScanShapeMatch)

  # ---- accumulator statement: `<acc>.add(char(<s>[<i>]))`, or bare
  # `<acc>.add(<s>[<i>])` when the receiver is already char-typed (the
  # itString type gate on `sNode`, applied by the caller, settles which) ----
  if addStmt.kind notin {nnkCall, nnkCommand} or addStmt.len != 3:
    return none(AccScanShapeMatch)
  if addStmt[0].kind notin {nnkSym, nnkIdent} or not isBuiltinNamed(addStmt[0], ["add"]):
    return none(AccScanShapeMatch)
  let accNode = unwrapHidden(addStmt[1])
  if accNode.kind != nnkSym:
    return none(AccScanShapeMatch)
  var addArg = unwrapHidden(addStmt[2])
  # Round-6 B7-rider fix: `char(<s>[<i>])` is an EXPLICIT type conversion,
  # which Nim's typed AST represents as `nnkConv` (confirmed empirically —
  # `treeRepr`: `Conv(Sym "char", BracketExpr(...))`), NOT `nnkCall`/
  # `nnkCommand` as this check previously assumed. That assumption was
  # never exercised pre-rider: every existing corpus entry uses an itString
  # receiver, whose `<s>[<i>]` is ALREADY char-typed, so the bare (no
  # wrapper) branch below always matched and this arm was dead code. A
  # string-backed `seq[byte]` receiver's `<s>[<i>]: byte` genuinely
  # requires the explicit `char(...)` conversion for `.add` on a `string`
  # accumulator to type-check — the shape B7-rider's widening newly makes
  # reachable — which is what surfaced this as a live bug, not merely a
  # style mismatch with `scanDelimiterChar`'s own (correctly `nnkConv`-
  # aware) `byte(...)`/`uint8(...)` unwrap.
  if addArg.kind == nnkConv and addArg.len == 2 and
     addArg[0].kind in {nnkSym, nnkIdent} and addArg[0].strVal == "char":
    addArg = unwrapHidden(addArg[1])
  elif addArg.kind in {nnkCall, nnkCommand} and addArg.len == 2 and
       addArg[0].kind in {nnkSym, nnkIdent} and addArg[0].strVal == "char":
    addArg = unwrapHidden(addArg[1])
  if addArg.kind != nnkBracketExpr or addArg.len != 2:
    return none(AccScanShapeMatch)
  if unwrapHidden(addArg[0]).kind != nnkSym or
     not sameSym(unwrapHidden(addArg[0]), sNode):
    return none(AccScanShapeMatch)
  if not sameSym(unwrapHidden(addArg[1]), iNode):
    return none(AccScanShapeMatch)

  # ---- NOW the type gates (structural candidacy already established) ----
  if iNode.typeKind == ntyNone or classifyType(iNode).ty.kind != itInt:
    return none(AccScanShapeMatch)
  if boundNode.typeKind == ntyNone or classifyType(boundNode).ty.kind != itInt:
    return none(AccScanShapeMatch)
  if refersToSym(boundNode, iNode):
    return none(AccScanShapeMatch)

  # B0 discipline, reused verbatim: only a bound that is SYNTACTICALLY the
  # scanned receiver's own `.len` is accepted.
  if not boundIsScannedLen(boundNode, sNode):
    return none(AccScanShapeMatch)

  let litNode = unwrapHidden(litNodeRaw)

  if not counterAdvancesByOne(incStmt, iNode):
    return none(AccScanShapeMatch)

  some((iNode: iNode, boundNode: boundNode, sNode: sNode, litNode: litNode,
        accNode: accNode, retNode: thenStmt))

proc tryRecognizeAccumulatingScan(n: NimNode, preamble: var seq[IRStmt],
                                   ctx: ParseCtx): Option[IRStmt] =
  ## Round-6 B4 (ADR-0028, accumulating-string sibling of Q1/B0's
  ## `tryRecognizeScanIdiom` and B3's `tryRecognizeScanPairIdiom`).
  ## Recognizes the `readCString` family idiom
  ## `tryMatchAccumulatingScanIdiomShape` matches and rewrites it to the SAME
  ## closed-form primitive Q1/B3 use (`iekStrFind`'s 3-arg `indexOf`,
  ## symbolic start), reusing B0's not-found/OOB split verbatim, plus ONE new
  ## binding for the accumulated payload:
  ##   if <i> < <bound>:                        # B0: guard by loop entry
  ##     <entry-read probe: <s>[<i>]>            # B0: real IndexDefect fork
  ##                                              # a negative start raises
  ##     let p = <s>.find($<lit>, <i>)
  ##     if p == -1 or p >= <bound>:
  ##       <i> = <bound>                          # not found: fall through
  ##     else:
  ##       <acc> = <acc's entry value> & <s>[<i> .. p - 1]
  ##       <i> = p
  ##       <original `return <expr>`>            # found: re-parsed against
  ##                                              # the just-updated <acc>/
  ##                                              # <i> bindings (B3's
  ##                                              # rebind-then-reparse
  ##                                              # technique, extended to a
  ##                                              # second variable)
  ## The payload is `<acc's entry value> & iekStrSubstr(<s>, <i>, p - 1)` —
  ## the RFC's pinned formula `iekStrSubstr(s, offset, terminatorIx - 1)`
  ## generalized to stay sound regardless of what `<acc>` already held
  ## entering the loop (every corpus shape has `var acc = ""` immediately
  ## before the loop, so the concat is a no-op in practice, but the closed
  ## form does not need to inspect that preceding statement to know it: it
  ## reads `<acc>`'s CURRENT binding at the point the loop starts, exactly
  ## like `iIR` reads `<i>`'s, per Q1's "whatever it was bound/rebound to"
  ## precedent — both `accIR` and `iIR` are captured once, before either is
  ## reassigned by this closed form). `iekStrSubstr`'s hi bound is
  ## INCLUSIVE (S3): `p - 1` excludes the terminator itself and includes the
  ## last pre-terminator character. An immediate terminator (`p == <i>` at
  ## loop entry) gives `hi < lo`, so `(hi - lo) + 1 <= 0` and Z3's
  ## `seq.extract` reports the empty string — the empty-payload case is
  ## expressible without a special case.
  ##
  ## Same "when in doubt, none" doctrine and the same two type gates as
  ## Q1/B3 — itString receiver, char-literal delimiter — plus a third: the
  ## accumulator itself must be itString (the payload is always a genuine
  ## `string` in the corpus, whether the SCANNED receiver is a real string
  ## or a string-backed `seq[byte]` — chapulin's own `readCString(data:
  ## seq[byte]): (string, int)` shape — so this third gate does NOT widen).
  ## Round-6 B7-rider: the RECEIVER gate WIDENED to a string-backed
  ## `seq[byte]` receiver via the shared `scanReceiverOk`/
  ## `scanDelimiterChar` (closes BLOCKER A — B1/B3's own scope note
  ## deferred this for the whole family, no slice picked it up until now).
  let shapeOpt = tryMatchAccumulatingScanIdiomShape(n)
  if shapeOpt.isNone: return none(IRStmt)
  let (iNode, boundNode, sNode, litNode, accNode, retNode) = shapeOpt.get
  let (recvOk, byteBacked) = scanReceiverOk(sNode, ctx)
  if not recvOk:
    return none(IRStmt)
  let litCharOpt = scanDelimiterChar(litNode, byteBacked)
  if litCharOpt.isNone:
    return none(IRStmt)
  if accNode.typeKind == ntyNone or classifyType(accNode).ty.kind != itString:
    return none(IRStmt)

  let sIR = parseExpr(sNode, preamble, ctx)
  let iIR = parseExpr(iNode, preamble, ctx)
  let accIR = parseExpr(accNode, preamble, ctx)
  let boundIR = parseExpr(boundNode, preamble, ctx)
  # #163 review R28: same gap as the other two scan recognizers -- resolve
  # `aty` by true symbol identity, same as R27's three normal-dispatch
  # sites. Only the COUNTER (`iNode`) can be ranged here; the accumulator
  # (`accNode`) is gated `itString` a few lines above, so it never carries
  # a range type and never needs an `aty`.
  let accScanCounterCls = classifyType(iNode)
  let accScanCounterTy = if accScanCounterCls.ty.kind == itInt and
                             accScanCounterCls.ty.hasRange:
                            accScanCounterCls.ty
                          else: nil
  let probeName = freshSynth(ctx, "accScanEntryRead")
  let litChar = litCharOpt.get
  let litIR = mkStrLit($litChar)
  let findIR = mkStrOp(iekStrFind, "find", @[sIR, litIR, iIR])
  let p = freshSynth(ctx, "accScanFind")
  let noMatchCond = mkBinop(bOr,
    mkBinop(bEq, mkVar(p), mkIntLit(-1)),
    mkBinop(bGe, mkVar(p), boundIR))
  let payloadIR = mkStrOp(iekStrConcat, "&",
    @[accIR, mkStrOp(iekStrSubstr, "[]",
                      @[sIR, iIR, mkBinop(bSub, mkVar(p), mkIntLit(1))])])
  let foundBody = mkBlock(@[
    mkAssign(accNode.strVal, payloadIR),
    mkAssign(iNode.strVal, mkVar(p), accScanCounterTy),
    parseStmt(retNode, ctx)])
  some(mkIf(
    @[mkBranch(mkBinop(bLt, iIR, boundIR),
               mkBlock(@[
                 mkLet(probeName, tInt(8),
                       mkStrOp(iekStrAt, "[]", @[sIR, iIR])),
                 mkLet(p, tInt(64), findIR),
                 mkIf(
                   @[mkBranch(noMatchCond, mkAssign(iNode.strVal, boundIR, accScanCounterTy))],
                   foundBody)]))],
    nil))

proc mkShortCircuitWhile(guardNode: NimNode, rawBodyNode: NimNode,
                         body: IRStmt, ctx: ParseCtx): IRStmt  ## Round-6 B6
  ## fwd decl (defined below, R14) — `tryRecognizePairLoopIdiom`'s
  ## non-member fallback branch needs it ahead of its textual definition,
  ## same pattern as `unwrapHidden`'s own fwd decl a few hundred lines up.

type CallDestructureMatch = tuple[calleeSym, sArg, startArg, aName, bName: NimNode]

proc matchCallDestructureLet(letNode: NimNode): Option[CallDestructureMatch] =
  ## Round-6 B6 (ADR-0028 leg) helper. Structural match for `let (a, b) =
  ## callee(s, start)` AS IT ARRIVES IN TYPED AST — Nim's semchecker
  ## desugars tuple-unpacking BEFORE the macro ever sees it (verified
  ## empirically via `getImpl.treeRepr` while landing this slice: NOT an
  ## `nnkVarTuple` node, which never appears in typed AST for this shape —
  ## a `LetSection` with exactly THREE `nnkIdentDefs`: a hidden tuple temp
  ## bound to the call, then each destructured name bound to
  ## `tmp[0]`/`tmp[1]`). `none` on any mismatch, same "when in doubt, none"
  ## doctrine as every sibling `tryMatch*Shape` proc in this file.
  if letNode.kind != nnkLetSection or letNode.len != 3:
    return none(CallDestructureMatch)
  for id in letNode:
    if id.kind != nnkIdentDefs or id.len != 3:
      return none(CallDestructureMatch)
  let id0 = letNode[0]
  let id1 = letNode[1]
  let id2 = letNode[2]
  let tmpSym = id0[0]
  if tmpSym.kind != nnkSym:
    return none(CallDestructureMatch)
  let callNode = unwrapHidden(id0[2])
  if callNode.kind notin {nnkCall, nnkCommand} or callNode.len != 3:
    return none(CallDestructureMatch)
  let calleeSym = callNode[0]
  if calleeSym.kind != nnkSym:
    return none(CallDestructureMatch)
  let sArg = unwrapHidden(callNode[1])
  let startArg = unwrapHidden(callNode[2])
  proc tupleGetIx(id: NimNode): tuple[name: NimNode, ok: bool] =
    let valNode = unwrapHidden(id[2])
    if valNode.kind != nnkBracketExpr or valNode.len != 2:
      return (nil, false)
    if not sameSym(unwrapHidden(valNode[0]), tmpSym):
      return (nil, false)
    let ixNode = unwrapHidden(valNode[1])
    if ixNode.kind != nnkIntLit:
      return (nil, false)
    (id[0], true)
  let (aName, aOk) = tupleGetIx(id1)
  if not aOk or unwrapHidden(id1[2])[1].intVal != 0:
    return none(CallDestructureMatch)
  let (bName, bOk) = tupleGetIx(id2)
  if not bOk or unwrapHidden(id2[2])[1].intVal != 1:
    return none(CallDestructureMatch)
  some((calleeSym: calleeSym, sArg: sArg, startArg: startArg,
        aName: aName, bName: bName))

type PairLoopShapeMatch = tuple[iNode, boundNode, sNode, calleeSym,
                                keyNode, p1Node, valNode, p2Node, pairsNode: NimNode]

proc tryMatchPairLoopIdiomShape(n: NimNode): Option[PairLoopShapeMatch] =
  ## Round-6 B6 (ADR-0028 leg, `readOptions` pair-loop). Structural shape
  ## check for chapulin's option-parsing idiom — a while loop that
  ## RE-INVOKES a B4-recognized (`readCString`-shaped) helper TWICE per
  ## iteration, chained (the second call's start is the first call's own
  ## returned offset — the same chaining B5 already threads through
  ## `calleeIntOffsetReturnPositions`), breaking on an empty key and
  ## accumulating `(key, val)` pairs:
  ##   while <i> < <bound>:              # <bound> syntactically <s>.len
  ##     let (<key>, <p1>) = <helper>(<s>, <i>)
  ##     if <key>.len == 0:
  ##       break
  ##     let (<val>, <p2>) = <helper>(<s>, <p1>)
  ##     <pairs>.add((<key>, <val>))
  ##     <i> = <p2>
  ## `<helper>` must be the SAME callee both times, and its OWN body must
  ## itself match `tryMatchAccumulatingScanIdiomShape` (B4) — "when in
  ## doubt, none": a helper that merely LOOKS chained but isn't a genuine
  ## readCString-shaped scan is left unrecognized, same discipline B5's
  ## `calleeIntOffsetReturnPositions` uses for its own callee introspection.
  ## Deliberately narrow to a TOP-LEVEL `while` (wired only at `parseStmt`'s
  ## own `nnkWhileStmt` arm, not `parseIterBodyStmt`'s nested for/iterator
  ## variant) — chapulin's `readOptions` is always a plain top-level loop;
  ## widening to a for/iterator-nested pair-loop is unneeded corpus surface
  ## and would require threading the fallback branch's `iterVarBindings`/
  ## `forBodyNode` context, out of scope for this slice.
  if n.kind != nnkWhileStmt or n.len != 2: return none(PairLoopShapeMatch)
  let cond = n[0]
  let body = n[1]
  if cond.kind != nnkInfix or cond.len != 3 or not isBuiltinNamed(cond[0], ["<"]):
    return none(PairLoopShapeMatch)
  let iNode = cond[1]
  let boundNode = cond[2]
  if iNode.kind != nnkSym: return none(PairLoopShapeMatch)
  if body.kind != nnkStmtList or body.len != 5: return none(PairLoopShapeMatch)

  let call1Opt = matchCallDestructureLet(body[0])
  if call1Opt.isNone: return none(PairLoopShapeMatch)
  let call1 = call1Opt.get
  if call1.sArg.kind != nnkSym: return none(PairLoopShapeMatch)
  let sNode = call1.sArg
  if not sameSym(call1.startArg, iNode): return none(PairLoopShapeMatch)
  let keyNode = call1.aName
  let p1Node = call1.bName

  # ---- stmt1: `if <key>.len == 0: break` ----
  let ifStmt = body[1]
  if ifStmt.kind != nnkIfStmt or ifStmt.len != 1: return none(PairLoopShapeMatch)
  let elifBranch = ifStmt[0]
  if elifBranch.kind != nnkElifBranch or elifBranch.len != 2:
    return none(PairLoopShapeMatch)
  let ifCond = elifBranch[0]
  var breakBody = elifBranch[1]
  if breakBody.kind == nnkStmtList:
    if breakBody.len != 1: return none(PairLoopShapeMatch)
    breakBody = breakBody[0]
  if breakBody.kind != nnkBreakStmt: return none(PairLoopShapeMatch)
  if ifCond.kind != nnkInfix or ifCond.len != 3 or not isBuiltinNamed(ifCond[0], ["=="]):
    return none(PairLoopShapeMatch)
  let zeroLit = unwrapHidden(ifCond[2])
  if zeroLit.kind != nnkIntLit or zeroLit.intVal != 0:
    return none(PairLoopShapeMatch)
  let lenExpr = unwrapHidden(ifCond[1])
  var keyLenOk = false
  if lenExpr.kind in {nnkCall, nnkCommand} and lenExpr.len == 2 and
     lenExpr[0].kind in {nnkSym, nnkIdent} and isBuiltinNamed(lenExpr[0], ["len"]) and
     sameSym(unwrapHidden(lenExpr[1]), keyNode):
    keyLenOk = true
  elif lenExpr.kind == nnkDotExpr and lenExpr.len == 2 and
       lenExpr[1].kind in {nnkSym, nnkIdent} and isBuiltinNamed(lenExpr[1], ["len"]) and
       sameSym(unwrapHidden(lenExpr[0]), keyNode):
    keyLenOk = true
  if not keyLenOk: return none(PairLoopShapeMatch)

  # ---- stmt2: `let (<val>, <p2>) = <helper>(<s>, <p1>)` — chained, same callee ----
  let call2Opt = matchCallDestructureLet(body[2])
  if call2Opt.isNone: return none(PairLoopShapeMatch)
  let call2 = call2Opt.get
  if not sameSym(call2.calleeSym, call1.calleeSym): return none(PairLoopShapeMatch)
  if call2.sArg.kind != nnkSym or not sameSym(call2.sArg, sNode):
    return none(PairLoopShapeMatch)
  if not sameSym(call2.startArg, p1Node): return none(PairLoopShapeMatch)
  let valNode = call2.aName
  let p2Node = call2.bName

  # ---- stmt3: `<pairs>.add((<key>, <val>))` ----
  let addStmt = body[3]
  if addStmt.kind notin {nnkCall, nnkCommand} or addStmt.len != 3:
    return none(PairLoopShapeMatch)
  if addStmt[0].kind notin {nnkSym, nnkIdent} or not isBuiltinNamed(addStmt[0], ["add"]):
    return none(PairLoopShapeMatch)
  let pairsNode = unwrapHidden(addStmt[1])
  if pairsNode.kind != nnkSym: return none(PairLoopShapeMatch)
  let tupleArg = unwrapHidden(addStmt[2])
  if tupleArg.kind notin {nnkTupleConstr, nnkPar} or tupleArg.len != 2:
    return none(PairLoopShapeMatch)
  if not sameSym(unwrapHidden(tupleArg[0]), keyNode): return none(PairLoopShapeMatch)
  if not sameSym(unwrapHidden(tupleArg[1]), valNode): return none(PairLoopShapeMatch)

  # ---- stmt4: `<i> = <p2>` ----
  let asgnStmt = body[4]
  if asgnStmt.kind != nnkAsgn or asgnStmt.len != 2: return none(PairLoopShapeMatch)
  if not sameSym(unwrapHidden(asgnStmt[0]), iNode): return none(PairLoopShapeMatch)
  if not sameSym(unwrapHidden(asgnStmt[1]), p2Node): return none(PairLoopShapeMatch)

  # ---- NOW the type gates (structural candidacy already established, per
  # B3's N3 lesson: purely structural checks first, `classifyType` only
  # after) ----
  if iNode.typeKind == ntyNone or classifyType(iNode).ty.kind != itInt:
    return none(PairLoopShapeMatch)
  if boundNode.typeKind == ntyNone or classifyType(boundNode).ty.kind != itInt:
    return none(PairLoopShapeMatch)
  if refersToSym(boundNode, iNode): return none(PairLoopShapeMatch)
  # Round-6 B7-rider: the receiver's itString-vs-string-backed-seq[byte]
  # gate moved OUT of this shape-match predicate and into the recognizer
  # (`tryRecognizePairLoopIdiom`, below) — mirroring Q1/B3/B4's own
  # discipline of leaving the RECEIVER type gate to the recognizer, not the
  # structural shape-match. This is not just cosmetic: this predicate is
  # also called from `collectStringBackedByteSeqParams` (the very collector
  # that BUILDS `ctx.procScoped.stringBackedParams`) to detect pair-loop-shaped
  # candidates — gating on itString HERE would make a byte-backed `data`
  # param permanently unrecognizable (the classifier could never see past
  # this predicate to mark it, since `ctx.procScoped.stringBackedParams` does not
  # exist yet at classification time). `sNode`'s type is NOT constrained by
  # this predicate at all; only that it is a genuine symbol (already
  # checked above via `call1.sArg.kind != nnkSym`).
  if pairsNode.typeKind == ntyNone: return none(PairLoopShapeMatch)
  let pairsCls = classifyType(pairsNode)
  if pairsCls.ty.kind != itSeq or pairsCls.ty.seqElemTy.kind != itTuple or
     pairsCls.ty.seqElemTy.fields.len != 2 or
     pairsCls.ty.seqElemTy.fields[0].kind != itString or
     pairsCls.ty.seqElemTy.fields[1].kind != itString:
    return none(PairLoopShapeMatch)

  # B0 discipline, reused verbatim: only a bound that is SYNTACTICALLY the
  # scanned receiver's own `.len` is accepted.
  if not boundIsScannedLen(boundNode, sNode):
    return none(PairLoopShapeMatch)

  # The callee itself must be a genuine B4 (readCString) closed form —
  # "when in doubt, none": a same-shaped-but-different helper (e.g. one
  # that doesn't scan/terminate the same way) is left unrecognized rather
  # than assumed.
  let impl = resolveRoutineImpl(call1.calleeSym)
  if impl == nil: return none(PairLoopShapeMatch)
  let calleeBody = impl[6]
  if calleeBody.kind == nnkEmpty: return none(PairLoopShapeMatch)
  var calleeMatched = false
  proc scanForAccShape(nn: NimNode) =
    if calleeMatched or nn == nil or nn.kind == nnkEmpty: return
    if nn.kind == nnkWhileStmt and tryMatchAccumulatingScanIdiomShape(nn).isSome:
      calleeMatched = true
      return
    for c in nn: scanForAccShape(c)
  scanForAccShape(calleeBody)
  if not calleeMatched: return none(PairLoopShapeMatch)

  some((iNode: iNode, boundNode: boundNode, sNode: sNode,
        calleeSym: call1.calleeSym, keyNode: keyNode, p1Node: p1Node,
        valNode: valNode, p2Node: p2Node, pairsNode: pairsNode))

proc tryRecognizePairLoopIdiom(n: NimNode, preamble: var seq[IRStmt],
                               ctx: ParseCtx): Option[IRStmt] =
  ## Round-6 B6 (ADR-0028 leg, option-region membership). Recognizes the
  ## `readOptions` pair-loop `tryMatchPairLoopIdiomShape` matches and
  ## replaces the WHOLE loop with a two-way fork on region membership:
  ##   if <s>[<i> .. <bound>-1] ∈ ((nonzero)* "\0")*:
  ##     <certified: no defect possible here — nothing further modeled>
  ##   else:
  ##     <the ORIGINAL loop's defect-relevant statements — both chained
  ##      scans, the break-check, the index advance — k-unrolled via the
  ##      pre-existing fallback machinery, MINUS the fold (statement 3,
  ##      `<pairs>.add(...)`)>
  ## Region membership is the LOOP-SAFETY invariant, not a per-pair
  ## functional-correctness claim: STAR inner segments (round-2 depth
  ## correction) because `readCString` returns "" freely and `readOptions`
  ## accepts mid-region empty keys/all-empty values, with the canonical
  ## double-NUL terminator itself an empty segment — `plus` would reject
  ## exactly the well-formed inputs a property search generates.
  ##
  ## BOTH branches omit the fold (`<pairs>.add((<key>, <val>))`) — not just
  ## the member branch. This is the ADR-0028 text taken literally ("the
  ## no-defect proof for the whole option arm WITHOUT MODELING THE FOLD"),
  ## and empirically MANDATORY, not merely a simplification for its own
  ## sake: `itSeq[itTuple[string,string]]` has no backing in
  ## `allocateSeqDataRaw` this cycle (recorded non-goal, same class as the
  ## A6 exit-gate's own `seq[(string,string)]`-as-formal-param note), and
  ## this engine's `isIf`/`isWhile` walker (`runtime.nim`) descends into
  ## EVERY branch/iteration UNCONDITIONALLY — there is no feasibility
  ## pre-check before walking a branch's body, only after (at witness
  ## extraction). A Nim exception from an unmodeled construct (not a
  ## MODELED raise-fork — a genuine walker-internal failure) is caught only
  ## by `runSymexImpl`'s single top-level handler, which returns
  ## `sxUnknown` UNCONDITIONALLY, discarding any already-recorded `w.found`
  ## entries — so a syntactically-present-but-dynamically-infeasible
  ## `.add` on the fallback branch would silently poison the ENTIRE query,
  ## including the member branch's own clean proof (confirmed via an
  ## isolated repro while landing this slice: `r.errors` carried exactly
  ## one `seNestedSeqUnsupportedError`, sourced from the fallback branch,
  ## for a query whose ASSUMED literal satisfies the member condition —
  ## `w.found` was never even consulted). Dropping the fold is sound for
  ## every pin this slice makes (defect/raise reachability never depends
  ## on `pairs`' content — the RFC's own "no verdict depends on them in
  ## the defect search" clause) and keeps the fallback branch WALKABLE.
  ## The retained statements (both chained scans, the break-check, the
  ## index advance) are exactly the defect-relevant ones — a truncated/
  ## non-member region still reaches the SAME modeled ScanError raise arm
  ## the inner B4 closed form already provides, via ordinary per-iteration
  ## walking of those statements — no new raise/decline machinery.
  let shapeOpt = tryMatchPairLoopIdiomShape(n)
  if shapeOpt.isNone: return none(IRStmt)
  let shape = shapeOpt.get
  # Round-6 B7-rider: receiver gate widened to string-backed seq[byte]
  # receivers (BLOCKER A) — see `scanReceiverOk`'s own doc comment. Applied
  # HERE (not inside `tryMatchPairLoopIdiomShape`) so the classifier's own
  # candidate walk can still see past this predicate before
  # `ctx.procScoped.stringBackedParams` exists — see that predicate's own updated doc
  # comment for why.
  let (recvOk, _) = scanReceiverOk(shape.sNode, ctx)
  if not recvOk:
    return none(IRStmt)
  let sIR = parseExpr(shape.sNode, preamble, ctx)
  let iIR = parseExpr(shape.iNode, preamble, ctx)
  let boundIR = parseExpr(shape.boundNode, preamble, ctx)
  const foldStmtIx = 3   ## `<pairs>.add((<key>, <val>))` — see doc above
  var fbStmts: seq[IRStmt]
  for ix in 0 ..< n[1].len:
    if ix == foldStmtIx: continue
    fbStmts.add parseStmt(n[1][ix], ctx)
  let fallbackBody = mkBlock(fbStmts)
  let fallback = mkShortCircuitWhile(n[0], n[1], fallbackBody, ctx)
  # Round-6 R5 (finding S4, walker v93): the MEMBER branch below (built
  # next) is an EMPTY block — it never advances `shape.iNode` — and no
  # single closed form for its post-loop value is faithful across every
  # witness satisfying region membership (see
  # `collectPairLoopCounterConsumedAfter`'s own doc comment for the
  # concrete counter-example: the canonical double-NUL-terminated shape
  # exits at `bound - 1` via `break`, not `bound`). Whenever the counter is
  # read anywhere after the loop, skip the region-membership fast-path
  # fork ENTIRELY and use `fallback` — the SAME fold-omitted
  # `mkShortCircuitWhile` k-unroll the non-member arm already uses — as the
  # loop's WHOLE replacement. This is NOT the same as declining recognition
  # outright (`none(IRStmt)`, routing to the generic unrecognized-loop
  # path): that path parses `n[1]` UNMODIFIED, fold included, and the fold
  # statement (`<pairs>.add(...)`) is unconditionally unwalkable this cycle
  # (`itSeq[itTuple[string,string]]` has no `allocateSeqDataRaw` backing,
  # per this proc's own doc comment above) — reached for REAL (not merely
  # symbolically, as the discarded member/non-member split would keep it)
  # the instant a real iteration executes it, degrading every such query to
  # `sxUnknown`. `fallback` already omits the fold and already correctly
  # tracks `shape.iNode` via ordinary per-iteration `i = p2` walking — it
  # is the genuinely faithful (if slower, k-unroll-bounded) replacement.
  if containsSym(ctx.procScoped.pairLoopCounterConsumedAfter, shape.iNode):
    return some(fallback)
  let memberCond = mkStrOp(iekStrInOptionRegion, "optregion", @[sIR, iIR, boundIR])
  some(mkIf(@[mkBranch(memberCond, mkBlock(@[]))], fallback))

proc scanShapeReceiverMutated(body: NimNode, paramSym: NimNode): bool =
  ## Round-6 B1a mutation-fallback guard (ADR-0028 Leg 1): true iff `body`
  ## contains ANY syntactic mutation site targeting the symbol `paramName`
  ## — `<paramName>[i] = v` (the bracket-assign LHS shape `nnkAsgn`'s own
  ## LHS-dispatch already recognizes, `dsl_parser.nim` ~4443) or
  ## `<paramName>.add/del/insert(..)` (the three seq-mutation call forms
  ## the `nnkCall`/`nnkCommand` arm models, ~5091-5102). Z3 String is
  ## immutable (ADR-0006): a mutated param stays array-modeled — today's
  ## `itSeq` representation and its EXISTING per-operation classified
  ## degrades (no NEW decline site here, so no `siteMsg`/TOT-1 obligation —
  ## the fallback IS today's pre-existing behavior, just reached through an
  ## explicit exclusion instead of never being considered for
  ## string-backing in the first place).
  ##
  ## Round-6 R4 (W2a): ALSO true iff `paramName` is passed at a VAR-MODE
  ## argument position of ANY call anywhere in `body`, regardless of what
  ## the callee's own body does with it (`proc grow(s: var seq[byte]) =
  ## s.add 0` called as `grow(data)` — the direct-form checks above only
  ## ever look for a mutation SYNTACTICALLY local to `body` itself, missing
  ## this indirection entirely). Deliberately an OVER-APPROXIMATION: a
  ## `var`-mode formal MIGHT not actually mutate through it, but declining
  ## the string-backed classification over a param that turns out to be
  ## harmless only costs a missed optimization (falls back to the
  ## pre-existing array-model k-unroll path, still sound) — whereas
  ## classifying a genuinely-mutated receiver string-backed is the crash
  ## class this finding exists to close (an `svString` value reaching
  ## `iekSeqAdd`'s receiver arm, `runtime.nim`). The callee is resolved via
  ## the shared `resolveRoutineImpl` core (not raw `getImpl`) so an
  ## unresolvable callee (a bare template, an unwalkable routine kind)
  ## degrades to "not proven var" instead of risking the A5/W3
  ## non-catchable-compile-error hazard class.
  ##
  ## Round-6 N25 (Low): every receiver check below used to compare
  ## `recv.strVal == paramName` — a bare PRINTED-NAME match — even though
  ## `paramSym` (this proc's own parameter, now the formal's true `nnkSym`
  ## node instead of a `string`) has real binding identity available via
  ## the house `sameSym` primitive. A nested-scope SHADOW local sharing the
  ## real formal's name (e.g. `block: var data = @[...]; grow(data)`, where
  ## `grow`'s `var` formal mutates only the SHADOW) matched by name and
  ## wrongly vetoed the REAL formal's string-backed classification —
  ## false-positive-only (the same "when in doubt, decline" doctrine this
  ## whole veto already follows: an over-cautious exclusion only costs a
  ## missed closed-form promotion, never a wrong verdict), but still worth
  ## closing since the collectors it feeds (`considerCandidate`,
  ## `markSymOrRootParam`) were already migrated to symbol identity in R4.
  ## `sameSym` throughout, never `strVal`.
  proc scan(n: NimNode): bool =
    if n == nil or n.kind == nnkEmpty: return false
    case n.kind
    of nnkAsgn:
      if n.len == 2:
        let lhs = unwrapHidden(n[0])
        if lhs.kind == nnkBracketExpr and lhs.len == 2:
          let recv = unwrapHidden(lhs[0])
          if recv.kind == nnkSym and sameSym(recv, paramSym):
            return true
    of nnkCall, nnkCommand:
      if n.len >= 2 and n[0].kind in {nnkSym, nnkIdent} and
         n[0].strVal in ["add", "del", "insert"]:
        let recv = unwrapHidden(n[1])
        if recv.kind == nnkSym and sameSym(recv, paramSym):
          return true
      if n.len >= 1 and n[0].kind == nnkSym:
        let calleeImpl = resolveRoutineImpl(n[0])
        if calleeImpl != nil:
          let calleeFormals = calleeImpl[3]
          var idx = 0
          for i in 1 ..< calleeFormals.len:
            let id = calleeFormals[i]
            let isVarFormal = id[id.len - 2].kind == nnkVarTy
            for j in 0 ..< id.len - 2:
              let argPos = idx + 1   ## n[0] is the callee sym itself
              if isVarFormal and argPos < n.len:
                let arg = unwrapHidden(n[argPos])
                if arg.kind == nnkSym and sameSym(arg, paramSym):
                  return true
              inc idx
    else: discard
    for child in n:
      if scan(child): return true
    false
  scan(body)

proc findDeclInit(n: NimNode, target: NimNode): NimNode =
  ## Round-6 Q3 (design-cleanup slice; extracted from three independent
  ## copies of this exact traversal — see the review ledger's Q3 finding).
  ## Shared search core for every "trace this symbol back to its own
  ## declaration site" collector below. Depth-first search for a
  ## `var <target> = <initExpr>` / `let <target> = <initExpr>` anywhere in
  ## `n`; returns the (unwrapped) initializer expression of the FIRST
  ## matching declaration found (true binding identity via `sameSym`, never
  ## a name match), `nil` when no such declaration exists. Deliberately
  ## stops at the first match and does not keep searching afterward, even
  ## when the caller's own predicate on that match ultimately declines it —
  ## Nim forbids redeclaring the same binding within one scope, and a
  ## shadowing redeclaration in a nested scope is a DIFFERENT symbol
  ## (`sameSym` would not match it there), so "first match" and "only
  ## match" coincide by construction. Callers apply their own predicate to
  ## the returned node — `findRootParam` below wants a bare symbol,
  ## `collectIntOffsetLiteralLocals`'s `hasLiteralInit` wants a literal-
  ## family kind — the traversal itself has no opinion on which.
  if n == nil or n.kind == nnkEmpty: return nil
  if n.kind in {nnkVarSection, nnkLetSection}:
    for idefs in n:
      if idefs.kind == nnkIdentDefs and idefs.len >= 3 and
         sameSym(idefs[0], target):
        return unwrapHidden(idefs[^1])
  for child in n:
    let r = findDeclInit(child, target)
    if r != nil: return r
  nil

proc findRootParam(n: NimNode, target: NimNode): NimNode =
  ## Round-6 Q3. `target`'s own root, traced through AT MOST one direct
  ## `var <target> = <root>` / `let <target> = <root>` local rebind — `nil`
  ## unless that rebind's initializer is itself a bare symbol reference (a
  ## computed expression has no "root param" to promote). Was independently
  ## copied verbatim into `collectStringBackedByteSeqParamsImpl` and
  ## `collectIntOffsetParamsImpl` with a doc note arguing the duplication
  ## was deliberate ("the two collectors mark DIFFERENT sets for DIFFERENT
  ## reasons, sharing would couple two independent concerns") — consolidated
  ## here because that argument does not actually hold for the RESOLUTION
  ## step: `markSymOrRootParam` below takes the destination set as an
  ## explicit `into` parameter, so no state or policy is shared between the
  ## two collectors, only this pure symbol-identity lookup is.
  let initExpr = findDeclInit(n, target)
  if initExpr != nil and initExpr.kind == nnkSym: initExpr else: nil

proc markSymOrRootParam(sym: NimNode, procBody: NimNode,
                         formalSyms: seq[NimNode],
                         into: var HashSet[string]) =
  ## Round-6 Q3 (N28 hardening: acceptance is now SYMBOL-identical, not
  ## name-equal). Shared by every "one-level call trace" collector below
  ## (Round-6 B4/B7-rider): marks `sym`'s own name into `into` when `sym` IS
  ## one of the proc's own formal parameters, or when `sym` is a LOCAL that
  ## traces back to one through `findRootParam`'s single-rebind rule.
  ## No-ops on a non-symbol or a local with no traceable root — the
  ## conservative "when in doubt, don't mark" doctrine every collector in
  ## this family shares. Structurally shared (the proc body, the formals'
  ## own Sym nodes, and the target symbol all flow in as explicit arguments;
  ## the destination set flows in as `into`) rather than semantically
  ## shared: each caller still decides what its own `into` set MEANS and why
  ## a name belongs in it — this proc only performs the symbol-identity
  ## resolution both callers independently needed, verbatim.
  ##
  ## N28 (Medium, verdict-affecting for the int-offset collector — see its
  ## own walker-version doc note): BOTH acceptance tests used to be NAME
  ## checks (`sym.strVal in paramNames` / `root.strVal in paramNames`)
  ## against a `HashSet[string]` of the proc's OWN formal names, even though
  ## `sym`/`root` are true `nnkSym` nodes. A nested-scope SHADOW local
  ## sharing a formal's printed name collides both ways: (a) `sym` itself
  ## can BE the shadow (e.g. a scan's own loop-index symbol declared with
  ## the same name as an unrelated formal, never rebinding from anything),
  ## and (b) `findRootParam` can correctly resolve a rebind's root to the
  ## SHADOW's own symbol, which then wrongly reads as the unrelated FORMAL
  ## by name. Either way the formal (never actually touched by the scan)
  ## gets promoted — for the int-offset collector, an unconditional svInt
  ## promotion with no declared range (`runtime.nim`'s top-level param
  ## loop), silently losing that formal's real fixed-width wraparound
  ## semantics. Fixed by testing true symbol identity via `containsSym`
  ## (built on the house `sameSym` primitive, R6) against the proc's own
  ## formal SYMBOLS, passed in explicitly rather than flattened to names.
  if sym.kind != nnkSym: return
  if containsSym(formalSyms, sym):
    into.incl sym.strVal
  else:
    let root = findRootParam(procBody, sym)
    if root != nil and containsSym(formalSyms, root):
      into.incl root.strVal

type
  CollectorVisiting = ref seq[NimNode]
    ## Round-6 N7 (design-cleanup slice; ADR-0028 Leg 1 review ledger).
    ## Shared cycle-guard carrier for every collector that recurses across
    ## the call graph through its own recursive `Impl` overload
    ## (`collectStringBackedByteSeqParamsImpl`, `collectIntOffsetParamsImpl`)
    ## — replaces the `ref seq[NimNode]` annotation each one spelled out
    ## independently. N11's symbol-identity discipline is unchanged, only
    ## named now.

proc newCollectorVisiting(): CollectorVisiting =
  new(seq[NimNode])

proc enterVisiting(visiting: CollectorVisiting, sym: NimNode): bool =
  ## True iff `sym` (a proc's own `procDef[0]`) is ALREADY being visited —
  ## the caller should return its zero value immediately, same as the
  ## `if containsSym(visiting[], procDef[0]): return` guard every recursive
  ## collector used to spell out by hand. Otherwise marks `sym` visiting
  ## (mutates `visiting` in place) and returns false. Pure extraction of
  ## the copy-pasted containsSym/add idiom (Round-6 N11's own fix, applied
  ## twice) — no behavior change.
  if containsSym(visiting[], sym): return true
  visiting[].add sym
  false

proc traceOneCallBoundary[T](procDef: NimNode,
                              getCalleeMarked: proc(calleeImpl: NimNode): T {.closure.},
                              isMarked: proc(marked: T, formalSym: NimNode): bool {.closure.},
                              onMatch: proc(argNode: NimNode) {.closure.}) =
  ## Round-6 N7 (design-cleanup slice). The ONE shared "one-level call-
  ## boundary trace" every collector below independently hand-rolled
  ## (review ledger: "collectIntOffsetParamsImpl's walkCalls +
  ## collectIntOffsetLiteralLocals's walkCalls — near-identical: resolve
  ## callee -> ask what's marked -> walk formal positions -> mark matching
  ## actual" — `collectStringBackedByteSeqParamsImpl`'s own walkCalls is a
  ## third instance of the exact same shape, folded in here too).
  ##
  ## Walks `procDef`'s body for every direct `callee(args...)` call whose
  ## callee resolves to a real, walkable routine body (`resolveRoutineImpl`,
  ## the N2/N23-audited nil-core, never raw `getImpl`); for each of the
  ## callee's OWN formal parameters that `isMarked` accepts (against
  ## whatever `getCalleeMarked` reports for that callee), invokes `onMatch`
  ## on the call's own actual-argument node at that same formal position.
  ##
  ## Deliberately generic over `T` (a collector's own "marked" carrier —
  ## `seq[NimNode]` for the string-backed collector, `HashSet[string]` for
  ## the int-offset ones) and deliberately silent on HOW deep
  ## `getCalleeMarked` itself recurses or whether it needs a cycle guard:
  ## `collectStringBackedByteSeqParamsImpl`/`collectIntOffsetParamsImpl`
  ## close over their own `CollectorVisiting` and call themselves back
  ## through `getCalleeMarked` (transitively walking the whole call graph,
  ## guarded against cycles at each recursive entry via `enterVisiting`);
  ## `collectIntOffsetLiteralLocals` instead composes a DIFFERENT,
  ## already fully self-contained collector (`collectIntOffsetParams`) as a
  ## black box and needs no guard of its own (genuinely bounded to depth
  ## one — see its own doc comment). This proc owns only the traversal
  ## skeleton every caller previously copied by hand: the
  ## `nnkCall`/`nnkCommand` match, the callee resolution, the formal-
  ## position bookkeeping, and the recursive descent into every child node
  ## afterward. (A caller whose callee is already mid-visit simply gets an
  ## empty/absent `calleeMarked` back from its own `getCalleeMarked` — the
  ## recursive `Impl`'s own entry guard, not a check here — so this proc
  ## does not need to know about `visiting` at all.)
  proc walkCalls(n: NimNode) =
    if n == nil or n.kind == nnkEmpty: return
    if n.kind in {nnkCall, nnkCommand} and n.len >= 1 and n[0].kind == nnkSym:
      let calleeImpl = resolveRoutineImpl(n[0])
      if calleeImpl != nil:
        let calleeMarked = getCalleeMarked(calleeImpl)
        let calleeFormals = calleeImpl[3]
        var idx = 0
        for i in 1 ..< calleeFormals.len:
          let id = calleeFormals[i]
          for j in 0 ..< id.len - 2:
            if isMarked(calleeMarked, id[j]):
              let argPos = idx + 1   ## n[0] is the callee sym itself
              if argPos < n.len:
                onMatch(unwrapHidden(n[argPos]))
            inc idx
    for child in n:
      walkCalls(child)
  walkCalls(procDef[6])

proc collectStringBackedByteSeqParamsImpl(procDef: NimNode,
                                           visiting: CollectorVisiting): seq[NimNode] =
  ## Round-6 B1a (ADR-0028 Leg 1). NimNode-level PRE-PASS (Layer 1, ADR-0002
  ## — stateless, no walker dependency), invoked from `parseProc*`
  ## immediately after param classification and BEFORE `parseStmt` walks
  ## the body (Leg 1's round-2 correction: the representation choice must
  ## exist before `parseExpr`'s bracket arm makes its `iekStrSubstr`-vs-
  ## `iekSeqSlice` decision, which is baked into the IR the instant that
  ## arm returns — there is no walk-time dispatch left to gate by
  ## `runSymexImpl` entry).
  ##
  ## Recognizes a `seq[byte]` FORMAL PARAMETER as "string-backed" — later
  ## allocated via the itString machinery instead of the array `itSeq`
  ## machinery (`allocateSym`, `runtime.nim`) — iff (a) some loop anywhere
  ## in the proc body matches ANY of the family's four scan-idiom SHAPES
  ## (`tryMatchScanIdiomShape`/`tryMatchScanPairIdiomShape`/
  ## `tryMatchAccumulatingScanIdiomShape`/`tryMatchPairLoopIdiomShape` —
  ## Round-6 B7-rider: widened from Q1-shape-only, see below) scanning that
  ## param with a byte-range literal delimiter, and (b) the param has no
  ## mutation site anywhere in the body (`scanShapeReceiverMutated`).
  ## Scoped to the TOP-LEVEL proc's OWN formal parameters only —
  ## deliberately not recursed into nested `nnkProcDef`s (a callee's own
  ## string-backed-ness is its OWN parse's concern, were a future slice to
  ## extend this there; the round-6 corpus's decode twins are flat
  ## single-proc SUTs).
  ##
  ## Round-6 B7-rider (closes BLOCKER A): pre-rider, this walk ONLY tried
  ## `tryMatchScanIdiomShape` (Q1/B0's and-shaped guard) — so a `seq[byte]`
  ## param scanned EXCLUSIVELY via a B3/B4/B6-shaped loop (chapulin's own
  ## `readCString`/`readOptions` shapes — early-return-on-match, not
  ## and-shaped) was NEVER added to `ctx.procScoped.stringBackedParams` at all, no
  ## matter how the four recognizers' own receiver gates were widened
  ## downstream: the classifier itself was the missing link for those
  ## shapes. Now tries all four shape predicates per loop (mutually
  ## exclusive by construction via each shape's own body-statement-count
  ## discipline, same order `parseStmt`'s own dispatch tries them in, so a
  ## loop can only ever match one) and extracts the common `(sNode,
  ## litNodeOpt)` pair each shape carries — B6's pair-loop shape carries no
  ## delimiter literal of its own (its "delimiter" is inside the CALLEE it
  ## invokes, which is that callee's own separate parse's concern), so it
  ## reports `none` there and skips the literal check.
  ##
  ## Round-6 B7-rider addition: a ONE-LEVEL CALL TRACE (mirrors
  ## `collectIntOffsetParamsImpl`'s own "wrapper" promotion, applied to
  ## string-backing instead of int-offset-ness — see the trace's own doc
  ## comment further down for why this is a genuine composability
  ## requirement, not an optional nicety). `visiting` (a cycle guard, same
  ## role as `collectIntOffsetParamsImpl`'s) makes this proc itself
  ## recursive across direct call edges, so it now takes an explicit
  ## `visiting` parameter — `collectStringBackedByteSeqParams` (below) is
  ## the original zero-argument entry point every caller still uses.
  ##
  ## Round-6 R4 (N8/N2 design fix): returns `seq[NimNode]` (the qualifying
  ## formal params' own Sym nodes), not `HashSet[string]` — see
  ## `ProcScopedCollectors.stringBackedParams`'s doc comment for the full rationale.
  ## `paramSyms` maps each of THIS proc's own formal names to its declaring
  ## Sym node (unique within one proc's formal-param list — Nim forbids
  ## duplicate parameter names), so the final result can look up the real
  ## symbol identity for whichever names survive the mutation veto.
  # Round-6 N11 (Low; cycle-guard symbol identity): `visiting` used to be a
  # `ref HashSet[string]` keyed by `procDef[0].strVal` — a BARE PROC NAME —
  # even though the collectors THEMSELVES were already migrated to true
  # symbol identity (`seq[NimNode]` + `containsSym`/`sameSym`) back in R4.
  # Two overloads sharing a name (e.g. `helper(data: seq[byte])` and
  # `helper(data: seq[byte], flag: bool)`) collided on this one shared key:
  # recursing into the FIRST overload marked "helper" visited, so a call to
  # the SECOND, entirely-different overload later in the same body was
  # skipped outright (`calleeSym.strVal notin visiting[]` false) — the
  # second overload's own qualifying scan never traced, silently
  # under-classifying its caller-side argument (degrade-only: a missed
  # closed-form promotion, never a wrong verdict, since the un-promoted
  # argument falls back to the pre-existing sound k-unroll path). Fixed by
  # keying `visiting` on the proc's own `nnkSym` node (`containsSym`, the
  # house identity primitive) instead of its printed name — two overloads
  # are different bindings and no longer alias each other's guard entry.
  if visiting.enterVisiting(procDef[0]): return

  var paramNames: HashSet[string]
  var paramSyms: Table[string, NimNode]
  var formalSyms: seq[NimNode]
  let formalParams = procDef[3]
  for i in 1 ..< formalParams.len:
    let id = formalParams[i]
    for j in 0 ..< id.len - 2:
      paramNames.incl id[j].strVal
      paramSyms[id[j].strVal] = id[j]
      formalSyms.add id[j]
  if paramNames.len == 0: return
  var candidates: HashSet[string]
  proc considerCandidate(sNode: NimNode, litNodeOpt: Option[NimNode]) =
    # N28: symbol-identity acceptance (`containsSym`/`sameSym`, not a bare
    # `strVal` name check) — a nested-scope SHADOW local sharing a formal's
    # printed name (e.g. the scan's own receiver symbol shadowing an
    # unrelated formal) must never be mistaken for that formal here. See
    # `markSymOrRootParam`'s own doc comment for the full N28 writeup — this
    # is that same acceptance-by-name hole's direct-check sibling.
    if sNode.kind != nnkSym or not containsSym(formalSyms, sNode): return
    # Round-6 R4 (W3): guard `classifyType` with the standing DoD's
    # `typeKind != ntyNone` idiom — `sNode` may be reached while parsing a
    # MONOMORPHIZED generic callee's body (via the one-level call trace
    # below, which recurses this whole proc onto `calleeImpl`), the exact
    # A5 hard-crash class (`getTypeInst` on a typeless node is a
    # non-catchable compile error, not something a `try` can intercept).
    if sNode.typeKind == ntyNone: return
    let recvCls = classifyType(sNode)
    let isByteSeq = recvCls.ty.kind == itSeq and
                    recvCls.ty.seqElemTy.kind == itInt and
                    recvCls.ty.seqElemTy.width == 8 and
                    not recvCls.ty.seqElemTy.signed
    if not isByteSeq: return
    if litNodeOpt.isNone:
      candidates.incl sNode.strVal
      return
    # Round-6 B7-rider: delegates to the SAME `scanDelimiterChar` the four
    # recognizers themselves use (byteBacked=true — kept in lockstep so
    # classifier and recognizer can never diverge on which delimiter
    # literals qualify a byte-seq receiver, including the `byte(<lit>)`/
    # `uint8(<lit>)` conversion-call unwrap).
    if scanDelimiterChar(litNodeOpt.get, byteBacked = true).isSome:
      candidates.incl sNode.strVal
  proc walk(n: NimNode) =
    if n == nil or n.kind == nnkEmpty: return
    if n.kind == nnkWhileStmt:
      let scanOpt = tryMatchScanIdiomShape(n)
      if scanOpt.isSome:
        considerCandidate(scanOpt.get.sNode, some(scanOpt.get.litNode))
      else:
        let pairOpt = tryMatchScanPairIdiomShape(n)
        if pairOpt.isSome:
          considerCandidate(pairOpt.get.sNode, some(pairOpt.get.litNode))
        else:
          let accOpt = tryMatchAccumulatingScanIdiomShape(n)
          if accOpt.isSome:
            considerCandidate(accOpt.get.sNode, some(accOpt.get.litNode))
          else:
            let plOpt = tryMatchPairLoopIdiomShape(n)
            if plOpt.isSome:
              considerCandidate(plOpt.get.sNode, none(NimNode))
    for child in n:
      walk(child)
  walk(procDef[6])

  # ---- one-level call trace ----
  # `runtime.nim`'s `isCall` arm lowers a call's actual argument ONCE, in
  # the CALLER'S OWN env (`argVals.add lower(p.env, stmt.cargs[i],
  # argProto)`), then binds it DIRECTLY into the callee's env
  # (`calleeEnv[formal.name] = argVals[i]`) — no representation bridge.
  # Unlike `IRParam.isIntOffset` (int and BV are fungible via `toZ3Int`,
  # so an `argProto` alone suffices to bridge them), itString and itSeq
  # are DIFFERENT Z3 sorts (Sequence vs Array) with no lossless
  # reinterpretation between them. So if a callee's OWN formal is
  # string-backed (because ITS OWN body has a qualifying loop) but the
  # CALLER's corresponding argument is a bare top-level param with NO
  # qualifying loop of its OWN, the caller would allocate that param
  # array-modeled (`svSeq`) while the callee's inlined body expects
  # `svString` fed through it — a genuine representation mismatch AT THE
  # CALL BOUNDARY (confirmed empirically while landing this rider: the
  # mismatch does not crash — string ops silently thread bogus values
  # through an array-modeled receiver — so the visible symptom is a
  # WRONG VERDICT, not a decline). Without this trace, a receiver scanned
  # EXCLUSIVELY through a helper call — chapulin's own `readOptions`
  # calling `readCString`, or this file's own `tests/tsymex_r6_b7r_byte
  # scan.nim` corpus — would never compose correctly. Bounded to DIRECT
  # calls with the SAME `visiting` cycle guard `collectIntOffsetParamsImpl`
  # uses, and the SAME "at most one direct rebind" trace (Round-6 Q3: the
  # shared `findRootParam`/`markSymOrRootParam` above — see their own doc
  # comments for why consolidating them out of this proc's local scope is
  # safe).
  proc markIfParamOrLocal(sym: NimNode) =
    markSymOrRootParam(sym, procDef[6], formalSyms, candidates)

  traceOneCallBoundary[seq[NimNode]](
    procDef,
    getCalleeMarked = proc(calleeImpl: NimNode): seq[NimNode] =
      collectStringBackedByteSeqParamsImpl(calleeImpl, visiting),
    isMarked = proc(marked: seq[NimNode], formalSym: NimNode): bool =
      containsSym(marked, formalSym),
    onMatch = markIfParamOrLocal)

  for name in candidates:
    if not scanShapeReceiverMutated(procDef[6], paramSyms[name]):
      result.add paramSyms[name]

proc collectStringBackedByteSeqParams(procDef: NimNode): seq[NimNode] =
  let visiting = newCollectorVisiting()   ## N11: symbol-identity cycle guard
  collectStringBackedByteSeqParamsImpl(procDef, visiting)

proc offsetShapedElem(n: NimNode, iNode: NimNode): bool =
  ## Round-6 B5 (ADR-0028 Leg 1, chained composition). True iff `n` is the
  ## scan's own index symbol `<iNode>` itself, or a trivial `<iNode> +/-
  ## <literal>` arithmetic on it — the two shapes every B3/B4 `return
  ## <expr>` in the corpus uses for its "next scan position" component
  ## (`return (i, i + 1)`, `return (acc, i + 1)`). Deliberately narrow —
  ## "when in doubt, false" (an over-eager match would wrongly force a
  ## non-offset field to `svInt`, which is merely a missed-precision bug,
  ## not unsound, but still worth keeping tight and mirrored on the
  ## existing scope-guard doctrine).
  let core = unwrapHidden(n)
  if sameSym(core, iNode): return true
  if core.kind == nnkInfix and core.len == 3 and
     core[0].kind in {nnkSym, nnkIdent} and isBuiltinNamed(core[0], ["+", "-"]) and
     sameSym(unwrapHidden(core[1]), iNode) and
     unwrapHidden(core[2]).kind == nnkIntLit:
    return true
  false

proc scanOffsetReturnPositions(iNode, retNode: NimNode): seq[int] =
  ## Round-6 B5. `retNode` is a recognized B3/B4 loop's OWN `return <expr>`
  ## (`ScanPairShapeMatch`/`AccScanShapeMatch`'s `retNode` field). Returns
  ## the 0-based TUPLE-CONSTRUCTOR positions whose element is
  ## `offsetShapedElem` — the corpus's "next scan position" field, e.g.
  ## `return (payload, i + 1)`'s position 1. A non-tuple (scalar) `return
  ## <expr>` that is ITSELF offset-shaped reports `@[0]` (B3's plain
  ## int-result shape with no accumulation and no tuple, e.g. `return i`).
  if retNode.kind != nnkReturnStmt or retNode.len != 1: return
  # `nnkReturnStmt`'s own child is either the bare expr (untyped) or, in a
  # value-returning proc — every corpus shape — `Asgn(result, EXPR)` (the
  # semchecker's own rewrite of `return EXPR`, per `parseStmt`'s own
  # `nnkReturnStmt` arm doc comment a few hundred lines below, reused here
  # verbatim rather than re-derived).
  var inner = retNode[0]
  if inner.kind == nnkAsgn and inner[0].kind == nnkSym and
     inner[0].strVal == "result":
    inner = inner[1]
  let expr = unwrapHidden(inner)
  if expr.kind in {nnkTupleConstr, nnkPar}:
    for i in 0 ..< expr.len:
      var elem = unwrapHidden(expr[i])
      if elem.kind == nnkExprColonExpr: elem = unwrapHidden(elem[1])  ## named tuple field
      if offsetShapedElem(elem, iNode):
        result.add i
  elif offsetShapedElem(expr, iNode):
    result.add 0

proc calleeIntOffsetReturnPositions(calleeSym: NimNode): seq[int] =
  ## Round-6 B5 (ADR-0028 Leg 1, chained composition — the catalog #6
  ## finding this slice retires). Mirrors `collectIntOffsetParams`'s "which
  ## int carries a scan offset" analysis, but for a CALLEE's OWN RETURN
  ## rather than its formal params: if `calleeSym`'s body directly contains
  ## a recognized B3 (`tryMatchScanPairIdiomShape`) or B4
  ## (`tryMatchAccumulatingScanIdiomShape`) scan loop, the loop's OWN
  ## `return <expr>` genuinely carries a Sequence-theory Int at the
  ## positions `scanOffsetReturnPositions` finds (`iekStrFind`'s own
  ## result — never a BV, per `runtime_strings.nim`'s `iekStrFind` lower
  ## arm, which is unconditionally `SymVal(kind: svInt, ...)`).
  ##
  ## THE GAP this closes: `retBindEq`'s fresh call-return placeholder
  ## (`freshRetSym` -> `allocateSym`) allocates every `itInt` tuple field at
  ## its TYPE-DRIVEN default (BV) regardless of what kind the callee
  ## actually computes — `reconcileInt` (CR-9(c)) only widens the pair
  ## USED IN THE EQUALITY CONSTRAINT itself (both sides converted to
  ## `svInt` via `toZ3Int`/bv2int for the `retBindEq` proof), it does NOT
  ## change the ENV BINDING a caller's `let (_, p1) = callee(...)` sees
  ## going forward — `p1` stays BV. That is invisible for a SINGLE scan
  ## (the position is only ever read via ordinary int comparisons), but
  ## breaks CHAINING: passing `p1` on as a SECOND scan's offset argument
  ## carries it, still BV, into `iekStrSubstr`'s CR-17 Int-sortedness
  ## check inside the second call. Marking the position here lets
  ## `allocateSym`'s `itTuple`/`itInt` arms allocate `svInt` directly at
  ## call-return time — the same mechanism `IRParam.isIntOffset` already
  ## uses for TOP-LEVEL formal params, applied at the OTHER end of the
  ## data flow (a call's RETURN, not a proc's PARAM).
  ##
  ## Deliberately narrow — only the callee's OWN, directly-recognized loop
  ## (not a further-nested wrapper call) is consulted; a wrapper-of-a-
  ## wrapper composition falls back to the pre-existing BV default (a
  ## missed-precision `sxUnknown`, never a wrong verdict — "when in doubt,
  ## none" restated for this collector).
  let impl = resolveRoutineImpl(calleeSym)  ## never raises (N2's shared nil-core)
  if impl == nil: return
  let body = impl[6]
  if body.kind == nnkEmpty: return
  proc walkLoops(n: NimNode): seq[int] =
    if n == nil or n.kind == nnkEmpty: return
    if n.kind == nnkWhileStmt:
      let pairOpt = tryMatchScanPairIdiomShape(n)
      if pairOpt.isSome:
        return scanOffsetReturnPositions(pairOpt.get.iNode, pairOpt.get.retNode)
      let accOpt = tryMatchAccumulatingScanIdiomShape(n)
      if accOpt.isSome:
        return scanOffsetReturnPositions(accOpt.get.iNode, accOpt.get.retNode)
    for child in n:
      let found = walkLoops(child)
      if found.len > 0: return found
    @[]
  walkLoops(body)

proc accumulatingScanIndex(loop: NimNode): NimNode =
  ## The loop index of a B4 accumulating scan (`collectIntOffsetParams`),
  ## or nil.
  let shapeOpt = tryMatchAccumulatingScanIdiomShape(loop)
  if shapeOpt.isSome: shapeOpt.get.iNode else: nil

proc scanOffsetIndex(loop: NimNode): NimNode =
  ## RFC-0005 S8q/S8t. The loop index of a recognised scan whose closed
  ## form reads its index inside a string query, or nil
  ## (`collectScanOffsetParams`): a B3 scan-pair (early return on the
  ## delimiter, `tryMatchScanPairIdiomShape`, S8q), a Q1/B0 skip-while scan
  ## (`tryMatchScanIdiomShape`, S8t) and a B6 pair loop
  ## (`tryMatchPairLoopIdiomShape`, S8t). B4's accumulating scan has its
  ## own collector (`collectIntOffsetParams`), whose params `runSymexImpl`
  ## allocates the same way since S8t.
  let pairOpt = tryMatchScanPairIdiomShape(loop)
  if pairOpt.isSome: return pairOpt.get.iNode
  let scanOpt = tryMatchScanIdiomShape(loop)
  if scanOpt.isSome: return scanOpt.get.iNode
  let pairLoopOpt = tryMatchPairLoopIdiomShape(loop)
  if pairLoopOpt.isSome: return pairLoopOpt.get.iNode
  nil

proc collectIntOffsetParamsImpl(procDef: NimNode,
                                 visiting: CollectorVisiting,
                                 loopIndex: proc(loop: NimNode): NimNode {.nimcall.} =
                                   accumulatingScanIndex): HashSet[string] =
  ## Round-6 B4 (ADR-0028 Leg 1, ADR-0027's recorded lift — "int params
  ## whose def-use reaches an iekStrSubstr bound / iekStrFind start ->
  ## allocate svInt"). B1 left this collector unbuilt because Q1/B0/B3's
  ## closed forms only ever pass a scan's index through `iekStrAt`/
  ## `iekStrFind`, both of which tolerate a BV-allocated int via a one-way
  ## `toZ3Int` bridge. B4's payload computation is the first to need its
  ## scan's ENTRY OFFSET as `iekStrSubstr`'s LOW bound directly, and
  ## `iekStrSubstr` deliberately does NOT bridge (the CR-17 non-termination
  ## finding recorded on its own runtime arm — `runtime_strings.nim`) — so
  ## the formal PARAM feeding that offset must allocate `svInt` from the
  ## start (`allocateSym`'s `itInt` arm / `runSymexImpl`'s top-level
  ## param loop otherwise always choose a BV representation).
  ##
  ## Finds every accumulating-scan loop's `<i>` symbol (via
  ## `tryMatchAccumulatingScanIdiomShape`, the SAME predicate the B4
  ## recognizer itself consults — "one predicate by construction", B1a's
  ## own discipline extended here), then traces `<i>` to its ROOT formal
  ## parameter through AT MOST one direct `var <i> = <param>` local rebind
  ## (the shape every accumulating-scan CALLEE in the corpus uses: `var i =
  ## offset; while i < s.len: ...`).
  ##
  ## `readCString`-shaped helpers are, by their nature, called through a
  ## wrapper (`let (k, nextPos) = readCString(data, pos)` — chapulin's own
  ## `readOptions`) rather than inlined at the `symexFind` target — unlike
  ## B1a's `seq[byte]`-allocation classifier (a property of ONE proc's own
  ## body), the representation choice here must reach the OUTERMOST
  ## parameter allocation, so a param that resolves ONE call boundary
  ## outward is traced too: for every direct call `callee(args...)` in this
  ## proc's body, if `callee`'s OWN body (recursively, this SAME analysis)
  ## marks one of `callee`'s formal parameters, and the call's argument at
  ## that SAME position is a bare symbol (top-level param here, or a local
  ## itself traceable via the one-rebind rule above), that symbol is
  ## marked too. Bounded to direct calls (no further indirection than the
  ## family's real shape needs) with a `visiting` cycle guard.
  ##
  ## `none` (empty set) on anything less direct: a param that isn't
  ## provably the scan's own offset stays BV-allocated, and B4's own
  ## `iekStrSubstr` CR-17 decline (`sxUnknown`) is the safe fallback — never
  ## a wrong verdict, only a missed proof.
  # Round-6 N11 (Low; cycle-guard symbol identity) — see the identical fix's
  # doc comment on `collectStringBackedByteSeqParamsImpl` above for the full
  # writeup (same bug, same class, both collectors share it): keyed by
  # `procDef[0].strVal` pre-fix, so two overloaded procs sharing a printed
  # name collided on one shared cycle-guard entry — recursing into the first
  # overload silently blocked ever recursing into the second, unrelated one.
  if visiting.enterVisiting(procDef[0]): return

  var paramNames: HashSet[string]
  var formalSyms: seq[NimNode]
  let formalParams = procDef[3]
  for i in 1 ..< formalParams.len:
    let id = formalParams[i]
    for j in 0 ..< id.len - 2:
      paramNames.incl id[j].strVal
      formalSyms.add id[j]
  if paramNames.len == 0: return

  var iSyms: seq[NimNode]
  proc walkLoops(n: NimNode) =
    if n == nil or n.kind == nnkEmpty: return
    if n.kind == nnkWhileStmt:
      let iNode = loopIndex(n)
      if iNode != nil:
        iSyms.add iNode
    for child in n:
      walkLoops(child)
  walkLoops(procDef[6])

  # NOTE: uses an explicit local `marked` set, not the implicit `result` —
  # Nim forbids capturing a proc's `result` slot into a nested closure
  # (`markIfParamOrLocal`/`walkCalls` below both need to mutate it across
  # recursive calls) as a memory-safety violation.
  var marked: HashSet[string]

  # Round-6 Q3: the "trace `sym` to a root formal param through at most one
  # direct rebind" step used to be a verbatim-copied local `findRootParam` +
  # `markIfParamOrLocal` pair (identical to the ones in
  # `collectStringBackedByteSeqParamsImpl` above) — now the shared
  # `markSymOrRootParam`/`findRootParam` module-level procs; see their own
  # doc comments.
  proc markIfParamOrLocal(sym: NimNode) =
    markSymOrRootParam(sym, procDef[6], formalSyms, marked)

  for iSym in iSyms:
    markIfParamOrLocal(iSym)

  # One-level call trace (see doc comment above).
  traceOneCallBoundary[HashSet[string]](
    procDef,
    getCalleeMarked = proc(calleeImpl: NimNode): HashSet[string] =
      collectIntOffsetParamsImpl(calleeImpl, visiting, loopIndex),
    isMarked = proc(calleeMarked: HashSet[string], formalSym: NimNode): bool =
      formalSym.strVal in calleeMarked,
    onMatch = markIfParamOrLocal)
  marked

proc collectIntOffsetParams(procDef: NimNode): HashSet[string] =
  let visiting = newCollectorVisiting()   ## N11: symbol-identity cycle guard
  collectIntOffsetParamsImpl(procDef, visiting)

proc collectScanOffsetParams(procDef: NimNode): HashSet[string] =
  ## RFC-0005 S8q. The entry proc's `int` params that reach a scan's loop
  ## index (`scanOffsetIndex`: B3 scan-pair since S8q; Q1/B0 skip-while
  ## scan and B6 pair loop since S8t), traced exactly as
  ## `collectIntOffsetParams` traces B4's (at most one `var i = <param>`
  ## rebind, one call boundary).
  ## B3's closed form reads its index through `iekStrAt`/`iekStrFind`,
  ## which bridge a bit-vector with a signed `bv2int` (an `ite` over
  ## `bvslt`); inside a string query Z3 did not answer that bridge within
  ## its `rlimit` (`tsymex_r6_b7r_bytescan` B7R-3: past 300 s in the walk's
  ## context, `unknown` at 10M units standalone; SAT in 0.1 s with the
  ## param an Int). `runSymexImpl` allocates a marked param as a Z3 Int
  ## stamped with its Nim width and bounded by its type's range
  ## (`IRParam.isScanOffset`), which is the bit-vector's value set, so
  ## it loses no overflow obligation.
  let visiting = newCollectorVisiting()
  collectIntOffsetParamsImpl(procDef, visiting, scanOffsetIndex)

proc collectIntOffsetLiteralLocals(procDef: NimNode): seq[NimNode] =
  ## Round-6 B7r2 (walker v88). A COMPANION to `collectIntOffsetParams` for
  ## the case that collector cannot cover: a scan/pair-loop counter seeded
  ## directly from an INT LITERAL (`var pos = 2`), not a formal param or a
  ## bare-symbol rebind of one. `collectIntOffsetParamsImpl`'s own
  ## `findRootParam` correctly declines to trace THROUGH a literal (there
  ## is no param to promote — "none on anything less direct" is the right
  ## call for a genuinely SYMBOLIC def-use chain), leaving the local
  ## BV-allocated by the type-driven `intLitProto` default at the `isLet`
  ## walker arm, which then fails `iekStrSubstr`/`iekStrInOptionRegion`'s
  ## CR-17 Int-sortedness check the moment the local feeds a recognized
  ## scan/pair-loop closed form — reproduced minimally by chapulin's own
  ## B7-1 BLOCKER (a)/(b) repros (the `readOptions` pair-loop's own offset
  ## seeded by a literal, e.g. `var pos = 2` immediately after a header
  ## check, rather than threaded through as a formal param the way
  ## `tsymex_r6_b6_optionregion.nim`'s own pinned SUT does it).
  ##
  ## A LITERAL, unlike a param, carries NO such risk: its value is already
  ## fully known at PARSE time, so re-representing it as `svInt` instead of
  ## the BV default is unconditionally sound — no def-use tracing needed,
  ## just "does this exact loop-counter symbol's OWN declaration site
  ## initialize it with a bare int literal". Finds every loop matching
  ## EITHER of the two shapes whose counter can be seeded this way in the
  ## corpus — B4's accumulating-scan (`tryMatchAccumulatingScanIdiomShape`)
  ## and B6's pair-loop (`tryMatchPairLoopIdiomShape`) — and marks the
  ## counter's OWN name (not a traced root) directly, gated on its
  ## `nnkVarSection`/`nnkLetSection` declaration's initializer being a bare
  ## `nnkIntLit`/`nnkUIntLit`-family node (anything else — a computed
  ## expression, a call — stays BV, unaffected: the conservative "none on
  ## anything less direct" doctrine still applies to non-literal,
  ## non-param-traceable inits). A literal argument passed DIRECTLY at a
  ## call site is ALREADY handled by B5's own `intLitProto`-bypass at the
  ## call-argument-lowering site (`runtime.nim`'s `isCall` arm, keyed off
  ## the CALLEE's `IRParam.isIntOffset`) — this collector does not need to
  ## re-cover that case.
  ##
  ## Round-6 N17 (Low): a DIFFERENT call-boundary shape is NOT covered by
  ## B5's bypass, and this collector originally had no trace for it either
  ## (its param sibling `collectIntOffsetParamsImpl` DOES have the
  ## equivalent one-level trace — see that proc's own doc comment — this
  ## collector lacked the parallel leg). The gap: a literal-seeded LOCAL
  ## (`var pos = 2`, not itself a formal param) passed as an ARGUMENT to a
  ## callee whose OWN body has a qualifying offset-consuming loop at that
  ## formal position (traced via `collectIntOffsetParams`, the SAME
  ## analysis the param sibling's own trace already consults for its own
  ## purposes). B5's bypass only fires for a LITERAL syntactically AT the
  ## call site (`readCStringHelper(s, 0)`) — it never sees a local variable
  ## reference, literal-seeded or not. Without a trace here, that local
  ## stays BV-allocated in THIS proc's own env, then gets bound as-is into
  ## the callee's env where the inlined body's `iekStrSubstr`/
  ## `iekStrInOptionRegion` CR-17 check expects `svInt` — the exact
  ## `sxUnknown` degrade this collector exists to close, one call hop
  ## further out. Fixed by mirroring the param sibling's own `walkCalls`
  ## structure below: for each direct call, resolve the callee (via the
  ## audited `resolveRoutineImpl`, N23's own fix), ask
  ## `collectIntOffsetParams` which of ITS OWN formals are offset-traced,
  ## and mark the corresponding actual argument here iff it is a bare
  ## symbol that is itself one of THIS proc's own literal-seeded locals
  ## (`hasLiteralInit`, below). No `visiting` cycle guard is needed here —
  ## unlike the param sibling, this trace never recurses onto ITSELF
  ## (`collectIntOffsetParams` is a different collector with its own
  ## independent, already-fixed N11 cycle guard), so it is bounded to depth
  ## one by construction regardless of the call graph's own shape.
  var iSyms: seq[NimNode]
  proc walkLoops(n: NimNode) =
    if n == nil or n.kind == nnkEmpty: return
    if n.kind == nnkWhileStmt:
      let accOpt = tryMatchAccumulatingScanIdiomShape(n)
      if accOpt.isSome: iSyms.add accOpt.get.iNode
      let pairOpt = tryMatchPairLoopIdiomShape(n)
      if pairOpt.isSome: iSyms.add pairOpt.get.iNode
    for child in n:
      walkLoops(child)
  walkLoops(procDef[6])

  proc hasLiteralInit(n: NimNode, target: NimNode): bool =
    ## True iff `target`'s own declaration site initializes it with a bare
    ## int-literal-family node. Round-6 Q3: now built on the shared
    ## `findDeclInit` search core (see its doc comment) instead of an
    ## independently copied traversal — was the third near-identical copy of
    ## this exact depth-first shape, differing from `findRootParam` only in
    ## which initializer kind it accepts.
    let initExpr = findDeclInit(n, target)
    initExpr != nil and initExpr.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit,
                                           nnkInt32Lit, nnkInt64Lit,
                                           nnkUIntLit, nnkUInt8Lit,
                                           nnkUInt16Lit, nnkUInt32Lit,
                                           nnkUInt64Lit}

  # Round-6 R4 (N8/N2 design fix): `result` collects the counter's OWN Sym
  # node (already available as `iSym` — it came straight off the
  # recognizer's own shape match), not `iSym.strVal`. Pre-R4 this was the
  # exact identity-erosion point N8 diagnosed: `hasLiteralInit` above
  # already does the sound symbol-identity check (`sameSym`) to find the
  # matching declaration, but the RESULT was then flattened to a bare name
  # string, discarding that work — see `ProcScopedCollectors.intOffsetLiteralLocals`'s
  # doc comment for the full writeup and confirmed narrow repro.
  # NOTE: collects into an explicit local `marked` seq, not the implicit
  # `result` — Nim forbids capturing a proc's `result` slot into a nested
  # closure (`walkCalls` below needs to mutate it across recursive calls),
  # the SAME memory-safety restriction `collectIntOffsetParamsImpl` already
  # documents and works around for its own `marked` local.
  var marked: seq[NimNode]
  for iSym in iSyms:
    if iSym.kind == nnkSym and hasLiteralInit(procDef[6], iSym):
      marked.add iSym

  # Round-6 N17 (folded into N7's shared engine): one-level call trace (see
  # the doc comment above for the gap this closes). Marks a LITERAL-seeded
  # local argument here instead of promoting a formal param, so `onMatch`
  # applies `hasLiteralInit` itself rather than delegating to
  # `markSymOrRootParam`/`markIfParamOrLocal` the way the param sibling
  # does — no `CollectorVisiting` needed (see this proc's own doc comment
  # on why the trace is bounded to depth one regardless).
  traceOneCallBoundary[HashSet[string]](
    procDef,
    getCalleeMarked = proc(calleeImpl: NimNode): HashSet[string] =
      collectIntOffsetParams(calleeImpl),
    isMarked = proc(calleeMarked: HashSet[string], formalSym: NimNode): bool =
      formalSym.strVal in calleeMarked,
    onMatch = proc(argNode: NimNode) =
      if argNode.kind == nnkSym and hasLiteralInit(procDef[6], argNode) and
         not containsSym(marked, argNode):
        marked.add argNode)
  marked

proc collectRawVarNames(n: NimNode, into: var HashSet[string]) =
  ## N20 helper (RFC-chapulin-hardening bucket-2). A minimal, PURELY LEXICAL
  ## (pre-classification, pre-A-normalisation) variable-name collector over a
  ## raw `NimNode` subtree: every `nnkSym`/`nnkIdent` leaf's `.strVal` goes
  ## into `into`. Deliberately coarse — it does not distinguish a variable
  ## reference from a field/proc name sharing the same identifier text, and
  ## it descends through EVERY child unconditionally (no A2a-style guard-cond
  ## carve-out, no hidden-conv unwrap) — the ONE consumer
  ## (`collectAssumedLoopBound`, below) only ever uses the result for a
  ## deliberately-conservative NAME-INTERSECTION heuristic (see that proc's
  ## own doc comment), where an over-inclusive name set costs nothing but a
  ## slightly wider "might be assumed-bounded" guess, never a soundness risk.
  if n == nil or n.kind == nnkEmpty: return
  if n.kind in {nnkSym, nnkIdent}:
    into.incl n.strVal
  for child in n:
    collectRawVarNames(child, into)

proc collectAssumedBoundVars(procDef: NimNode): HashSet[string] =
  ## N20 (RFC-chapulin-hardening bucket-2). One PRE-PASS per proc body
  ## (mirrors `collectIntOffsetParams`/`collectStringBackedByteSeqParams`'s
  ## own established idiom): every variable name referenced inside ANY
  ## `symexAssume(cond)` call anywhere in the proc body, collected via
  ## `collectRawVarNames` over each such call's condition argument. Feeds
  ## `collectAssumedLoopBound`'s while-guard check — see that proc's own doc
  ## comment, and `beBudgetExhaustedAssumedBound`'s (types.nim) for the full
  ## mechanism this exists to support. Whole-proc, not lexically scoped to
  ## "before this specific loop" — a deliberate over-approximation (the same
  ## class of conservatism `collectRawVarNames` documents): an assume that
  ## textually follows the loop it happens to share a variable name with
  ## still marks it, which only WIDENS which loops get the (non-solver,
  ## purely diagnostic) "an assumed bound exists" note — it can never
  ## suppress a genuine `beBudgetExhausted` classification the OLD code
  ## would have emitted, since both kinds set `w.sawUnknown`/taint the SAME
  ## way (see the new kind's own doc: "the STATUS/soundness behavior is
  ## UNCHANGED — only the classification is more honest").
  var found = initHashSet[string]()
  proc walkAssumes(n: NimNode) =
    if n == nil or n.kind == nnkEmpty: return
    if isMarkerCall(n, "symexAssume") and n.len >= 2:
      collectRawVarNames(n[1], found)
    for child in n:
      walkAssumes(child)
  walkAssumes(procDef[6])
  found

proc collectAssumedLoopBound(guardNode: NimNode, ctx: ParseCtx): bool =
  ## N20 (RFC-chapulin-hardening bucket-2). `true` iff `guardNode` (a
  ## while-loop's RAW guard) references at least one variable name also
  ## present in `ctx.procScoped.assumedBoundVars` (populated once per proc
  ## by `collectAssumedBoundVars`, above). A purely LEXICAL, zero-Z3-call
  ## signal — see `beBudgetExhaustedAssumedBound`'s doc comment (types.nim)
  ## for why a real per-iteration solver check is out of this slice's scope,
  ## and why this conservative name-match heuristic is still a genuine
  ## classification improvement rather than a guess dressed up as one: it
  ## never CHANGES a verdict, only which of two `sevError` kinds a k-unroll
  ## exhaustion reports.
  if guardNode == nil: return false
  var guardVars = initHashSet[string]()
  collectRawVarNames(guardNode, guardVars)
  for v in guardVars:
    if v in ctx.procScoped.assumedBoundVars: return true
  false

proc collectPairLoopCounterConsumedAfter(procDef: NimNode): seq[NimNode] =
  ## Round-6 R5 (finding S4, walker v93). `tryRecognizePairLoopIdiom`'s
  ## MEMBER-branch closed form is an EMPTY block — it never advances the
  ## pair-loop's counter — and, unlike a naive `i = bound` binding, there is
  ## NO single closed form that is faithful for every witness satisfying
  ## `iekStrInOptionRegion` membership. Concrete counter-example (hand-
  ## derived, pinned in `tests/tsymex_r6_r5_pairloop_counter.nim`): for the
  ## region "aa\x00bb\x00\x00" (one real pair then the canonical empty-key
  ## terminator, 7 bytes, `bound = 7`), the real loop runs `i: 0 -> 6` (the
  ## `readCStringOpt` pair "aa"/"bb"), then its SECOND iteration reads the
  ## empty-key terminator at position 6 and `break`s — the `i = p2` advance
  ## for that iteration never executes, so the real post-loop `i` is 6
  ## (`bound - 1`), NOT 7 (`bound`). A region with no embedded empty-key
  ## segment before `bound`, by contrast, genuinely does exit with
  ## `i == bound` (the loop guard, not a `break`, ends it) — so the two
  ## sub-cases disagree and no single formula covers both. Binding
  ## `i = bound` unconditionally would therefore be UNSOUND for exactly the
  ## canonical (already-pinned, most common) terminated shape.
  ##
  ## The sound remedy is the RFC's own fallback option: skip the
  ## region-membership fast-path fork — using the SAME fold-omitted
  ## `mkShortCircuitWhile` k-unroll the non-member arm already builds as
  ## the loop's WHOLE, genuinely per-iteration-correct replacement — for
  ## any pair-loop whose counter is READ AFTER the loop, where "stale vs.
  ## real" could actually change a verdict. This is the parse-time pre-pass
  ## that decides "after", mirroring `collectIntOffsetLiteralLocals`'s own
  ## single-pass, no-call-boundary-trace style (a pair-loop's counter
  ## consumption is a property of ONE proc's own body, same scope class):
  ## a single pre-order walk of the proc body in SOURCE order, tracking
  ## every `tryMatchPairLoopIdiomShape` candidate visited SO FAR — any
  ## `nnkSym` reference (true binding identity, `sameSym`) to one of those
  ## counters found from that point onward marks it "consumed after".
  ##
  ## The matched while node's OWN subtree (guard + body) is deliberately
  ## NEVER descended into once recognized (`return` before the generic
  ## child recursion) — the loop's own internal references to its counter
  ## (the guard `i < bound`, the `i = p2` advance) are the loop's own
  ## mechanics, not a downstream consumer; descending into them would
  ## self-flag every pair-loop as "consumed" trivially the instant it is
  ## visited.
  ##
  ## A conservative OVER-approximation by construction: source-order
  ## pre-order traversal treats an `if`/`elif`/`else` sibling arm's
  ## reference as "after" even when it is mutually exclusive with the loop
  ## at runtime, and a reference nested arbitrarily deep in a later
  ## statement (not just an immediate sibling) is still found, since the
  ## walk descends through every node kind uniformly outside the two
  ## special-cased kinds above. The same "when in doubt, decline" doctrine
  ## every other B6-adjacent recognizer in this file already applies —
  ## false positives only cost a missed closed-form optimization (falls
  ## back to the sound k-unroll fallback), never a wrong verdict.
  var matched: seq[NimNode]
  var consumedAfter: seq[NimNode]
  proc walk(n: NimNode) =
    if n == nil or n.kind == nnkEmpty: return
    case n.kind
    of nnkSym:
      for m in matched:
        if sameSym(n, m) and not containsSym(consumedAfter, m):
          consumedAfter.add m
    of nnkWhileStmt:
      let shapeOpt = tryMatchPairLoopIdiomShape(n)
      if shapeOpt.isSome:
        matched.add shapeOpt.get.iNode
        return   ## do not descend into the matched loop's own subtree
      for child in n: walk(child)
    else:
      for child in n: walk(child)
  walk(procDef[6])
  consumedAfter

proc hasContinueShallow(n: NimNode): bool =
  ## True iff `n` contains a `nnkContinueStmt` outside a nested loop/routine
  ## boundary (mirrors `hasBreakContinueShallow`'s nesting rules, but
  ## continue-only — R14: only `continue` can skip a trailing guard-refresh
  ## statement; `break` exits the loop outright, so a stale post-break guard
  ## is never checked again and is harmless).
  hasKindShallow(n, {nnkContinueStmt})

proc mkRotatedGuardWhile(cond: IRExpr, body: IRStmt, guardPre: seq[IRStmt]): IRStmt =
  ## The pre-R14 do-while rotation (former `mkGuardedWhile`'s guarded path),
  ## RETAINED for the narrow case where it is PROVABLY safe: `guardPre` must
  ## re-run every real iteration for some reason other than a clean and-split
  ## (a plain guard's ordinary hoisting — e.g. a nested `let`, or even a
  ## no-op structural artifact of the typed AST — or a nested and-chain), AND
  ## the loop body contains no `continue` that could ever skip the trailing
  ## refresh. Callers MUST have already established `not
  ## hasContinueShallow(rawBodyNode)` before calling this. See
  ## `mkShortCircuitWhile`'s doc comment for why a bare non-empty preamble is
  ## NOT itself evidence of a short-circuit fault needing the and-split or a
  ## degrade.
  if guardPre.len == 0:
    mkWhile(cond, body)
  else:
    let rotatedBody = mkBlock(@[body] & guardPre)
    mkBlock(guardPre & @[mkWhile(cond, rotatedBody)])

proc retargetContinue(s: IRStmt, label: string): IRStmt =
  ## RFC-0005 S8w. `s` with every `continue` that leaves the loop being
  ## built (an `isContinue`: a `for` loop's is already a labelled break,
  ## `resolveContinue`) turned into `break label`. A nested `isWhile` owns
  ## the `continue`s inside it and is not entered. The body was parsed for
  ## this loop alone and is rewritten in place. Iterative, with an explicit
  ## work list: a guard's nested short-circuit lowering makes `if`s as deep
  ## as its chain is long.
  var work = @[s]
  while work.len > 0:
    let n = work.pop()
    if n == nil: continue
    case n.kind
    of isContinue:
      n[] = IRStmt(kind: isBreak, brkLabel: label)[]
    of isBlock:
      for x in n.stmts: work.add x
    of isIf:
      for br in n.branches: work.add br.body
      work.add n.elseBody
    of isTry:
      work.add n.tryBody
      for h in n.tryHandlers: work.add h.body
      work.add n.tryFinally
    else:
      discard
  s

proc mkRotatedContinueWhile(cond: IRExpr, body: IRStmt,
                            guardPre: seq[IRStmt], ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8w. The rotation (`mkRotatedGuardWhile`) for a body that
  ## has a `continue`: the body is wrapped in a labelled block and each of
  ## its `continue`s becomes a `break` out of that block
  ## (`retargetContinue`), so a `continue` lands on the trailing guard
  ## refresh and the next guard test sees the loop's current state, as in
  ## Nim, where `continue` re-evaluates the whole guard. Before S8w this
  ## shape declined (R14 Case 2 / 3: `continue` skipped the refresh and the
  ## guard temporary went stale). The loop's real guard stays the `isWhile`
  ## guard, so S8k's feasibility pruning still applies to it.
  let lbl = freshSynth(ctx, "cont")
  let wrapped = mkLabelledBlock(lbl, @[retargetContinue(body, lbl)])
  mkRotatedGuardWhile(cond, wrapped, guardPre)

proc mkShortCircuitWhile(guardNode: NimNode, rawBodyNode: NimNode,
                         body: IRStmt, ctx: ParseCtx): IRStmt =
  ## RFC-chapulin-hardening R14 (CRITICAL soundness fix). REPLACES the old
  ## `mkGuardedWhile` do-while rotation as the DEFAULT: that rotation
  ## re-evaluated a short-circuit guard's hoisted preamble as a TRAILING
  ## statement in the loop body (`<body>; <guardPre>`). `walkBlock`
  ## (runtime.nim) stops processing a block's remaining statements once a
  ## statement returns zero paths — which is exactly what `continue` does
  ## (siphons the path into `continuePaths`, returns `@[]`). So a `continue`
  ## skipped the trailing guard-refresh, the guard temp went stale, and the
  ## NEXT guard check ran against old loop-variable state — a false verdict
  ## (confirmed repro: a `continue` in a `while i < s.len and s[i] != 'z':
  ## inc i; continue` body).
  ##
  ## THE FIX (preferred): desugar a short-circuit `and` at the LOOP level
  ## instead of hoisting a guard temp. `while (A and B): body` (B carrying an
  ## inline defect fork, e.g. `s[i]`) becomes
  ##   while A:                 # A is the REAL loop guard
  ##     <B's preamble>         # B's hoisted stmts (re-run every real iter)
  ##     if not B: break        # short-circuit exit when B is false
  ##     body
  ## B is lowered INSIDE the body, which the walker only enters when guard A
  ## holds — so the path entering the body already has A in its path
  ## condition, and B's inline fault forks guarded FOR FREE by loop semantics
  ## (no `sc` temp, no rotation, no deposit rewriting). `continue` jumps to
  ## the top of `while A`, re-evaluating A and re-running B's preamble at the
  ## body top — exactly Nim's re-evaluation, so it is continue-safe BY
  ## CONSTRUCTION regardless of what the body does. A is a REAL SAT-able
  ## guard (not `while true`), so Z3 prunes cleanly — no path-frontier
  ## blowup under nesting.
  ##
  ## THE SUBTLETY (why this is NOT simply "non-empty preamble ⇒ split-or-
  ## degrade"): a while guard's parse can hoist a non-empty preamble for
  ## reasons that have NOTHING to do with short-circuit `and`/`or` fault
  ## guarding — e.g. `(a div b) > i` semchecks to a trivial
  ## `nnkStmtListExpr(Empty, Infix("<", i, Infix("div", a, b)))` (the `>`
  ## operator's own desugaring artifact), whose lone leading `Empty` child
  ## still parses to one (no-op) preamble statement (CR-1b's
  ## `nnkStmtListExpr` handling, unconditionally used for the "value-
  ## returning multi-statement body" shape). Treating ANY non-empty preamble
  ## as "must be a fault guard, therefore split-or-degrade" over-degrades
  ## these ordinary shapes to `sxUnknown` — a real regression (caught by
  ## `tsymex_r1_draingap.nim`'s `whileDivZero`, whose `(a div b) > i` guard
  ## has no `and`/`or` at all). The actual hazard is narrower: a preamble
  ## that must re-run every real iteration is UNSAFE to hoist via the old
  ## rotation ONLY when the body contains a `continue` that could skip the
  ## refresh. So: whenever the clean and-split (above) is not available, fall
  ## back to the pre-R14 rotation (`mkRotatedGuardWhile`) IF AND ONLY IF the
  ## raw body provably contains no `continue` (`hasContinueShallow`) —
  ## otherwise (RFC-0005 S8w; it sound-degraded before) the same rotation
  ## with the body in a labelled block whose `continue`s become `break`s out
  ## of it (`mkRotatedContinueWhile`), so every iteration, including one a
  ## `continue` ends, runs the trailing refresh.
  ##
  ## Outcomes, decided by inspecting the RAW (untouched) guard node:
  ##  1. Top-level `A and B`, A a simple (non-hoisting) guard, B carrying the
  ##     fault (inline defect-fork op, or its own hoisted preamble) → the
  ##     faithful split above. Continue-safe unconditionally — does not even
  ##     consult `hasContinueShallow`.
  ##  1b. Top-level `A and B`, NEITHER side carries a fault → no special
  ##     handling needed at all; reconstruct the plain flat guard
  ##     `mkBinop(bAnd, condA, condB)`.
  ##  2. A top-level `and` whose LHS `A` itself required hoisting (a nested
  ##     short-circuit buried in `A`, e.g. `(X and Y) and B`) — splitting only
  ##     the outer `and` would leave `A`'s own guard temp exactly as stale as
  ##     the bug this proc fixes, so the clean split doesn't apply. Falls
  ##     back to the rotation (body continue-free) or the continue-
  ##     retargeting rotation (body has continue; S8w). Rare.
  ##  3. Anything else (a plain non-and/or guard whose parse hoists a
  ##     preamble for any reason, or a top-level `or` with a fault) — same
  ##     fallback: rotation (continue-free) or the continue-retargeting
  ##     rotation (has continue; S8w).
  ##  4. No preamble at all needed for the guard — PLAIN `mkWhile(cond,
  ##     body)`, byte-identical to the pre-R1B fast path. This also covers an
  ##     UNBOUNDED single-expr guard with a genuinely-reachable fault (e.g.
  ##     `while s[i] != 'z'`) — R1's drain correctly keeps forking the real
  ##     IndexDefect; do NOT degrade it.
  ##
  ## Shared by BOTH `nnkWhileStmt` arms (`parseStmtInner` and the
  ## `parseIterBodyStmt` for/iterator-body context) so they stay consistent.
  let bodyHasContinue = hasContinueShallow(rawBodyNode)
  # A2a guard-cond carve-out (Mechanism constraint 4, RFC-parser-normalization
  # #146/#149): the ENTIRE guard-condition tree parse below — including the
  # and-split's preA/preB parses — runs under `ctx.inGuardCond`, so any
  # `parseAtomicOperand` call reached while parsing the guard no-ops (plain
  # parseExpr, no hoist) instead of manufacturing a preamble. A manufactured
  # guard-cond preamble would flip the Case-1b/4 fast paths below into the
  # Case-2/3 rotation for continue-bearing loops that prove today.
  # Saved/restored (not blindly cleared) so this can never leak `false` past
  # its own scope even if guard parsing ever nests.
  let savedInGuardCond = ctx.inGuardCond
  ctx.inGuardCond = true
  result =
    if guardNode.kind == nnkInfix and guardNode.len == 3 and
       isBuiltinNamed(guardNode[0], ["and"]):
      # RFC-0005 S8t: the guard's whole `and` chain is flattened and its
      # operands parsed once each, in source order. `A` is the longest
      # prefix that is a plain guard (the first operand hoists nothing, the
      # rest are pure); `B` is the remaining chain, lowered with nested
      # guards (`lowerShortCircuitParts`). Pre-S8t the split was only at
      # the top binary node: `(X and Y) and B` with a fault in `X` fell to
      # the rotation below with `preA & preB`, which ran B's hoisted reads
      # UNGUARDED by A (a false IndexDefect: `while s[0] == 'a' and i <
      # s.len and s[i] == 'a'` read `s[s.len]`), and a long chain forked
      # 2^(n-1) paths through D1c's chained temporaries.
      var operands: seq[NimNode]
      flattenShortCircuitChain(guardNode, "and", operands)
      var parts: seq[ShortCircuitPart]
      for o in operands:
        var pre: seq[IRStmt]
        let ir = parseExpr(o, pre, ctx)
        parts.add (pre: pre, ir: ir)
      var k0 = 0
      if parts[0].pre.len == 0:
        k0 = 1
        while k0 < parts.len and shortCircuitPartIsPure(parts[k0]):
          inc k0
      if k0 >= 1 and k0 < parts.len:
        # Case 1: faithful and-split. Continue-safe by construction.
        var condA = parts[0].ir
        for i in 1 ..< k0:
          condA = mkBinop(bAnd, condA, parts[i].ir)
        var preB: seq[IRStmt]
        let condB = lowerShortCircuitParts(bAnd, parts[k0 .. ^1], preB, ctx)
        let breakIfNotB = mkIf(@[mkBranch(mkUnop(uNot, condB), mkBreak())], nil)
        let loopBody = mkBlock(preB & @[breakIfNotB, body])
        mkWhile(condA, loopBody)
      elif k0 == parts.len:
        # Case 1b: no fault anywhere in this and-guard — plain flat guard
        # (identical to D1c's own fast path for the same node).
        var cond = parts[0].ir
        for i in 1 ..< parts.len:
          cond = mkBinop(bAnd, cond, parts[i].ir)
        mkWhile(cond, body)
      elif not bodyHasContinue:
        # Case 2, continue-free: the FIRST operand needed hoisting -- safe
        # to fall back to the pre-R14 rotation since there is no `continue`
        # to ever skip the refresh. The rotated preamble is the whole
        # chain's nested lowering, so every later operand stays guarded.
        var pre: seq[IRStmt]
        let cond = lowerShortCircuitParts(bAnd, parts, pre, ctx)
        mkRotatedGuardWhile(cond, body, pre)
      else:
        # Case 2, continue present. RFC-0005 S8w: the rotation with each
        # `continue` retargeted onto the trailing refresh
        # (`mkRotatedContinueWhile`); it declined before S8w.
        var pre: seq[IRStmt]
        let cond = lowerShortCircuitParts(bAnd, parts, pre, ctx)
        mkRotatedContinueWhile(cond, body, pre, ctx)
    else:
      var tmpPre: seq[IRStmt]
      let cond = parseExpr(guardNode, tmpPre, ctx)
      if tmpPre.len == 0:
        # Case 4: no preamble needed at all — plain fast path.
        mkWhile(cond, body)
      elif not bodyHasContinue:
        # Case 3, continue-free: whatever the preamble is for (ordinary
        # hoisting, an `or`-guard's fault, a nested fault — it does not matter
        # WHY), it is safe to re-run via the pre-R14 rotation since there is no
        # `continue` to ever skip the refresh.
        mkRotatedGuardWhile(cond, body, tmpPre)
      else:
        # Case 3, continue present (an `or`-guard with a fault, or a fault
        # nested deeper). RFC-0005 S8w: as Case 2 -- the rotation with each
        # `continue` retargeted onto the trailing refresh; it declined
        # before S8w.
        mkRotatedContinueWhile(cond, body, tmpPre, ctx)
  ctx.inGuardCond = savedInGuardCond
  # N20 (RFC-chapulin-hardening bucket-2): when `result` came out a plain
  # `isWhile` (cases 1/1b/4 above — the common shapes; the rotated
  # cases 2/3 are NOT `isWhile` at their top level and are left
  # unmarked, a missed-opportunity, never a regression, per
  # `collectAssumedLoopBound`'s own doc), mark whether its RAW guard
  # references an assumed-bounded variable — purely diagnostic, zero
  # verdict impact (see `beBudgetExhaustedAssumedBound`'s doc, types.nim).
  if result.kind == isWhile:
    result.wHasAssumedBound = collectAssumedLoopBound(guardNode, ctx)

proc iterArgPath(a: NimNode; hasIx: var bool): bool =
  ## RFC-0005 S8bs. `a` is a location Nim's inline iterator expansion maps
  ## an iterator's by-value parameter to (`transf.putArgInto`): a variable,
  ## parameter, `result` or constant, and fields, dereferences and elements
  ## of one. `hasIx`: an element's index is not a literal.
  case a.kind
  of nnkSym:
    symKind(a) in {nskVar, nskLet, nskParam, nskResult, nskForVar, nskConst}
  of nnkDotExpr:
    a.len == 2 and a[1].kind == nnkSym and iterArgPath(a[0], hasIx)
  of nnkCheckedFieldExpr:
    a.len >= 1 and a[0].kind == nnkDotExpr and iterArgPath(a[0], hasIx)
  of nnkHiddenDeref, nnkDerefExpr:
    a.len == 1 and iterArgPath(a[0], hasIx)
  of nnkBracketExpr:
    if a.len != 2 or a[0].typeKind notin {ntyArray, ntySequence, ntyVar}:
      return false
    var ix = a[1]
    while ix.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and ix.len > 0:
      ix = ix[^1]
    if ix.kind notin {nnkCharLit .. nnkUInt64Lit}: hasIx = true
    iterArgPath(a[0], hasIx)
  else: false

proc hoistIterIndices(a: NimNode; preamble: var seq[IRStmt];
                      ctx: ParseCtx; ok: var bool): NimNode =
  ## RFC-0005 S8bs. `a` with each element's non-literal index read into a
  ## `let` (`markByRef` names it): the location is fixed when the loop
  ## starts. Indices are read in Nim's order, the root's first.
  if a.len == 0: return a
  result = copyNimNode(a)
  for i, c in a:
    if a.kind == nnkBracketExpr and i == 1:
      var ix = c
      while ix.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and ix.len > 0:
        ix = ix[^1]
      if ix.kind in {nnkCharLit .. nnkUInt64Lit}:
        result.add c
      else:
        let mk = markByRef(c)
        if mk.isNil:
          ok = false
          result.add c
        else:
          preamble.add mkLet(byRefName(mk), classifyType(c).ty,
                             parseExpr(c, preamble, ctx))
          result.add mk
    else:
      result.add hoistIterIndices(c, preamble, ctx, ok)

proc substIterArg(n, f, by: NimNode): NimNode =
  ## RFC-0005 S8bs. `n` with each use of the by-value formal `f` spelled
  ## `by`.
  if n.kind == nnkSym and containsSym(@[f], n): return copyNimTree(by)
  if n.len == 0: return n
  result = copyNimNode(n)
  for c in n: result.add substIterArg(c, f, by)

proc bindIterArg(impl, formalSym, tyNode, arg: NimNode;
                 body: var NimNode; preamble: var seq[IRStmt];
                 ctx: ParseCtx): bool =
  ## RFC-0005 S8bs. Bind an inlined iterator's formal as Nim's inline
  ## expansion does (`transf.transformFor`), not as a copy: the iterator
  ## runs in the caller's frame, and its parameters name the caller's
  ## locations.
  ##   * a `var` formal is the actual itself, re-read at each use (an
  ##     element's index too: Nim maps the formal to the expression);
  ##   * a by-value formal whose actual is a location (`iterArgPath`) is
  ##     that location: a write to it through a pointer, a global or the
  ##     loop body is seen through the formal. An element's location is
  ##     fixed when the loop starts (Nim takes its address there): its
  ##     index is read, and the element checked, once;
  ##   * anything else (an expression, a conversion) is a copy: false, the
  ##     caller's `let`.
  ## Before, every formal was a copy: a `var` formal's writes were lost,
  ## and a by-value one missed writes through other names.
  let f = formalInBody(impl, formalSym)
  if f.isNil: return false
  if tyNode.kind == nnkVarTy:
    var a = arg
    if a.kind == nnkHiddenAddr and a.len == 1: a = a[0]
    # RFC-0005 S8bu: a `var openArray` formal viewing a whole seq is the
    # seq (`varSeqViews`).
    let src = openArraySource(a)
    if src != a and not isToOpenArray(src) and
       classifyType(src).ty.kind == itSeq:
      a = src
    var b = ByRefSub(isPtr: false, tail: a)
    b.addrNode = newNimNode(nnkHiddenAddr)
    b.addrNode.add copyNimTree(a)
    body = substByRefBody(body, f, b)
    return true
  var hasIx = false
  # RFC-0005 S8bu: a by-value `openArray` formal viewing a whole seq, or a
  # whole array whose first index is 0, is that location.
  var arg = arg
  let src = openArraySource(arg)
  if src != arg and not isToOpenArray(src):
    let k = classifyType(src).ty.kind
    if k == itSeq or (k == itArray and arrayIndexLow(src) == 0): arg = src
  if not iterArgPath(arg, hasIx): return false
  if not hasIx:
    body = substIterArg(body, f, arg)
    return true
  var ok = true
  var pre: seq[IRStmt]
  let fixed = hoistIterIndices(arg, pre, ctx, ok)
  if not ok: return false
  for st in pre: preamble.add st
  # The element is read where the loop starts: its index (and a variant
  # arm on the way) is checked there, as Nim's `addr` checks it.
  preamble.add mkLet(freshSynth(ctx, "iterArgChk"), classifyType(arg).ty,
                     parseExpr(fixed, preamble, ctx))
  body = substIterArg(body, f, stripFieldChecks(fixed))
  true

proc parseIterBodyStmt(n: NimNode,
                       iterVarBindings: seq[(string, IRType)],
                       forBodyNode: NimNode,
                       ctx: ParseCtx): IRStmt =
  ## Parse an iterator body node (after param-subst), transforming each
  ## `nnkYieldStmt(e)` into bound let(s) followed by the for-body.
  ##
  ## Single loop variable (iterVarBindings.len == 1, A3-S1):
  ##   block: let <iterVar> = e; <forBody>
  ##
  ## Multiple loop variables (A3-S2a tuple-yield):
  ##   e MUST be an explicit tuple constructor `(e1, e2, …)` (after peeling any
  ##   `nnkHiddenSubConv` wrapper that semcheck inserts for typed tuple returns).
  ##   Emits one `let` per loop variable:
  ##     block: let a = e1; let b = e2; …; <forBody>
  ##   A non-constructor yield (e.g. `yield myTupleVar`) degrades to
  ##   mkUnsupported (sound — Invariant 3; indirect tuple var out of scope).
  ##
  ## `iterVarBindings[k]` carries the k-th loop var name and its IRType from
  ## the iterator's declared formal return type (not derived from the yield
  ## expression — avoids classifyType failures on untyped literal AST nodes
  ## in pre-transf `getImpl` output, ADR-0014).
  ##
  ## Compound control-flow nodes (StmtList, While, If) are recursed into;
  ## all other nodes delegate to the normal parseStmt.
  ## The existing `isWhile` bounded-unroll (maxLoopUnwind) applies unchanged
  ## to any `while` in the inlined body (ADR-0014 D3).
  case n.kind
  of nnkYieldStmt:
    if iterVarBindings.len == 1:
      # D2 step 3 (single-var, A3-S1): yield rewrite → let <iterVar> = <e>; <forBody>
      # This path is byte-identical to the original A3-S1 implementation.
      var yp: seq[IRStmt]
      let yieldIR = parseExpr(n[0], yp, ctx)
      let bindStmt = mkLet(iterVarBindings[0][0], iterVarBindings[0][1], yieldIR)
      let bodyIR = parseStmt(forBodyNode, ctx)
      var stmts = yp
      stmts.add bindStmt
      stmts.add bodyIR
      if stmts.len == 1: stmts[0] else: mkBlock(stmts)
    else:
      # D2 step 3 (multi-var, A3-S2a): require explicit tuple constructor.
      # Semcheck wraps `yield (e1, e2)` as nnkHiddenSubConv[nnkEmpty, nnkTupleConstr].
      let yieldExprRaw = n[0]
      let tupleConstr =
        if yieldExprRaw.kind == nnkTupleConstr: yieldExprRaw
        elif yieldExprRaw.kind == nnkHiddenSubConv and yieldExprRaw.len >= 2 and
             yieldExprRaw[1].kind == nnkTupleConstr: yieldExprRaw[1]
        else: nil
      if tupleConstr == nil:
        return ctx.declineMarker(feUnsupportedStmtKind, "A3-S2a: multi-var for-loop requires explicit tuple " &
          "constructor in yield (got " & $yieldExprRaw.kind &
          " — indirect tuple variable not supported; ADR-0014 S2, Invariant 3)")
      if tupleConstr.len != iterVarBindings.len:
        return ctx.declineMarker(feUnsupportedStmtKind, "A3-S2a: arity mismatch — yield tuple has " &
          $tupleConstr.len & " elements, for-loop has " &
          $iterVarBindings.len & " vars (ADR-0014 S2, Invariant 3)")
      # Emit one `let varK = elemK` per loop variable, in order.
      var stmts: seq[IRStmt]
      for k in 0 ..< iterVarBindings.len:
        var elemPre: seq[IRStmt]
        let elemIR = parseExpr(tupleConstr[k], elemPre, ctx)
        for s in elemPre: stmts.add s
        stmts.add mkLet(iterVarBindings[k][0], iterVarBindings[k][1], elemIR)
      let bodyIR = parseStmt(forBodyNode, ctx)
      stmts.add bodyIR
      if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkStmtList, nnkStmtListExpr:
    var stmts: seq[IRStmt]
    for c in n:
      stmts.add parseIterBodyStmt(c, iterVarBindings, forBodyNode, ctx)
    if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkBlockStmt:
    # RFC-0005 S8m: the iterator's own `block` is a break target.
    ctx.pushJumpTarget(isLoop = false,
      blockSym = (if n[0].kind in {nnkSym, nnkIdent}: n[0] else: nil))
    let blk = parseIterBodyStmt(n[n.len - 1], iterVarBindings, forBodyNode, ctx)
    wrapJumpBlock(ctx.popJumpTarget().brkLabel, blk)
  of nnkWhileStmt:
    # RFC-0005 S8m: the iterator's own `while` is a jump target.
    ctx.pushJumpTarget(isLoop = true)
    var wp: seq[IRStmt]
    # RFC-chapulin-hardening Q1 (ADR-0025) / B3 / B4 (ADR-0028): try the
    # bounded scan-idiom lifts BEFORE building the ordinary k-unrolled
    # `mkWhile` — see `tryRecognizeScanIdiom`'s, `tryRecognizeScanPairIdiom`'s,
    # and `tryRecognizeAccumulatingScan`'s doc comments for the exact
    # recognized shapes. Tried in order, first `some` wins — the three
    # predicates are mutually exclusive by construction (guard shape / body
    # statement count: 1 vs 2 vs 3) so ordering never matters in practice,
    # but Q1 stays first as the longer-lived, more heavily exercised
    # recognizer.
    let scanLift = tryRecognizeScanIdiom(n, wp, ctx)
    let pairLift = if scanLift.isNone: tryRecognizeScanPairIdiom(n, wp, ctx)
                   else: none(IRStmt)
    let accLift = if scanLift.isNone and pairLift.isNone:
                    tryRecognizeAccumulatingScan(n, wp, ctx)
                  else: none(IRStmt)
    let whileIR =
      if scanLift.isSome or pairLift.isSome or accLift.isSome:
        # Closed-form replacement for the whole loop (no loop to re-run) — its
        # preamble `wp` (the hoisted `find` call) runs once, hoisted as before.
        let hit = if scanLift.isSome: scanLift.get
                  elif pairLift.isSome: pairLift.get
                  else: accLift.get
        if wp.len > 0:
          var all = wp
          all.add hit
          mkBlock(all)
        else:
          hit
      else:
        # `wp` is still empty here (tryRecognizeScanIdiom only appends on the
        # `some(...)` path) and unused below — R14 routes through the shared
        # `mkShortCircuitWhile` helper so a `while i<s.len and s[i]==c` NESTED
        # INSIDE a for/iterator body desugars to the loop-level and-split
        # (guard A re-evaluated by real `while` semantics, B's fault forked
        # inside the body), exactly like the top-level `parseStmtInner` arm —
        # and stays continue-safe by construction (see `mkShortCircuitWhile`).
        let whileBody = parseIterBodyStmt(n[1], iterVarBindings, forBodyNode, ctx)
        mkShortCircuitWhile(n[0], n[1], whileBody, ctx)
    discard ctx.popJumpTarget()
    whileIR
  of nnkIfStmt, nnkIfExpr:
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    var allPre: seq[IRStmt]
    for arm in n:
      case arm.kind
      of nnkElifBranch, nnkElifExpr:
        var cp: seq[IRStmt]
        let condIR = parseExpr(arm[0], cp, ctx)
        for cs in cp: allPre.add cs
        let branchBody = parseIterBodyStmt(arm[1], iterVarBindings, forBodyNode, ctx)
        branches.add mkBranch(condIR, branchBody)
      of nnkElse, nnkElseExpr:
        elseBody = parseIterBodyStmt(arm[0], iterVarBindings, forBodyNode, ctx)
      else: discard
    let ifNode = mkIf(branches, elseBody)
    if allPre.len > 0:
      var all = allPre
      all.add ifNode
      mkBlock(all)
    else:
      ifNode
  else:
    # No yield in this subtree — delegate to the normal statement parser.
    # (nnkYieldStmt in an unrecognised context becomes mkUnsupported via
    # parseStmt's default arm — sound degradation, never a false positive.)
    parseStmt(n, ctx)

proc zeroValueForType(ty: IRType): IRExpr =
  ## An uninitialized `var x: T` is zero-initialized by Nim. Return the IR for
  ## T's ZERO value where it is cleanly expressible; `nil` for types whose
  ## default is not modeled in this cycle (the caller then degrades to a
  ## classified `sxUnknown` — sound, never a wrong verdict). Zero-init (NOT a
  ## fresh free symbol) is the sound model: a read-before-write must observe
  ## Nim's guaranteed default, not an arbitrary value (Invariant 3).
  case ty.kind
  of itInt: mkIntLit(0)               ## int (and char, modeled as itInt): 0 / '\0'
  of itBool: mkBoolLit(false)
  of itFloat32: mkFloatLit(0.0, 32)
  of itFloat64: mkFloatLit(0.0, 64)
  of itString: mkStrLit("")           ## Nim `string` default is the empty string
  of itRef, itPtr: mkNil(ty)           ## RFC-0005 S8m: a `ref`/`ptr` is nil. An
                                       ## uninitialised `var p: ref T` local was
                                       ## a decline, and every catch-all dummy of
                                       ## a ref type was an int that crashed the
                                       ## first `p != nil` (`eqBV`'s kind assert).
  of itTable, itSet, itBitSet:
    ## RFC-0005 S8u: the empty container. An uninitialised `var t: Table[K,
    ## V]` was a decline that left `t` unbound, and the first `t[k] = v` hit
    ## `lower`'s `recv.kind == svTable` assertion (`weInternalWalkerFault`).
    ## RFC-0005 S8bq: a builtin set's is `{}`.
    mkZeroValue(ty)
  of itDistinct:                       ## RFC-0005 S8u: the base type's zero. A
    zeroValueForType(ty.distinctBase)  ## distinct value is its base value in
                                       ## the IR (`D(x)` is the identity).
  of itArray, itTuple, itSeq, itVariant, itMultiVariant:
    ## RFC-0005 S8aj: an aggregate's zero is its elements' and fields'
    ## zeros, and a seq's is the empty seq: `defaultZero`'s recursion, the
    ## walker's lowering of `iekZeroValue` (a shape it cannot zero, such as
    ## a variant whose ordinal-0 tag is not legal, is allocated and
    ## degraded there, never left unbound). An uninitialised
    ## `var a: array[3, int]` was declined here and left `a` unbound, so the
    ## first `a[0] = ...` bound it to a scalar and the next `a[i]` asserted
    ## (`weInternalWalkerFault`, "iekIndex on non-array kind=svBV64"); an
    ## object holding an array or a seq, and a local seq, did the same.
    ## S8z independently fixed `itArray`/`itTuple`/`itVariant`/
    ## `itMultiVariant` at the single call site that needed them then (the
    ## uninitialised-`var` statement), special-cased there instead of here;
    ## that call site now just delegates to this proc, which is this one
    ## mechanism for every caller (construction-time field omission
    ## included — `itSeq` was not covered by S8z's special case).
    mkZeroValue(ty)
  else:
    ## RFC-0005 S8ao (S8aj's remainder): `itUninterp` STAYS a decline --
    ## every value reaching here is a sort the walker chose not to give a
    ## REAL Z3 representation to in the first place, not merely a shape
    ## whose zero "isn't written down yet" (`itArray`/`itTuple`/`itSeq`/
    ## `itVariant`/`itMultiVariant`, just above). `classifyType`
    ## (`dsl_typebridge.nim`) builds `itUninterp` for exactly three
    ## placeholder prefixes, and none has a sound zero to fabricate here:
    ##   - `__ownership:*` (`owned T` / `Atomic[T]`, ADR-0010
    ##     Breadth-LOW-L4): deliberately out of scope for the ref cluster
    ##     -- no sort was ever allocated for these, so there is nothing to
    ##     build a zero constant OF.
    ##   - `__closure` (a proc-typed local with no initializer, e.g.
    ##     `var f: proc(x: int): int`): Nim's real zero is a nil closure,
    ##     but `svClosure` (`runtime.nim`) carries a SITE KEY into real
    ##     lambda-body IR (`runtime_closures.nim`) -- there is no "nil
    ##     closure" sentinel value today that a later `f(...)` call could
    ##     soundly degrade through; minting one is a new SymVal shape
    ##     (plus every call/compare site that would need to recognise it),
    ##     out of proportion for a single caller's zero-init.
    ##   - `__unsupported:<X>` (`classifyType`'s catch-all for a type name
    ##     no structural arm recognises): `X` names some real Nim type the
    ##     classifier never identified, so its actual shape -- and
    ##     therefore its actual zero -- is UNKNOWN here. Fabricating a
    ##     zero for an unidentified shape is exactly the "launder a gap
    ##     into a sound-looking value" move RFC-0005 §3.1 rules out; the
    ##     caller's classified decline is the only sound answer.
    ## Pinned by `tests/tsymex_rfc0005_s8ao_remainder.nim` and, since
    ## RFC-0005 S8ap, `tests/tsymex_rfc0005_s8ap_remainder.nim` (all three
    ## prefixes, reached through an uninitialized-`var` local -- the one
    ## caller of `zeroValueForType` this arm's `nil` return still visibly
    ## degrades -- never a crash, never a guessed value). S8ap gives that
    ## decline each prefix's own kind (`uninterpVarDecline`, below):
    ## `heUnsupportedOwnership`, `ceUnsupportedHof`,
    ## `feUnsupportedParamType`.
    nil

proc uninterpVarDecline(ty: IRType): (SymexErrorKind, string) =
  ## RFC-0005 S8ap (S8ao's remainder). The classified kind and reason for an
  ## uninitialised `var` of the `itUninterp` placeholder `ty` -- the SAME
  ## kind `allocateSym` (`runtime.nim`, its `itUninterp` arm) degrades with
  ## for that placeholder, so the one placeholder reports one kind wherever
  ## it surfaces:
  ##   `__ownership:*`          -> `heUnsupportedOwnership`
  ##   `__closure`              -> `ceUnsupportedHof`
  ##   `__unsupported:*`        -> `feUnsupportedParamType`
  ##   `__unsupported_witness:*`-> `feUnsupportedWitnessType`
  ## Any other name is a malformed placeholder: `feUnsupportedStmtKind`, the
  ## pre-S8ap kind, rather than a guess.
  let nm = ty.uninterpName
  if nm.startsWith("__ownership:"):
    (heUnsupportedOwnership, "ownership wrapper `" &
      nm.substr(len("__ownership:")) &
      "` is out of scope for the ref cluster (Breadth-LOW-L4)")
  elif nm == "__closure":
    (ceUnsupportedHof, "a proc-valued local with no lambda the walker " &
      "built has no symbolic model (Nim's zero is a nil closure)")
  elif nm.startsWith("__unsupported_witness:"):
    (feUnsupportedWitnessType, "unsupported witness shape `" &
      nm.substr(len("__unsupported_witness:")) & "`")
  elif nm.startsWith("__unsupported:"):
    (feUnsupportedParamType, "unsupported type `" &
      nm.substr(len("__unsupported:")) & "`, whose shape is unknown")
  else:
    (feUnsupportedStmtKind, "uninitialized `var` of unmodeled type " &
      $ty.kind & " `" & nm & "`")

proc unsupportedFieldPlaceholder(ty: IRType): IRExpr =
  ## RFC-chapulin-hardening R8 (deferred LOW finding, telemetry hygiene). A
  ## KIND-COMPATIBLE placeholder for an omitted `nnkObjConstr` field whose
  ## type `zeroValueForType` declines (no clean zero this cycle). Used
  ## EXCLUSIVELY by the P2a construction-time DEGRADE path, always alongside
  ## a classified `feUnsupportedExprKind` parse-error + `mkUnsupported`
  ## SND-1 taint stmt emitted by the caller — the taint alone already forces
  ## the reported verdict to `sxUnknown` regardless of this placeholder's
  ## content (`isTargetLabel`'s `if p.uncertain: w.sawUnknown = true`
  ## chokepoint never even calls `trySolve`), so this is NEVER real modeling
  ## and NEVER influences the verdict.
  ##
  ## What this DOES fix: before R8, the degrade path filled the field with a
  ## bare `mkIntLit(0)` regardless of the field's actual declared type. For a
  ## NON-scalar field (seq/tuple/…) that is a KIND MISMATCH — `lowerTupleLit`
  ## only assigns a proto for `itInt`/`itBool` fields (see `runtime.nim`), so
  ## the mismatched element silently becomes a wrongly-kinded `SymVal`
  ## sitting where (say) an `svSeq` belongs. If the SUT later performs any
  ## type-appropriate operation on that field (`.len`, indexing, …), the
  ## walker raises a plain `ValueError` (e.g. `iekSeqLen`'s "on non-container
  ## kind=..." arm) — an exception NONE of `runSymexImpl`'s specific carriers
  ## match, so it falls through to the generic `CatchableError` catch-all and
  ## gets reported as `weInternalWalkerFault`, clobbering the
  ## already-registered `feUnsupportedExprKind` classification before
  ## `prog.parseErrors` is ever drained (that only happens if the walk
  ## completes without raising). Building a KIND-matching placeholder here
  ## means ordinary type-appropriate operations succeed structurally (with
  ## meaningless content — irrelevant, since the taint already owns the
  ## verdict), so the walk completes and the classified error surfaces.
  ##
  ## Mirrors the existing ref-field precedent just above in the P2a arm
  ## (`mkNil(fty)` for an unresolved ref-typed field) and Cluster H's
  ## `zeroIRExprForType` sibling (heap-field zero-init): `itRef`/`itPtr` →
  ## `mkNil`; `itTuple` → recurse field-by-field (bounded — Nim forbids
  ## cyclic VALUE nesting). For `itSeq`, an EMPTY seq literal is
  ## kind-correct without attempting to claim it is a REAL modeled zero (this
  ## proc is reached ONLY from the degrade branch, never the sound
  ## `zeroValueForType`-succeeds branch, so it can never promote a field from
  ## "unmodeled" to "real"). The residual `itTable`/`itSet`/`itArray`/
  ## `itVariant`/`itMultiVariant`/`itDistinct`/`itUninterp` kinds have no
  ## literal IR constructor at all today (same set `zeroIRExprForType`
  ## declines) — a same-kind placeholder isn't buildable without new IR
  ## machinery, out of scope for this telemetry-only fix; `mkIntLit(0)`
  ## remains the fallback there, same residual risk as before R8.
  let realZero = zeroValueForType(ty)
  if realZero != nil: return realZero   ## RFC-0005 S8m: covers itRef/itPtr
  case ty.kind
  of itSeq: mkSeqLit(@[], ty.seqElemTy)
  of itTuple:
    var elems: seq[IRExpr]
    for f in ty.fields: elems.add unsupportedFieldPlaceholder(f)
    mkTupleLit(elems, ty)
  else: mkIntLit(0)   ## table/set/array/variant/multiVariant/distinct/
                       ## uninterp: no literal constructor exists (residual).

proc refExprClassify(n: NimNode): ClassifiedType =
  ## RFC-chapulin-hardening P2b. Classify whether VALUE expression `n`
  ## genuinely carries a ref/ptr ADDRESS (`itRef`/`itPtr`), reusing the SAME
  ## two-level classify already established for `nil` comparisons
  ## (`nnkInfix`'s `==`/`!=` arm) and recursive ref-object field reads
  ## (`nnkDotExpr`'s R9 extension): `classifyType` handles a BARE symbol
  ## directly (post-Cluster-H-Step-C: `itRef` for a plain named-ref-object
  ## alias, `itVariant` — deliberately, ADR-0022 sub-decision #1 — for a
  ## ref-VARIANT alias); a DERIVED (non-bare) expression re-classifies via
  ## `classifyFieldType` to recover `itRef`/`itPtr` (`classifyType` on a
  ## derived dot-expr node resolves the FIELD's placeholder value shape, not
  ## "this came from a ref field"). Used by the P2b `nnkObjConstr` arm to
  ## decide whether a ref-typed field's VALUE can be soundly stored as-is (an
  ## address) or must be degraded (an expression with no address to store).
  ##
  ## Cluster H Step C (ADR-0022): the `n.kind notin {nnkSym, nnkIdent}`
  ## exclusion below was FLAGGED for deletion by the original H1 brief (as
  ## one of "3 bare-symbol carve-outs suppressing itRef") but is KEPT after
  ## reasoning through the variant interaction (see the twin comment at the
  ## `nnkDotExpr` field-read site, ~1328, for the full argument). Short
  ## version: it is already dead-but-harmless for the new capability (a bare
  ## named-ref symbol now classifies `itRef` at Level 1, so the fallback below
  ## never fires for it), and deleting it would let a bare ref-VARIANT symbol
  ## (value-modelled to `itVariant` on purpose) get mis-recovered to `itRef`
  ## by `classifyFieldType` (which is deliberately variant-BLIND — correct
  ## for genuine FIELD declarations, wrong for a bare top-level symbol).
  var cls = classifyType(n)
  if cls.ty.kind notin {itRef, itPtr} and n.kind notin {nnkSym, nnkIdent}:
    let fc = classifyFieldType(n)
    if fc.ty.kind in {itRef, itPtr}: cls = fc
  cls

proc stmtListItems(n: NimNode): seq[NimNode] =
  ## Round-6 N34 fix. A `StmtList`-shaped body (`nnkStmtList`/
  ## `nnkStmtListExpr`) itemizes as its own children — that is what those
  ## node kinds MEAN. Anything else does NOT: in particular, the typed AST
  ## does not always wrap a lone `block:`-body statement in `nnkStmtList` —
  ## a `block:` with exactly one statement can typecheck directly to that
  ## bare statement node. Treating such a node as a StmtList and iterating
  ## `for c in n` would walk the STATEMENT'S OWN CHILDREN (e.g. an
  ## `nnkAsgn`'s LHS/RHS) as if they were sibling top-level statements —
  ## each then lands the unrecognised-node-kind catch-all
  ## (`mkUnsupported`), a consistent mis-parse/decline. Any body-itemizing
  ## call site should route through this helper rather than a bare
  ## `for c in n` so the lone-statement hazard can't resurface elsewhere.
  if n.kind in {nnkStmtList, nnkStmtListExpr}:
    for c in n: result.add c
  else:
    result.add n

proc addrRootSym(t: NimNode): NimNode =
  ## RFC-0005 S8bw (item 3), on S8an/S8ax/S8be. The variable an address
  ## path is rooted at: a `var` symbol, or a `var` parameter (its implicit
  ## dereference) -- either names one location for the routine's whole
  ## activation. nil for any other root.
  if t.kind == nnkSym and symKind(t) == nskVar: return t
  if t.kind == nnkHiddenDeref and t.len == 1 and t[0].kind == nnkSym and
     symKind(t[0]) == nskParam and t[0].getTypeInst.kind == nnkVarTy:
    return t[0]
  nil

proc fixedAddrNode(e: NimNode): NimNode =
  ## RFC-0005 S8an/S8as. `e` (through conversions) when it is `addr lv` and
  ## `lv` names the same location for as long as a pointer to it lives: a
  ## variable, then fields of value objects/tuples and (RFC-0005 S8as)
  ## constant indices into value arrays -- no dereference and no computed
  ## index, which could re-point between uses, and no seq element, which
  ## a later `add` may move. nil otherwise.
  var a = e
  while a.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and a.len > 0:
    a = a[^1]
  if a.kind != nnkAddr or a.len != 1: return nil
  var t = a[0]
  while true:
    if t.kind == nnkDotExpr and t.len == 2 and
       t[0].getTypeImpl.kind in {nnkObjectTy, nnkTupleTy}:
      t = t[0]
    elif t.kind == nnkBracketExpr and t.len == 2 and
         t[0].typeKind == ntyArray:
      var ix = t[1]
      while ix.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and ix.len > 0:
        ix = ix[^1]
      if ix.kind notin {nnkCharLit .. nnkUInt64Lit}: return nil
      t = t[0]
    else: break
  if addrRootSym(t) == nil: return nil
  a

proc addrAliasDecl(c: NimNode): tuple[p, addrNode: NimNode] =
  ## RFC-0005 S8an. `let p = addr lv` (or `var`), one name, where `lv` names
  ## the same location for as long as `p` lives (`fixedAddrNode`).
  ## `(nil, nil)` otherwise.
  if c.kind notin {nnkLetSection, nnkVarSection} or c.len != 1: return
  let d = c[0]
  if d.kind != nnkIdentDefs or d.len != 3 or d[0].kind != nnkSym: return
  let a = fixedAddrNode(d[2])
  if a == nil: return
  (d[0], a)

const staleElemMarkerTag = "nelli:S8ax:stale-elem:"
  ## RFC-0005 S8ax. The text of the comment statement `parseDeferList`
  ## places before a statement that may dereference a pointer to a seq
  ## element after the seq may have been resized; `parseStmt` declines it.

proc stableIndex(ix: NimNode; rest: openArray[NimNode]): bool =
  ## RFC-0005 S8ax. Index expression `ix` has the same value at every
  ## statement of `rest`: literals, `let`s, constants and non-`var`
  ## parameters, a `var` no statement of `rest` names, and the integer
  ## operators and conversions over them. A call (side effects, or a
  ## result that differs) is not.
  case ix.kind
  of nnkCharLit .. nnkUInt64Lit: true
  of nnkSym:
    case symKind(ix)
    of nskConst, nskLet: not isModuleGlobal(ix) or symKind(ix) == nskConst
    of nskParam: ix.getTypeInst.kind != nnkVarTy
    of nskVar:
      if isModuleGlobal(ix): return false
      for r in rest:
        if mentionsSym(r, ix): return false
      true
    else: false
  of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv:
    ix.len > 0 and stableIndex(ix[^1], rest)
  of nnkInfix:
    ix.len == 3 and ix[0].kind == nnkSym and
      macros.strVal(ix[0]) in ["+", "-", "*", "div", "mod"] and
      not isUserCallee(ix[0]) and
      stableIndex(ix[1], rest) and stableIndex(ix[2], rest)
  else: false

proc elemAddrNode(e: NimNode; rest: openArray[NimNode]):
    tuple[addrNode, seqRoot, armRoot: NimNode] =
  ## RFC-0005 S8ax. `e` (through conversions) when it is `addr lv` and `lv`
  ## is a variable's element path: fields of value objects and tuples,
  ## indices into value arrays, and an index into the variable itself when
  ## it is a seq, each index stable over `rest` (`stableIndex`) -- so `lv`
  ## names one location at every statement of `rest`, unless the seq is
  ## resized (`seqRoot`, nil for none). `(nil, nil)` otherwise, and for a
  ## path `fixedAddrNode` already takes.
  var a = e
  while a.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and a.len > 0:
    a = a[^1]
  if a.kind != nnkAddr or a.len != 1: return
  var t = a[0]
  var seqStep = false
  var computed = false
  var armStep = false
  while true:
    if t.kind == nnkDotExpr and t.len == 2 and
       t[0].getTypeImpl.kind in {nnkObjectTy, nnkTupleTy}:
      t = t[0]
    elif t.kind == nnkCheckedFieldExpr and t.len >= 1 and
         t[0].kind == nnkDotExpr and t[0].len == 2:
      # RFC-0005 S8be: a field of a case object's arm. Nim checks the arm
      # where `addr` takes it; a statement that may change the object's
      # arm (`mayRearm`) leaves the pointer naming another arm's memory.
      if armStep: return
      armStep = true
      t = t[0][0]
    elif t.kind == nnkBracketExpr and t.len == 2 and
         t[0].typeKind in {ntyArray, ntySequence}:
      if not stableIndex(t[1], rest): return
      var ix = t[1]
      while ix.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and ix.len > 0:
        ix = ix[^1]
      if ix.kind notin {nnkCharLit .. nnkUInt64Lit}: computed = true
      if t[0].typeKind == ntySequence:
        if t[0].kind != nnkSym or seqStep: return
        seqStep = true
      t = t[0]
    else: break
  # RFC-0005 S8bw (item 3): a `var` parameter's arm field too.
  let root = addrRootSym(t)
  if root == nil or isModuleGlobal(root): return
  if not seqStep and not computed and not armStep: return
  # RFC-0005 S8be: one root at a time (an arm field under a seq element
  # is two ways to go stale).
  if seqStep and armStep: return
  (a, (if seqStep: root else: nil), (if armStep: root else: nil))

proc mayRearm(n, o: NimNode): bool =
  ## RFC-0005 S8be. Statement `n` may change the arm of the case object
  ## variable `o`: `o` occurs anywhere but as the object of a field access
  ## (`o.f`, read or written in place); or `n` calls a nested routine or a
  ## proc value, which may reach `o` by name.
  case n.kind
  of nnkSym:
    if containsSym(@[o], n): return true
    if isNestedRoutine(n): return true
    if symKind(n) in {nskVar, nskLet, nskParam} and
       n.getTypeInst.kind == nnkProcTy:
      return true
    return false
  of nnkDotExpr:
    if n.len == 2 and isSymOf(n[0], o): return false
  of nnkCheckedFieldExpr:
    if n.len >= 1 and n[0].kind == nnkDotExpr and n[0].len == 2 and
       isSymOf(n[0][0], o):
      return false
  of RoutineNodes:
    return mentionsSym(n, o)
  else: discard
  for c in n:
    if mayRearm(c, o): return true
  false

proc mayResizeSeq(n, s: NimNode): bool =
  ## RFC-0005 S8ax. Statement `n` may move the storage of the seq variable
  ## `s`: `s` occurs anywhere but under an element access `s[i]` or as the
  ## argument of a read-only builtin (`len`, `high`, `low`, iteration,
  ## `contains`, `find`, `$`, `==`); or `n` calls a nested routine or a
  ## proc value, which may reach `s` by name.
  case n.kind
  of nnkSym:
    if containsSym(@[s], n): return true
    if isNestedRoutine(n): return true
    if symKind(n) in {nskVar, nskLet, nskParam} and
       n.getTypeInst.kind == nnkProcTy:
      return true
    return false
  of nnkBracketExpr:
    if n.len == 2 and isSymOf(n[0], s):
      return mayResizeSeq(n[1], s)
  of nnkCall, nnkCommand, nnkInfix, nnkPrefix:
    if n.len >= 2 and n[0].kind == nnkSym and not isUserCallee(n[0]) and
       macros.strVal(n[0]) in ["len", "high", "low", "items", "pairs",
                               "mitems", "mpairs", "contains", "find", "$",
                               "==", "!="]:
      for j in 1 ..< n.len:
        if not isSymOf(n[j], s) and mayResizeSeq(n[j], s): return true
      return false
  of RoutineNodes:
    return mentionsSym(n, s)
  else: discard
  for c in n:
    if mayResizeSeq(c, s): return true
  false

proc addrRepoint(r, p: NimNode): NimNode =
  ## RFC-0005 S8as. `r` is the statement `p = addr lv'` re-pointing the
  ## alias `p` at another fixed location (`fixedAddrNode`): that node, nil
  ## otherwise.
  if r.kind in {nnkAsgn, nnkFastAsgn} and r.len == 2 and isSymOf(r[0], p):
    return fixedAddrNode(r[1])
  nil

proc substAddrAlias(n, p, addrNode: NimNode): NimNode =
  ## RFC-0005 S8an. `n` with `p[]` spelled as the pointee lvalue and a bare
  ## `p` (an argument; `addrAliasDecl`'s caller checked there is no other
  ## use) spelled as `addr lv`.
  ## RFC-0005 S8au: `p` passed to a `var ptr` formal (`nnkHiddenAddr(p)`)
  ## is spelled `addr lv` too: the formal only dereferences it
  ## (`ptrFormalStaysLocal`), so it is the `ptr` argument `addr lv`.
  if n.kind == nnkHiddenAddr and n.len == 1 and isSymOf(n[0], p):
    return copyNimTree(addrNode)
  if n.kind in {nnkDerefExpr, nnkHiddenDeref} and n.len == 1 and
     isSymOf(n[0], p):
    return copyNimTree(addrNode[0])
  if isSymOf(n, p): return copyNimTree(addrNode)
  if n.len == 0: return n
  result = copyNimNode(n)
  for c in n: result.add substAddrAlias(c, p, addrNode)

proc parseDeferList(items: seq[NimNode], start: int, ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8l. Parse the statements `items[start ..^ 1]` of one statement
  ## list, lowering `defer:` the way Nim does: a `defer: D` guards the REST of
  ## its own statement list, i.e. it becomes `try: <rest> finally: D` (the
  ## manual; probed: `defer: log r; if x > 0: return x*2` runs the defer
  ## after the return with result == 8, a raise under it runs it before the
  ## exception leaves, a `defer: result += 100` changes the returned value,
  ## and two defers run in reverse order). A later defer nests inside the
  ## earlier one's try, so it runs first. A defer that ends its list guards
  ## nothing and runs at once (an empty try body). Before S8l `nnkDefer` fell
  ## to the catch-all (`feUnsupportedStmtKind`: the defer body was dropped).
  var stmts: seq[IRStmt]
  for k in start ..< items.len:
    let c = items[k]
    if c.kind == nnkDefer:
      let fin = parseStmt(c[c.len - 1], ctx)   # lexically first
      stmts.add mkTry(parseDeferList(items, k + 1, ctx), @[], fin)
      break
    # RFC-0005 S8an: `let p = addr x` whose every later use is `p[]` or an
    # argument to a `ptr` formal that keeps it local (`ptrUsesStayLocal`)
    # IS `x`: the rest of the list is parsed with `p[]` spelled `x` and
    # `p` spelled `addr x` (the call-site cell). Any other use keeps the
    # declaration, and `heUnsafeCast`.
    # RFC-0005 S8as: a section declaring several names is one declaration
    # per name, so an alias among them is seen.
    if c.kind in {nnkLetSection, nnkVarSection} and c.len > 1:
      var anyAlias = false
      for d in c:
        if addrAliasDecl(newTree(c.kind, d)).p != nil: anyAlias = true
      if anyAlias:
        var expanded = items[0 ..< k]
        for d in c: expanded.add newTree(c.kind, d)
        expanded.add items[k + 1 ..< items.len]
        stmts.add parseDeferList(expanded, k, ctx)
        break
    var al = addrAliasDecl(c)
    # RFC-0005 S8ax: an element path with a computed index, or into a seq
    # (`elemAddrNode`): its index is checked where `addr` evaluates it, and
    # a use after a statement that may resize the seq declines.
    var seqRoot: NimNode = nil
    var armRoot: NimNode = nil   ## RFC-0005 S8be
    var checkAt = false
    if al.p == nil and c.kind in {nnkLetSection, nnkVarSection} and
       c.len == 1 and c[0].kind == nnkIdentDefs and c[0].len == 3 and
       c[0][0].kind == nnkSym:
      let el = elemAddrNode(c[0][2], items[k + 1 ..< items.len])
      if el.addrNode != nil:
        al = (c[0][0], el.addrNode)
        seqRoot = el.seqRoot
        armRoot = el.armRoot
        checkAt = true
    if al.p != nil:
      # RFC-0005 S8as: a statement of the list itself that re-points `p` at
      # another fixed location (`p = addr y`) switches the spelling for
      # the statements after it; a re-point anywhere else (under an `if`)
      # is a use that does not stay local.
      var stays = true
      for r in items[k + 1 ..< items.len]:
        if addrRepoint(r, al.p) != nil: continue
        var seen: seq[string]
        if not ptrUsesStayLocal(r, al.p, seen):
          stays = false
          break
      if stays:
        var rest: seq[NimNode]
        var cur = al.addrNode
        if checkAt:
          rest.add newTree(nnkDiscardStmt, copyNimTree(al.addrNode[0]))
        var stale = false
        for r in items[k + 1 ..< items.len]:
          let rp = addrRepoint(r, al.p)
          if rp != nil:
            cur = rp
            seqRoot = nil
            armRoot = nil
            stale = false
            continue
          let resizes = seqRoot != nil and mayResizeSeq(r, seqRoot) or
                        armRoot != nil and mayRearm(r, armRoot)
          if (stale or resizes) and mentionsSym(r, al.p):
            if armRoot != nil:
              # RFC-0005 S8be: an arm field's pointer after its object may
              # have changed arm.
              rest.add newCommentStmtNode(staleElemMarkerTag &
                "RFC-0005 S8be: `" & al.p.repr & "` points at an arm field " &
                "of `" & armRoot.repr & "`, which a statement before this " &
                "use (or this statement) may give another arm: the pointer " &
                "then names another arm's memory (feUnsupportedOp)")
            else:
              rest.add newCommentStmtNode(staleElemMarkerTag &
                "RFC-0005 S8ax: `" & al.p.repr & "` points into seq `" &
                seqRoot.repr & "`, which a statement before this use (or " &
                "this statement) may resize: Nim may move the elements, and " &
                "the pointer then names freed memory (feUnsupportedOp)")
          rest.add substAddrAlias(r, al.p, cur)
          if resizes: stale = true
        if rest.len > 0: stmts.add parseDeferList(rest, 0, ctx)
        break
    stmts.add parseStmt(c, ctx)
  if stmts.len == 1: stmts[0] else: mkBlock(stmts)

proc isKnownMutatingReceiverCall(calleeName: string, recv: NimNode,
                                  argc: int): bool =
  ## N49 (RFC-chapulin-hardening bucket-2, design round). True iff
  ## `calleeName(recv, ...)` (a method-call-syntax mutation, `argc` total
  ## call arguments) is one of the "#145 mutations recognised by name +
  ## receiver kind" shapes `parseStmtInner`'s `nnkCall`/`nnkCommand` arm
  ## already models for a BARE-SYMBOL receiver — `s.add(x)`, `s.del(i)`,
  ## `s.insert(v, i)`, `t.del(k)`, `s.incl(x)`, `s.excl(x)`, `t[k] = v`'s
  ## desugared `[]=` form — mirroring that arm's own name/receiver-
  ## type/arity matrix exactly (kept in sync by hand; both sites are small
  ## and rarely change). `recv` may be ANY node shape here (this predicate
  ## itself does not require a bare symbol) — `classifyType` is safe to
  ## call on it precisely because it is a genuine, already-semchecked
  ## sub-expression of the call being parsed (a real operand with a real
  ## resolved type), never a `monomorphize()`-synthesized node; the
  ## crash class this predicate exists to route AROUND lives one level
  ## further in, inside `ensureProcRegistered`'s own attempt to treat the
  ## mutation verb as an ordinary user proc.
  let cls = classifyType(recv)
  case calleeName
  of "add": (cls.ty.kind in {itString, itSeq}) and argc == 3
  of "del": (cls.ty.kind in {itSeq, itTable}) and argc == 3
  of "insert": cls.ty.kind == itSeq and argc == 4
  of "incl", "excl": cls.ty.kind == itSet and argc == 3
  of "[]=": cls.ty.kind == itTable and argc == 4
  else: false

proc parseRoutineCallStmt(n, calleeSym: NimNode, preamble: var seq[IRStmt],
                          ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8c. A statement-position call to a ROUTINE: the
  ## transparent / opaque / foreign arms, else the ordinary user-proc call.
  ## Split out of `parseStmtInner`'s `nnkCall` arm so a user callee -- a
  ## user `inc`/`add`/`incl`/`del`, or a user `+=` reaching the `nnkInfix`
  ## statement arm -- takes exactly this path and never a builtin mutation
  ## model that shares its name.
  let calleeName = calleeSym.strVal
  let userCallee = isUserRoutine(calleeSym)
  let m = getStdlibModelFor(calleeName, itBool)  ## kind ignored
  if hasSymexTransparentPragma(calleeSym) and isInertOpaqueCall(n):
    # Issue #163. A `{.symexTransparent.}` call in statement position is
    # DELETED — no IR at all, not an opaque no-op. nelli's own
    # instrumentation (`recordEdge`, `logCmp`) is the motivating case:
    # `{.cover.}` emits a `recordEdge` at the top of every branch arm,
    # so modelling them even as inert statements put an unknown effect
    # on every path of every instrumented proc.
    #
    # #163 review R7: the deletion is now GATED on `isInertOpaqueCall`
    # — the identical predicate the OPAQUE sibling arm below applies to
    # the same argument shapes. Before this gate, the call was dropped
    # UNCONDITIONALLY: a `var` formal (`nnkHiddenAddr`) or a `ref`/
    # `ptr`/possibly-ref-carrying-object argument lets the real callee
    # write through or observe state a deleted call's absence cannot
    # account for, so a transparent-tagged mutator (e.g.
    # `mutateT(x: var int)`) vanished and a target reading the
    # mutation's effect solved against the UNMUTATED value — a
    # concrete false `sxUnsat`. The non-inert case now falls through to
    # the opaque arm just below (mirrors the expression-position
    # fallback a few hundred lines up: a `{.symexTransparent.}` callee
    # whose promise is contradicted degrades to `{.symexOpaque.}`
    # handling — fails safe, never a silent wrong witness).
    #
    # The ARGUMENTS are still parsed, into the preamble, and only their
    # values are thrown away. The pragma is a promise about the CALLEE,
    # not about the expressions written at the call site: Nim evaluates
    # those before the call whether or not symex models the call, so
    # dropping them unparsed would silently delete any effect they carry
    # (and any honest degrade an unmodellable argument owes). Both
    # instrumentation shapes parse to nothing but a value —
    # `{.cover.}`'s `recordEdge(123)` is an int literal, `{.covercmp.}`'s
    # `logCmp(lTmp, rTmp, "==")` reads temps the rewrite already bound —
    # so the preamble stays empty in the case that motivated this arm.
    for i in 1 ..< n.len:
      discard parseExpr(n[i], preamble, ctx)
    mkBlock(@[])
  elif hasSymexTransparentPragma(calleeSym):
    # #163 review R7: the callee over-claimed `{.symexTransparent.}` —
    # at least one argument is not provably inert (a writable `var`/
    # `ref`/`ptr`/possibly-ref-carrying-object). Emit a SPECIFIC
    # parse-time degrade naming the callee and the broken promise —
    # entirely a front-end (`ctx.parseErrors`) classification, so it
    # sits alongside, not instead of, the generic
    # `feOpaqueCallUnmodelled` the resulting opaque-call fallback also
    # produces at walk time. Without this, the ONLY message the caller
    # sees is the generic opaque-call text, which literally suggests
    # "mark it `{.symexTransparent.}`" to a caller who already did —
    # actionable advice for a genuine `{.symexOpaque.}` call, wrong
    # advice here.
    # RFC-0005 S8 (§13.3, i3): an annotation violation, not a decline.
    ctx.annotationViolation(n, avArgNotInert, calleeName,
      "call `" & calleeName & "` is tagged `{.symexTransparent.}` " &
      "but takes a writable argument (var/ref/ptr/possibly-ref-" &
      "carrying), so it is not provably inert; treated as opaque " &
      "instead of dropped")
    var argIRs: seq[IRExpr]
    for i in 1 ..< n.len:
      argIRs.add parseExpr(n[i], preamble, ctx)
    mkOpaqueCall(calleeName, "", argIRs, tBool(), false)
  elif (m.kind == smkOpaqueEffectful and not userCallee) or
       hasSymexOpaquePragma(calleeSym) or isBodilessForeign(calleeSym):
    # RFC-0005 S8c: the name catalog is stdlib names; a same-named user
    # routine is walked (the final arm), only its pragmas can black it out.
    # RFC-0005 S8b: a bodiless foreign callee joins this arm (see
    # `isBodilessForeign`); the inertness rule below applies to it as
    # to any opaque call.
    #
    # Issue #163 slice 4: an opaque call in statement position (no
    # bound result — `retName == ""` below) whose every argument is
    # plainly value-typed (`isInertOpaqueCall`) cannot affect the
    # SUT's symbolic state. Compute the predicate against the RAW
    # node `n` before parsing — parsing doesn't consume `n`, but the
    # predicate is about the call site's shape, not the parsed IR.
    #
    # RFC-0005 S8as: and its body's writes to module-level variables (and a
    # nested routine's to its captures) are bounded by its effect summary
    # (`opaqueWriteSummary`); a catalogued stdlib routine writes none.
    #
    # RFC-0005 S8ax: a user or foreign routine's writes through its
    # arguments and to the heap are summarised too (`opaqueArgEffects`,
    # `reachPointees`), and its raises are forked (`opaqueRaiseTypes`).
    let catalogued = m.kind == smkOpaqueEffectful and not userCallee
    var inert = if catalogued: isInertOpaqueCall(n) else: true
    var eff: OpaqueEffects
    var raises, defects: seq[string]
    if not catalogued:
      eff = opaqueWriteSummary(calleeSym)
      opaqueArgEffects(n, calleeSym, eff)
      inert = eff.inert
      if inert:
        raises = opaqueRaiseTypes(calleeSym, ctx)
        defects = opaqueDefectTypes(calleeSym, ctx)   # RFC-0005 S8be
    var heapTys: seq[IRType]
    for t in eff.heapTys:
      let it = classifyType(t).ty
      if it == nil or it.kind notin {itRef, itPtr}: continue
      var dup = false
      for h in heapTys:
        if $h == $it: dup = true
      if not dup: heapTys.add it
    var argIRs: seq[IRExpr]
    for i in 1 ..< n.len:
      argIRs.add parseExpr(n[i], preamble, ctx)
    mkOpaqueCall(calleeName, "", argIRs, tBool(), inert, eff.havoc,
                 heapTys, eff.heapAll, raises, defects, eff.why)
  else:
    userOrMethodCallStmt(n, calleeSym, preamble, ctx)   ## RFC-0005 S8bn

type ValueFieldWrite = object
  ## RFC-0005 S8p. A field write on a VALUE tuple or object, rebuilt as a
  ## whole-root assignment: `root` is the variable the write lands in, `value`
  ## its new value.
  root:  string
  value: IRExpr
  heap:  IRStmt   ## RFC-0005 S8ar: the chain is rooted at a ref/ptr
                  ## object's field (`p.inner.s`): the field-deref write
                  ## of the rebuilt field (`root`/`value` unused)

proc toStmt(fw: ValueFieldWrite): IRStmt =
  ## RFC-0005 S8ar. The statement that lands the rebuilt value.
  if fw.heap != nil: fw.heap else: mkAssign(fw.root, fw.value)

proc heapFieldRoot(n: NimNode; operand: var NimNode;
                   fieldName: var string): bool =
  ## RFC-0005 S8ar. True iff `n` is a ref/ptr object's field (`p.inner`):
  ## `operand` is then the ref/ptr expression and `fieldName` the field. A
  ## value field chain may be rooted there (`p.inner.s.add v`,
  ## `p.inner.a = v`); the rebuilt field is written back to the heap cell
  ## (`mkFieldDerefWrite`), as `p.inner = v` is. Before S8ar such a chain
  ## was the "unsupported nnkAsgn shape" / N49 decline.
  let t = if n.kind == nnkCheckedFieldExpr and n.len >= 1: n[0] else: n
  if t.kind == nnkDotExpr and t.len == 2 and t[1].kind in {nnkSym, nnkIdent} and
     t[0].kind in {nnkHiddenDeref, nnkDerefExpr} and t[0].len >= 1 and
     classifyType(t[0][0]).ty.kind in {itRef, itPtr}:
    operand = t[0][0]
    fieldName = t[1].strVal
    return true
  false

proc wholeDerefRoot(n: NimNode; operand: var NimNode): bool =
  ## RFC-0005 S8at. True iff `n` is `p[]` of a ref / ptr whose pointee is
  ## held whole -- an anonymous tuple or an array (`wholeObjectPointee` is
  ## false: no field names to split it by) -- so a value chain rooted there
  ## (`p[0] = v`, `p[].a[1] = v`) is written back with one whole-pointee
  ## `isDerefWrite`, the cell `p[]` reads. `operand` is the ref/ptr
  ## expression. It was the "unsupported nnkAsgn shape" decline.
  if n.kind notin {nnkHiddenDeref, nnkDerefExpr} or n.len < 1: return false
  var op = n[0]
  if op.kind == nnkHiddenDeref and op.len == 1 and
     classifyType(op[0]).ty.kind in {itRef, itPtr}:
    op = op[0]
  if op.typeKind == ntyNone: return false
  let opTy = classifyType(op).ty
  if opTy.kind notin {itRef, itPtr}: return false
  let pointee = if opTy.kind == itPtr: opTy.ptrPointeeTy else: opTy.refPointeeTy
  if pointee == nil or pointee.kind notin {itTuple, itArray} or
     wholeObjectPointee(pointee) or
     (pointee.kind == itTuple and pointee.isPlaceholder):
    return false
  operand = op
  true

type FieldStep = object
  ## RFC-0005 S8s. One step of a value field chain: `recv.name` or a
  ## positional `recv[ix]` on a tuple, or `recv.name` on a variant.
  ## RFC-0005 S8u: or `recv[<literal>]` on an array.
  recv:    NimNode    ## the receiver, hidden wrappers stripped
  recvTy:  IRType
  ix:      int        ## tuple field / array element index (-1 on a variant)
  name:    string     ## the field's name ("" for an unnamed tuple element)
  tags:    seq[int]   ## variant: the arms declaring it (empty: a plain field)
  fieldTy: IRType
  idx:     NimNode    ## RFC-0005 S8z: an array element at a SYMBOLIC index
                      ## (`a[i]`): the index expression (nil otherwise)
  lo:      int64      ## RFC-0005 S8z: the array's first index

proc pureIndexExpr(n: NimNode): bool =
  ## RFC-0005 S8z. True when the index expression `n` calls nothing: symbols,
  ## literals, conversions, field and index reads, and builtin operators. A
  ## write's chain is parsed more than once (the read `op=` and a variant
  ## check make, then each rebuilt level), so an index that called a routine
  ## would call it more than once; such an index declines.
  case n.kind
  of nnkSym, nnkCharLit..nnkUInt64Lit: true
  of nnkHiddenStdConv, nnkHiddenSubConv, nnkConv, nnkHiddenDeref, nnkPar,
     nnkDotExpr, nnkBracketExpr, nnkCheckedFieldExpr, nnkStmtListExpr:
    for i in 0 ..< n.len:
      if n[i].kind != nnkEmpty and not (i == 0 and n.kind == nnkConv) and
         not (i == 1 and n.kind == nnkDotExpr) and not pureIndexExpr(n[i]):
        return false
    true
  of nnkInfix, nnkPrefix:
    if n[0].kind != nnkSym or isUserCallee(n[0]): return false
    for i in 1 ..< n.len:
      if not pureIndexExpr(n[i]): return false
    true
  else: false

proc fieldStep(lhs: NimNode; step: var FieldStep): bool =
  ## RFC-0005 S8s. Classifies `lhs` as one step of a value field chain. A
  ## variant arm field's `nnkCheckedFieldExpr` (Nim's discriminant check) is
  ## unwrapped: `valueFieldWrite` models the check with the field's
  ## `isVariantField` read. A discriminator is not a step (its writes have
  ## their own arms), nor is a field whose declared type is the scoped-decline
  ## placeholder.
  var t = unwrapHidden(lhs)
  if t.kind == nnkCheckedFieldExpr and t.len >= 1: t = t[0]
  if t.len != 2: return false
  var derefOp: NimNode
  # RFC-0005 S8at: `p[]` of a whole-held pointee is a chain root itself
  # (`wholeDerefRoot`); `unwrapHidden` would strip the deref.
  let recv = if wholeDerefRoot(t[0], derefOp): t[0] else: unwrapHidden(t[0])
  if recv.kind notin {nnkSym, nnkDotExpr, nnkBracketExpr, nnkCheckedFieldExpr,
                      nnkHiddenDeref, nnkDerefExpr}:   ## RFC-0005 S8at
    return false
  var recvTy: IRType
  if recv.kind in {nnkHiddenDeref, nnkDerefExpr}:
    let o = classifyType(derefOp).ty
    recvTy = if o.kind == itPtr: o.ptrPointeeTy else: o.refPointeeTy
  else:
    recvTy = classifyType(recv).ty
  if recvTy == nil: return false
  step = FieldStep(recv: recv, recvTy: recvTy, ix: -1)
  if t.kind == nnkBracketExpr and recvTy.kind == itArray:
    # RFC-0005 S8u: an array element at a constant index (`a[0]`,
    # `o.arr[2]`). Nim wraps the index in a conversion to the array's index
    # type; a literal one is in bounds (Nim rejects `a[7]` on an
    # `array[3, T]` at compile time). RFC-0005 S8z: the element's position
    # is the literal less the array's first index (`array[1..3, T]`'s `a[1]`
    # is position 0; S8u declined such an array). A symbolic index is a step
    # too (`idx`): `valueFieldWrite` stores it with `isIndexAssign`.
    step.lo = arrayIndexLow(recv)
    var ixNode = t[1]
    while ixNode.kind in {nnkHiddenStdConv, nnkHiddenSubConv} and ixNode.len >= 1:
      ixNode = ixNode[ixNode.len - 1]
    if ixNode.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                       nnkInt64Lit, nnkCharLit}:
      step.ix = int(ixNode.intVal - step.lo)
      if step.ix < 0 or step.ix >= recvTy.size: return false
    elif ixNode.typeKind != ntyNone and
         classifyType(ixNode).ty.kind in {itInt, itBool} and
         pureIndexExpr(ixNode):
      # RFC-0005 S8am (S8z's remainder, item 6): `itBool` joins `itInt`
      # here -- an `array[bool, T]` field/element write's index
      # (`o.arr[flag] = v`) is a value-field-chain step exactly like an int
      # one; the walker side (`isIndexAssign`, via `valueFieldWrite`) is
      # bool-index-ready since `coerceArrayBoolIndex` (runtime.nim).
      step.idx = t[1]
    else:
      return false
    step.fieldTy = recvTy.elemTy
    return step.fieldTy != nil and
           not isUnsupportedFieldPlaceholder(step.fieldTy)
  if t.kind == nnkBracketExpr:
    if recvTy.kind != itTuple or
       t[1].kind notin {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                        nnkInt64Lit}:
      return false
    step.ix = int(t[1].intVal)
    if step.ix < 0 or step.ix >= recvTy.fields.len: return false
    step.name = recvTy.fieldNames[step.ix]
    step.fieldTy = recvTy.fields[step.ix]
    return true
  if t.kind != nnkDotExpr or t[1].kind notin {nnkIdent, nnkSym}: return false
  step.name = t[1].strVal
  case recvTy.kind
  of itTuple:
    step.ix = recvTy.fieldNames.find(step.name)
    if step.ix < 0: return false
    step.fieldTy = recvTy.fields[step.ix]
  of itVariant:
    if step.name == recvTy.vDiscName: return false
    let pix = recvTy.vPlainFieldNames.find(step.name)
    if pix >= 0:
      step.fieldTy = recvTy.vPlainFieldTypes[pix]
    else:
      for arm in recvTy.vArms:
        let ix = arm.fieldNames.find(step.name)
        if ix >= 0:
          step.tags.add arm.tagOrdinal
          if step.fieldTy == nil: step.fieldTy = arm.fieldTypes[ix]
      if step.tags.len == 0: return false
  of itMultiVariant:
    for ax in recvTy.mvAxes:
      if step.name == ax.discName: return false
    let pix = recvTy.mvPlainFieldNames.find(step.name)
    if pix >= 0:
      step.fieldTy = recvTy.mvPlainFieldTypes[pix]
    else:
      for ax in recvTy.mvAxes:
        for arm in ax.arms:
          let ix = arm.fieldNames.find(step.name)
          if ix >= 0:
            step.tags.add arm.tagOrdinal
            if step.fieldTy == nil: step.fieldTy = arm.fieldTypes[ix]
        if step.tags.len > 0: break
      if step.tags.len == 0: return false
  else:
    return false
  step.fieldTy != nil and not isUnsupportedFieldPlaceholder(step.fieldTy)

proc valueFieldTy(lhs: NimNode): IRType =
  ## RFC-0005 S8p. The written field's type when `lhs` is a field chain over a
  ## VALUE tuple or object rooted at a variable (`o.a`, `o.inner.b`,
  ## `result.a`), nil for any other lvalue. A ref/ptr step is a heap write
  ## (the `nnkAsgn` arms above `valueFieldWrite`'s caller) and keeps its
  ## decline. RFC-0005 S8s: a step may also be a positional tuple element
  ## (`q[0]`, `q.a[1]`) or a field of a value variant or multi-variant, plain
  ## or in an arm (`v.a`); before S8s both declined.
  ## Pure: parses nothing, so a caller can ask before lifting any call.
  var step: FieldStep
  if not fieldStep(lhs, step): return nil
  var operand: NimNode
  var fieldName: string
  if step.recv.kind != nnkSym and valueFieldTy(step.recv) == nil and
     not heapFieldRoot(step.recv, operand, fieldName) and   ## RFC-0005 S8ar
     not wholeDerefRoot(step.recv, operand):                ## RFC-0005 S8at
    return nil
  step.fieldTy

proc valueFieldChecked(lhs: NimNode): bool =
  ## RFC-0005 S8s. True when some step of the chain `valueFieldTy` accepted
  ## is a variant ARM field: writing through it checks the discriminant.
  ## RFC-0005 S8z: or an array element at a symbolic index, whose
  ## `IndexDefect` Nim likewise raises before it evaluates the value
  ## (probed: `a[5] = raiser()` raises `IndexDefect`, not the value's
  ## `ValueError`).
  var step: FieldStep
  if not fieldStep(lhs, step): return false
  step.tags.len > 0 or step.idx != nil or
    (step.recv.kind != nnkSym and valueFieldChecked(step.recv))

proc valueFieldWrite(lhs: NimNode, newVal: IRExpr,
                     preamble: var seq[IRStmt], ctx: ParseCtx): ValueFieldWrite =
  ## RFC-0005 S8p. `o.a = v` / `o.inner.b = v` / `result.a += v` on a value
  ## tuple or object, for an `lhs` `valueFieldTy` accepts. Nim writes the one
  ## field in place; the other fields keep their values. That is the same as
  ## assigning the root a rebuilt tuple whose written field is `newVal` and
  ## whose other fields are reads of the old ones -- one level per step.
  ## RFC-0005 S8s: a variant step rebuilds with `iekVariantFieldSet`. Its
  ## discriminant check is not made here: the caller parses the read of
  ## `lhs` first when `valueFieldChecked` holds, and that read's
  ## `isVariantField` forks the out-of-arm `FieldDefect` before any write.
  var step: FieldStep
  discard fieldStep(lhs, step)
  let recvIR = parseExpr(step.recv, preamble, ctx)
  # RFC-0005 S8bw (item 2): every use of `recvIR` below copies the old
  # parts back into the same root, so a global root's unwritten parts are
  # not observed by it.
  block:
    var root = recvIR
    while root != nil and root.kind in {iekField, iekIndex}:
      root = if root.kind == iekField: root.obj else: root.arr
    if root != nil and root.kind == iekVar: root.vCopy = true
  let rebuilt =
    if step.recvTy.kind == itArray and step.idx != nil:
      # RFC-0005 S8z: a symbolic index. The old array is copied into a
      # temporary, `isIndexAssign` forks the `IndexDefect` and stores the one
      # element (`ite` per position), and the temporary is the rebuilt value.
      # The index is parsed as a read's is (`indexConvPending`: Nim checks it
      # as an index, not as a conversion to the index type).
      let tmp = freshSynth(ctx, "aw")
      preamble.add mkLet(tmp, step.recvTy, recvIR)
      ctx.indexConvPending = step.idx.kind in {nnkHiddenStdConv, nnkHiddenSubConv}
      let idxIR = parseExpr(step.idx, preamble, ctx)
      ctx.indexConvPending = false
      preamble.add mkIndexAssignStmt(tmp, idxIR, newVal, siteLoc(step.recv),
                                     step.lo)
      mkVar(tmp)
    elif step.recvTy.kind == itArray:
      # RFC-0005 S8u: the other elements are constant-index reads of the old
      # array (`iekIndex`'s concrete fast path: no fork).
      var elems: seq[IRExpr]
      for i in 0 ..< step.recvTy.size:
        elems.add(if i == step.ix: newVal
                  else: mkIndex(recvIR, mkIntLit(i)))
      mkArrayLit(elems, step.recvTy.elemTy)
    elif step.recvTy.kind == itTuple:
      var elems: seq[IRExpr]
      for i in 0 ..< step.recvTy.fields.len:
        elems.add(if i == step.ix: newVal
                  else: mkField(recvIR, i, step.recvTy.fieldNames[i]))
      mkTupleLit(elems, step.recvTy)
    else:
      mkVariantFieldSet(recvIR, step.name, step.tags, newVal)
  var operand: NimNode
  var fieldName: string
  if step.recv.kind == nnkSym:
    ValueFieldWrite(root: step.recv.strVal, value: rebuilt)
  elif wholeDerefRoot(step.recv, operand):
    # RFC-0005 S8at: the chain's root is `p[]` of a whole-held pointee; the
    # rebuilt value is stored whole, as `p[] = v`.
    let opTy = classifyType(operand).ty
    let isPtr = opTy.kind == itPtr
    let pointeeTy = if isPtr: opTy.ptrPointeeTy else: opTy.refPointeeTy
    let ptrIR = parseExpr(operand, preamble, ctx)
    ValueFieldWrite(heap: mkDerefWrite(ptrIR, rebuilt, pointeeTy, isPtr))
  elif valueFieldTy(step.recv) == nil and
       heapFieldRoot(step.recv, operand, fieldName):
    # RFC-0005 S8ar: the chain's root is a ref/ptr object's field; the
    # rebuilt field is written back to its heap cell, as `p.inner = v`.
    let opTy = classifyType(operand).ty
    let isPtr = opTy.kind == itPtr
    let pointeeTy = if isPtr: opTy.ptrPointeeTy else: opTy.refPointeeTy
    let ptrIR = parseExpr(operand, preamble, ctx)
    ValueFieldWrite(heap: mkFieldDerefWrite(ptrIR, rebuilt, step.recvTy,
                                            pointeeTy, fieldName, isPtr))
  else:
    valueFieldWrite(step.recv, rebuilt, preamble, ctx)

proc discReassignStmt(recvName: string; ty: IRType; discName: string;
                      rhsNode: NimNode; preamble: var seq[IRStmt];
                      ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8at. `recvName.<discName> = rhs` on the variant or
  ## multi-variant variable `recvName` -- the Phase 11 / A4 statements the
  ## bare-variable arm of `parseAsgn` builds (a static tag, a symbolic one,
  ## a multi-variant axis), factored for a field chain's copy.
  let rhs = unwrapHidden(rhsNode)
  let tagIR = discTagLit(parseExpr(rhs, preamble, ctx))
  if ty.kind == itVariant:
    if tagIR.kind == iekIntLit:
      var tagName = if rhs.kind == nnkSym: rhs.strVal else: ""
      for arm in ty.vArms:
        if arm.tagOrdinal == int(tagIR.ival):
          tagName = arm.tagName; break
      return mkVariantReassign(recvName, int(tagIR.ival), tagName,
                               branchGroups(ty.vArms))
    return mkVariantReassignSymbolic(recvName, "", tagIR, branchGroups(ty.vArms))
  for ax in ty.mvAxes:
    if ax.discName == discName:
      return mkVariantReassignSymbolic(recvName, ax.discName, tagIR,
                                       branchGroups(ax.arms))
  ctx.declineMarker(feUnsupportedStmtKind,
    "RFC-0005 S8at: discriminator `" & discName & "` names no axis of `" &
    $ty & "`")

proc writeBackField(recv: NimNode; newVal: IRExpr; preamble: var seq[IRStmt];
                    ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8at. `recv = newVal` for a field chain `valueFieldTy` or
  ## `heapFieldRoot` accepts: the value chain's rebuilt root assignment, or
  ## the field-deref write of a ref / ptr object's field.
  if valueFieldTy(recv) != nil:
    return valueFieldWrite(recv, newVal, preamble, ctx).toStmt
  var operand: NimNode
  var fieldName: string
  discard heapFieldRoot(recv, operand, fieldName)
  let opTy = classifyType(operand).ty
  let isPtr = opTy.kind == itPtr
  let pointeeTy = if isPtr: opTy.ptrPointeeTy else: opTy.refPointeeTy
  let ptrIR = parseExpr(operand, preamble, ctx)
  mkFieldDerefWrite(ptrIR, newVal, classifyType(recv).ty, pointeeTy,
                    fieldName, isPtr)

proc dottedFieldShape(fieldNode: NimNode): bool =
  ## RFC-0005 S8ao (S8aj's remainder), generalised by S8ap from `add` to
  ## every #145 mutation (was `dottedSeqAddShape`). True iff `fieldNode` (a
  ## dotted field chain -- `o.s`, `a.b.s`, or a ref/ptr object's field
  ## `p.s`) is a shape `dottedFieldMutate` below can lower: either step of
  ## the R6 ref-field-write arm (`parseAsgn`, `p.field = v`) -- a
  ## `nnkDotExpr` whose own receiver is a `HiddenDeref`/`DerefExpr` over a
  ## genuine `ref`/`ptr` -- or a `valueFieldTy`-accepted value-field chain.
  ## Pure (mirrors `valueFieldTy`'s own "parses nothing" contract): the
  ## caller decides eligibility with this BEFORE lifting the mutation's
  ## arguments, so an ineligible shape (e.g. a dotted field reached through
  ## a GLOBAL, not a local/param root -- S8an's own separate remainder)
  ## falls through to the existing N49 decline with its arguments left
  ## unparsed, same as today.
  let lhsFW = if fieldNode.kind == nnkCheckedFieldExpr and fieldNode.len >= 1:
                fieldNode[0]
              else: fieldNode
  if lhsFW.kind == nnkDotExpr and lhsFW.len == 2 and
     lhsFW[0].kind in {nnkHiddenDeref, nnkDerefExpr} and lhsFW[0].len >= 1:
    classifyType(lhsFW[0][0]).ty.kind in {itRef, itPtr}
  else:
    valueFieldTy(fieldNode) != nil

type DottedOp = enum
  ## RFC-0005 S8ap. The bare-symbol #145 mutation arm's IR constructors
  ## (`parseStmtInner`), one per mutation: `dottedFieldMutate` applies to a
  ## field's old value the same one the bare arm applies to a variable's.
  doSeqAdd, doSeqDel, doSeqInsert, doTabDel, doTabSet, doSetIncl, doSetExcl,
  doStrConcat, doStrUnsupported, doStrIndexAssign,
  doSeqInsertGrow   ## RFC-0005 S8ar: `insert`'s grow phase

proc mutationOp(calleeName: string; fk: IRTypeKind; n: NimNode): DottedOp =
  ## RFC-0005 S8ap (factored by S8at). The bare arm's IR for a mutation
  ## `isKnownMutatingReceiverCall` accepted, by name and receiver kind.
  case calleeName
  of "add":
    if fk == itSeq: doSeqAdd
    elif classifyType(n[2]).ty.kind == itString or
         unwrapHidden(n[2]).typeKind == ntyChar: doStrConcat
    else: doStrUnsupported
  of "del": (if fk == itSeq: doSeqDel else: doTabDel)
  of "insert": doSeqInsert
  of "incl": doSetIncl
  of "excl": doSetExcl
  else: doTabSet  # "[]="

proc elemLvalueBracket(n: NimNode): NimNode =
  ## RFC-0005 S8at. `n` as a two-child `nnkBracketExpr` (base, index), or
  ## nil: an array element is one already (`a[1]`); a `Table` value read
  ## through `[]`'s `var` overload is the call `[](t, k)` under a hidden
  ## deref, which `parseAsgn`'s `t[k] = v` arm takes as the bracket.
  if n.kind == nnkBracketExpr and n.len == 2: return n
  # RFC-0005 S8bc (item 7): the cell `mgetOrPut(t, k[, d])` returns a
  # reference to is `t[k]` once the call has run (it inserts an absent key),
  # so its writers write back through `t[k]`; their read of the cell's old
  # value parses the call itself (`parseMGetOrPut`), which performs the
  # insert first.
  let mg = mgetOrPutCall(n)
  if mg != nil: return nnkBracketExpr.newTree(mg[1], mg[2])
  let c = unwrapHidden(n)
  if c.kind in {nnkCall, nnkCommand} and c.len == 3 and
     c[0].kind == nnkSym and c[0].strVal == "[]":
    return nnkBracketExpr.newTree(c[1], c[2])
  nil

proc arrayElemLvalue(n: NimNode): bool =
  ## RFC-0005 S8at. `n` is an element of an array value (`a[1]`, `o.a[i]`,
  ## `p.a[k]`), or the value of a `Table` at a key (`t["a"]`, `p.t[k]`),
  ## indexed by a literal or a plain variable, so evaluating the index
  ## twice is evaluating it once.
  let b = elemLvalueBracket(n)
  b != nil and
    unwrapHidden(b[1]).kind in {nnkSym, nnkCharLit .. nnkUInt64Lit,
                                nnkFloatLit .. nnkFloat64Lit,
                                nnkStrLit .. nnkTripleStrLit} and
    classifyType(unwrapHidden(b[0])).ty.kind in {itArray, itTable}

proc pureIndexNode(n: NimNode): bool =
  ## RFC-0005 S8bc. An index evaluating it twice is evaluating it once: a
  ## literal or a plain variable (the gate `arrayElemLvalue` applies).
  unwrapHidden(n).kind in {nnkSym, nnkCharLit .. nnkUInt64Lit,
                           nnkFloatLit .. nnkFloat64Lit,
                           nnkStrLit .. nnkTripleStrLit}

proc pureLvalueTarget(n: NimNode): NimNode =
  ## RFC-0005 S8bl (item 1; factored out of S8bc's `parseIncDecLvalue`). The
  ## lvalue a mutation of `n` writes back through (`parseAsgn`), when reading
  ## `n` and then writing it evaluates its address once: a variable, an
  ## array element or a Table value (`arrayElemLvalue`; the write goes to
  ## `elemLvalueBracket`), a seq variable's element at a pure index, a field
  ## path `dottedFieldShape` accepts, or a dereference. nil otherwise.
  let lhs = unwrapHidden(n)
  let fieldNode = if lhs.kind == nnkCheckedFieldExpr and lhs.len >= 1: lhs[0]
                  else: lhs
  if lhs.kind == nnkSym and lhs.symKind in {nskVar, nskResult, nskParam}: lhs
  elif arrayElemLvalue(n): elemLvalueBracket(n)
  elif lhs.kind == nnkBracketExpr and lhs.len == 2 and
       unwrapHidden(lhs[0]).kind == nnkSym and
       classifyType(unwrapHidden(lhs[0])).ty.kind == itSeq and
       pureIndexNode(lhs[1]): lhs
  elif fieldNode.kind == nnkDotExpr and dottedFieldShape(fieldNode): lhs
  elif lhs.kind == nnkDerefExpr and lhs.len == 1: lhs
  else: nil

proc writeBack(target: NimNode; val: IRExpr; preamble: var seq[IRStmt];
               ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bl. `target = val` through the plain assignment's lvalue arm.
  parseAsgn(nnkAsgn.newTree(target, newEmptyNode()), val, preamble, ctx)

proc parseIncDecLvalue(n: NimNode; preamble: var seq[IRStmt];
                       ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bc (item 7). `inc(x[, y])` / `dec(x[, y])` -- the system
  ## magics -- on any receiver the bare-symbol int arm (Phase 15 R8) does
  ## not take. SOUNDNESS: those reached the user-call fallback, where a
  ## bodiless `{.magic.}` routine is registered with an EMPTY body, so the
  ## write to the `var` receiver was dropped without a record: `inc a[1]`,
  ## `inc t[k]`, `inc o.f`, `inc s[i]`, `inc p[]` left the value unchanged
  ## and a target behind the old value was a clean, wrong sxSat. Now:
  ##
  ##   * an unranged int receiver that is an array element, a Table value or
  ##     the cell `mgetOrPut` returns (`arrayElemLvalue`), a seq element
  ##     with a pure index, a field path `dottedFieldShape` accepts, or a
  ##     dereference, is `x = x +/- y`: the old value is read and bound
  ##     first (the element's IndexDefect / KeyError, `mgetOrPut`'s insert),
  ##     then the step, then the write through the plain assignment's own
  ##     lvalue arm (`parseAsgn`);
  ##   * every other receiver -- an enum, a char, a ranged int, any other
  ##     shape -- declines on its path (`feUnsupportedOp`), never the silent
  ##     no-op.
  let lty = classifyType(n[1]).ty
  let isInc = n[0].strVal == "inc"
  let target =
    if lty.kind != itInt or lty.hasRange: nil
    else: pureLvalueTarget(n[1])
  if target == nil:
    return ctx.declineAtSite(feUnsupportedOp,
      siteMsg(n, "`" & n[0].strVal & "` on `" & n[1].repr & "` (" &
              $lty.kind & ") is not modelled -- path degraded to sxUnknown"),
      "`" & n[0].strVal & "` on this receiver is not modelled")
  let oldTmp = freshSynth(ctx, "incOld")
  preamble.add mkLet(oldTmp, lty, parseExpr(n[1], preamble, ctx))
  let stepIR = if n.len >= 3: parseExpr(n[2], preamble, ctx) else: mkIntLit(1)
  let newVal = mkBinop(if isInc: bAdd else: bSub, mkVar(oldTmp), stepIR)
  parseAsgn(nnkAsgn.newTree(target, newEmptyNode()), newVal, preamble, ctx)

proc callMagic(n: NimNode): string =
  ## RFC-0005 S8bl. The magic of the system routine call `n` resolves to, or
  ## "" (a user routine, an unresolved head, a routine with no magic).
  if n.kind notin {nnkCall, nnkCommand, nnkInfix} or n.len < 2 or
     n[0].kind != nnkSym or isUserCallee(n[0]):
    return ""
  implMagic(resolveRoutineImpl(n[0]))

proc varMagicShapeDecline(n: NimNode; magic: string; ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bl (item 1). A modelled magic on an argument shape its arm
  ## does not accept, declined on its path, naming the magic.
  ctx.declineAtSite(feUnsupportedOp,
    siteMsg(n, "`" & n[0].strVal & "` (magic \"" & magic & "\") on `" &
            n.repr & "` is not modelled for this argument shape -- path " &
            "degraded to sxUnknown"),
    "`" & n[0].strVal & "` (magic " & magic & ") on this argument is not " &
    "modelled")

proc parseZeroWrite(n: NimNode; magic: string; preamble: var seq[IRStmt];
                    ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bl (item 1). `wasMoved(x)` / `=wasMoved(x)` / `reset(x)`:
  ## `x` becomes its type's zero (`zeroValueForType`), as Nim's binary-zero
  ## reset leaves it (probed: an int reads 0, a seq or a string is empty).
  let target = pureLvalueTarget(n[1])
  let zero = zeroValueForType(classifyType(n[1]).ty)
  if target == nil or zero == nil:
    return varMagicShapeDecline(n, magic, ctx)
  writeBack(target, zero, preamble, ctx)

proc parseSetLen(n: NimNode; magic: string; preamble: var seq[IRStmt];
                 ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bl (item 1). `setLen(s, n)` on a seq or a string: the old
  ## value is read and bound, the length guarded as `newSeq`'s (`Natural`:
  ## `RangeDefect` below 0; a length above `maxModelledInitialSize`
  ## declines), the resized value bound (`isSetLen`) and written back.
  ## `setLenUninit` leaves a grown slot uninitialised -- memory no model
  ## can name -- so a grow declines on its path; its shrink is `setLen`'s.
  let target = pureLvalueTarget(n[1])
  let ty = classifyType(n[1]).ty
  if target == nil or n.len != 3 or ty.kind notin {itSeq, itString}:
    return varMagicShapeDecline(n, magic, ctx)
  let oldTmp = freshSynth(ctx, "setLenOld")
  preamble.add mkLet(oldTmp, ty, parseExpr(n[1], preamble, ctx))
  let lenIR = parseNewSeqLen(n[2], n[0].strVal, preamble, ctx)
  if magic == "SetLengthSeqUninit":
    preamble.add mkIf(@[mkBranch(
      mkBinop(bGt, lenIR, mkSeqLen(mkVar(oldTmp), siteLoc(n))),
      ctx.declineAtSite(feUnsupportedOp,
        siteMsg(n, "`setLenUninit` growing a seq leaves the new slots " &
                "uninitialised -- path degraded to sxUnknown"),
        "`setLenUninit` grow (uninitialised slots) is not modelled"))])
  let newTmp = freshSynth(ctx, "setLenNew")
  preamble.add mkSetLenStmt(newTmp, mkVar(oldTmp), lenIR, ty, siteLoc(n))
  writeBack(target, mkVar(newTmp), preamble, ctx)

proc parseVarMagicStmt(n: NimNode; preamble: var seq[IRStmt];
                       ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bl (item 1). A statement-position call of a system magic
  ## with a `var` parameter that no older arm models (`varParamMagics`), or
  ## nil to let the older arms (and, past them, `ensureProcRegistered`'s
  ## decline) take it. SOUNDNESS: every one of these was registered with
  ## an empty body -- `swap(a[0], a[2])` left `a` unchanged, a false sxSat.
  ##
  ##   * `swap(a, b)`: Nim takes both addresses, then exchanges; here both
  ##     are read (each one's `IndexDefect` / `KeyError` in that order) and
  ##     bound, then `a = b0` and `b = a0`. Equal places swap to themselves;
  ##   * `wasMoved(x)`, `=wasMoved(x)` (semcheck calls the type's generated
  ##     hook), and system's `reset(x)` (not itself a magic; its body is
  ##     `=destroy` then `wasMoved`): x's zero;
  ##   * `setLen` / `setLenUninit`: `parseSetLen`;
  ##   * `=`(d, s) / `=copy(d, s)` / `=sink(d, s)`: the assignment `d = s`;
  ##   * `+=`(x, y) / `-=`(x, y) spelled as a call: the operator's own arm;
  ##   * `new(x)` on an lvalue other than a variable (whose `new(x)` arm
  ##     S8u wrote): a fresh cell bound (`isNew`), then written back.
  if n.kind notin {nnkCall, nnkCommand} or n.len < 2 or n[0].kind != nnkSym:
    return nil
  let magic = callMagic(n)
  if magic.len == 0:
    if n.len == 2 and n[0].strVal == "reset" and not isUserCallee(n[0]) and
       isStdlibDecl(n[0]):
      return parseZeroWrite(n, "reset", preamble, ctx)
    # Semcheck spells `wasMoved(a)` as a call of the type's generated
    # `=wasMoved` hook (`isGeneratedHook`), whose body is the magic.
    if n.len == 2 and n[0].strVal == "=wasMoved" and isGeneratedHook(n[0]):
      return parseZeroWrite(n, "WasMoved", preamble, ctx)
    return nil
  case magic
  of "Swap":
    if n.len != 3: return varMagicShapeDecline(n, magic, ctx)
    let ta = pureLvalueTarget(n[1])
    let tb = pureLvalueTarget(n[2])
    if ta == nil or tb == nil: return varMagicShapeDecline(n, magic, ctx)
    let ty = classifyType(n[1]).ty
    let a0 = freshSynth(ctx, "swapA")
    preamble.add mkLet(a0, ty, parseExpr(n[1], preamble, ctx))
    let b0 = freshSynth(ctx, "swapB")
    preamble.add mkLet(b0, ty, parseExpr(n[2], preamble, ctx))
    preamble.add writeBack(ta, mkVar(b0), preamble, ctx)
    writeBack(tb, mkVar(a0), preamble, ctx)
  of "WasMoved":
    if n.len != 2: return varMagicShapeDecline(n, magic, ctx)
    parseZeroWrite(n, magic, preamble, ctx)
  of "SetLengthSeq", "SetLengthStr", "SetLengthSeqUninit":
    parseSetLen(n, magic, preamble, ctx)
  of "Asgn":
    if n.len != 3: return varMagicShapeDecline(n, magic, ctx)
    parseAsgn(nnkAsgn.newTree(unwrapHidden(n[1]), n[2]), nil, preamble, ctx)
  of "Inc", "Dec":
    if n[0].strVal in ["+=", "-="] and n.len == 3:
      return parseStmtInner(nnkInfix.newTree(n[0], n[1], n[2]), preamble, ctx)
    nil
  of "New":
    if n[0].strVal != "new" or n.len != 2 or
       unwrapHidden(n[1]).kind == nnkSym:
      return nil   # S8u's `new(x)` arm; `unsafeNew` declines at registration
    let target = pureLvalueTarget(n[1])
    let ty = classifyType(n[1]).ty
    if target == nil or ty.kind != itRef:
      return varMagicShapeDecline(n, magic, ctx)
    let cell = freshSynth(ctx, "newCell")
    preamble.add mkNewT(cell, ty)
    writeBack(target, mkVar(cell), preamble, ctx)
  else:
    nil

proc parseMoveExpr(n, calleeSym: NimNode; preamble: var seq[IRStmt];
                   ctx: ParseCtx): IRExpr =
  ## RFC-0005 S8bl (item 1). `move(x)`: its value is x's, and x becomes its
  ## type's zero (probed: after `let b = move(a)` an int `a` reads 0 and a
  ## seq or a string is empty). The value is read and bound, then the zero
  ## written back. nil for any other call; an argument shape this does not
  ## accept reaches `ensureProcRegistered`'s magic decline.
  if n.len != 2 or callMagic(n) != "Move": return nil
  let target = pureLvalueTarget(n[1])
  let ty = classifyType(n).ty
  let zero = zeroValueForType(ty)
  if target == nil or zero == nil: return nil
  let tmp = freshSynth(ctx, "moved")
  preamble.add mkLet(tmp, ty, parseExpr(n[1], preamble, ctx))
  preamble.add writeBack(target, zero, preamble, ctx)
  mkVar(tmp)

proc dottedFieldMutate(fieldNode: NimNode, op: DottedOp, args: seq[IRExpr],
                       preamble: var seq[IRStmt], ctx: ParseCtx): IRStmt
  ## RFC-0005 S8bl fwd decl (defined below), for `parseTableForLoop`.

proc writesName(s: IRStmt; name: string): bool =
  ## RFC-0005 S8bl (item 4). The leaf statement `s` may write the env
  ## variable `name`: an assignment to it, an element store into it or a
  ## `pop` of it, a `new` bound to it, a discriminator reassignment of it,
  ## or a call one of whose arguments mentions it (a `var` argument is
  ## copied back to it).
  proc mentions(e: IRExpr): bool =
    var refs: HashSet[string]
    collectVarRefs(e, refs)
    name in refs
  case s.kind
  of isAssign: s.aname == name
  of isIndexAssign: s.iaRecvName == name
  of isSeqPop: s.spRecvName == name
  of isNew: s.nRetName == name
  of isVariantReassign: s.vrObjName == name
  of isVariantReassignSymbolic: s.vrsObjName == name
  of isCall:
    var any = false
    for a in s.cargs:
      if mentions(a): any = true
    any
  else: false

proc mutViewWriteBack(s: IRStmt; name: string;
                      writeBack: proc(): IRStmt): IRStmt =
  ## RFC-0005 S8bl (item 4). `s` with `writeBack()` placed right after every
  ## statement that writes `name` (`writesName`), at any nesting.
  if s == nil: return nil
  case s.kind
  of isBlock:
    var stmtsOut: seq[IRStmt]
    for c in s.stmts: stmtsOut.add mutViewWriteBack(c, name, writeBack)
    result = s
    result.stmts = stmtsOut
  of isIf:
    result = s
    for i in 0 ..< result.branches.len:
      result.branches[i].body =
        mutViewWriteBack(result.branches[i].body, name, writeBack)
    result.elseBody = mutViewWriteBack(s.elseBody, name, writeBack)
  of isWhile:
    result = s
    result.wbody = mutViewWriteBack(s.wbody, name, writeBack)
  of isTry:
    result = s
    result.tryBody = mutViewWriteBack(s.tryBody, name, writeBack)
    for i in 0 ..< result.tryHandlers.len:
      result.tryHandlers[i].body =
        mutViewWriteBack(result.tryHandlers[i].body, name, writeBack)
    result.tryFinally = mutViewWriteBack(s.tryFinally, name, writeBack)
  else:
    result = if writesName(s, name): mkBlock(@[s, writeBack()]) else: s

proc parseTableForLoop(n: NimNode; ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bc (item 6). A `for` over a `Table`'s stdlib `pairs`, `keys`
  ## or `values` (`for k, v in t` is `pairs(t)` after semcheck; `for (k, v)
  ## in t.pairs` and the single-variable `for kv in t.pairs` too), or nil
  ## for any other loop. It fell to the iterator inliner, which walked the
  ## stdlib body over the table's hidden slots and declined. Lowered as a
  ## bounded unroll over the table's key set:
  ##
  ##   tabKeys(ks := t)               (`isTabKeys`: an enumeration of the
  ##   let L = ks.len                  present keys in a FREE order)
  ##   var i = 0
  ##   while i < L:
  ##     let k = ks[i]
  ##     let v = t[k]                 (pairs / values: the LIVE value, as
  ##     body                          Nim reads `t.data[h].val` per yield)
  ##     if t.len != L: <decline>     (Nim asserts the length unchanged)
  ##     i += 1
  ##
  ## The walker's k-unroll bounds the trip count (`maxLoopUnwind`, declining
  ## past it), and a table that can hold two or more entries taints the path
  ## `feTableIterOrder`: Nim visits the keys in hash order, the model in any
  ## order, so a candidate is replayed and one whose label needs another
  ## order than Nim's is refuted to sxUnknown -- the order-dependent program
  ## declines; an order-independent one is confirmed. An sxUnsat holds for
  ## every order, Nim's among them.
  ##
  ## The length check is a scoped decline, not a modelled `AssertionDefect`:
  ## the assert is compiled out under `--assertions:off`. A table read
  ## through a call or another non-variable expression is iterated from the
  ## value bound once (the body cannot reach it). A float key declines: a
  ## NaN entry counts in the size but is never present, so no enumeration
  ## of the present keys has the size. `mpairs` / `mvalues` (a mutable view
  ## of the value) keep the inliner's decline.
  let iterExpr = n[^2]
  if iterExpr.kind notin {nnkCall, nnkCommand} or iterExpr.len != 2 or
     iterExpr[0].kind != nnkSym or
     iterExpr[0].strVal notin ["pairs", "keys", "values", "mpairs",
                               "mvalues"] or
     not isStdlibDecl(iterExpr[0]):
    return nil
  let container = iterExpr[1]
  let tabCls = classifyType(container)
  if tabCls.ty.kind != itTable: return nil
  let iterName = iterExpr[0].strVal
  var vars: seq[NimNode]
  for i in 0 ..< n.len - 2:
    if n[i].kind == nnkVarTuple:
      for c in n[i]:
        if c.kind != nnkEmpty: vars.add c
    else: vars.add n[i]
  var shapeOk =
    case iterName
    of "pairs": vars.len in [1, 2]
    of "mpairs": vars.len == 2   # RFC-0005 S8bl: `(k, var v)` unpacked
    else: vars.len == 1
  for v in vars:
    if v.kind != nnkSym: shapeOk = false
  if not shapeOk:
    return ctx.declineAtSite(feUnsupportedStmtKind,
      siteMsg(n, "for-loop over a Table's `" & iterName & "` with " &
              $vars.len & " loop variable(s) is not modelled"),
      "for-loop over a Table's `" & iterName & "`: loop-variable shape")
  let keyTy = tabCls.ty.tabKeyTy
  let valTy = tabCls.ty.tabValTy
  if keyTy.kind notin {itString, itInt, itBool}:
    return ctx.declineAtSite(feUnsupportedOp,
      siteMsg(n, "iteration over a Table keyed by " & $keyTy &
              " is not modelled (a NaN float key counts in the size but is " &
              "never present) -- path degraded to sxUnknown"),
      "iteration over a Table keyed by " & $keyTy.kind & " is not modelled")
  let intTy = tInt(64, signed = true)
  let bare = unwrapHidden(container)
  let live = bare.kind == nnkSym or
             (bare.kind == nnkDotExpr and dottedFieldShape(bare))
  let mutView = iterName in ["mpairs", "mvalues"]
  if mutView and not live:
    return ctx.declineAtSite(feUnsupportedOp,
      siteMsg(n, "`" & iterName & "` over a Table reached other than as a " &
              "variable or a field path is not modelled"),
      "`" & iterName & "` over this Table is not modelled")
  var body = parseLoopBody(n[^1], ctx).body   # a `continue` leaves the body
  var pre: seq[IRStmt]
  let snapIR = liftIndexContainer(parseExpr(container, pre, ctx), tabCls.ty,
                                  pre, ctx)
  let ksName = freshSynth(ctx, "tks")
  pre.add mkTabKeysStmt(ksName, snapIR, keyTy, siteLoc(n))
  let lenName = freshSynth(ctx, "tkn")
  pre.add mkLet(lenName, intTy, mkSeqLen(mkVar(ksName)))
  let ivName = freshSynth(ctx, "iv")
  pre.add mkLet(ivName, intTy, mkIntLit(0))
  var loopStmts: seq[IRStmt]
  let kSynth = freshSynth(ctx, "tkk")
  loopStmts.add mkIndexStmt(kSynth, mkVar(ksName), mkVar(ivName), keyTy)
  var vIR: IRExpr = nil
  if iterName != "keys":
    var inner: seq[IRStmt]
    let recvNow =
      if live: liftIndexContainer(parseExpr(container, inner, ctx),
                                  tabCls.ty, inner, ctx)
      else: snapIR
    loopStmts.add inner
    let vSynth = freshSynth(ctx, "tkv")
    loopStmts.add mkIndexStmt(vSynth, recvNow, mkVar(kSynth), valTy)
    vIR = mkVar(vSynth)
  if mutView:
    # RFC-0005 S8bl (item 4). `mpairs` / `mvalues` yield `var V`: the loop
    # variable IS the table's value at the key, so a write to it is a write
    # to `t[k]`. The variable is bound to the value, and every statement of
    # the body that writes it (an assignment, an element store or `pop`, a
    # call taking it, a `new`, a discriminator reassignment) is followed at
    # once by the store `t[k] = v` (`mutViewWriteBack`), so a later read of
    # `t` -- in the body, after a `break`, past a raise -- sees the write.
    # It was the inliner's decline.
    let vName = vars[^1].strVal
    loopStmts.add mkLet(vName, valTy, vIR)
    if vars.len == 2:
      loopStmts.add mkLet(vars[0].strVal, keyTy, mkVar(kSynth))
    proc writeBack(): IRStmt =
      var wbPre: seq[IRStmt]
      let st =
        if bare.kind == nnkSym:
          mkAssign(bare.strVal, mkTableSet(mkVar(bare.strVal), mkVar(kSynth),
                                           mkVar(vName)))
        else:
          dottedFieldMutate(bare, doTabSet, @[mkVar(kSynth), mkVar(vName)],
                            wbPre, ctx)
      if wbPre.len == 0: st else: mkBlock(wbPre & @[st])
    body = mutViewWriteBack(body, vName, writeBack)
  case iterName
  of "mpairs", "mvalues": discard
  of "keys": loopStmts.add mkLet(vars[0].strVal, keyTy, mkVar(kSynth))
  of "values": loopStmts.add mkLet(vars[0].strVal, valTy, vIR)
  else:
    if vars.len == 2:
      loopStmts.add mkLet(vars[0].strVal, keyTy, mkVar(kSynth))
      loopStmts.add mkLet(vars[1].strVal, valTy, vIR)
    else:
      let tupTy = classifyType(vars[0]).ty
      loopStmts.add mkLet(vars[0].strVal, tupTy,
                          mkTupleLit(@[mkVar(kSynth), vIR], tupTy))
  loopStmts.add body
  if live:
    var inner2: seq[IRStmt]
    let lenNow = mkSeqLen(parseExpr(container, inner2, ctx))
    loopStmts.add inner2
    # RFC-0005 S8bl (item 4): the iterator's `assert(len(t) == L)` after
    # each yield. With assertions on (they are, unless `--assertions:off`
    # or `-d:danger`) it raises `AssertionDefect` there, which is modelled;
    # with them off Nim walks the changed table's slots, an order this does
    # not model, and the path declines as S8bc's did.
    let lenChanged =
      when compileOption("assertions"): mkRaise("AssertionDefect", nil)
      else:
        ctx.declineAtSite(feUnsupportedOp,
          siteMsg(n, "the Table's length changed while iterating over it " &
                  "with assertions off: the iteration over the changed " &
                  "table is not modelled -- path degraded to sxUnknown"),
          "the Table's length changed while iterating over it")
    loopStmts.add mkIf(@[mkBranch(mkBinop(bNe, lenNow, mkVar(lenName)),
                                  lenChanged)])
  loopStmts.add mkAssign(ivName, mkBinop(bAdd, mkVar(ivName), mkIntLit(1)))
  pre.add mkWhile(mkBinop(bLt, mkVar(ivName), mkVar(lenName)),
                  mkBlock(loopStmts))
  mkBlock(pre)

proc insertArgs(elemTy: IRType; args: seq[IRExpr];
                preamble: var seq[IRStmt]; ctx: ParseCtx): seq[IRExpr] =
  ## RFC-0005 S8ar. `insert(x, item, i)`'s two arguments bound to fresh
  ## locals, in Nim's order (item, then i). `insert` lowers in two phases
  ## (`IRExpr.insGrow`), each of which reads both arguments; an argument
  ## that reads the seq itself (`s.insert(v, s.len)`) must see the seq
  ## as it was at the call, not as the grow phase left it. The index local
  ## takes an Int proto (`lIsIntOffsetLocal`), the representation `del`'s
  ## index lowers to.
  let tv = freshSynth(ctx, "insv")
  let ti = freshSynth(ctx, "insi")
  preamble.add mkLet(tv, elemTy, args[0])
  preamble.add mkLet(ti, tInt(), args[1], isIntOffsetLocal = true)
  @[mkVar(tv), mkVar(ti)]

proc dottedOpExpr(op: DottedOp; old: IRExpr; args: seq[IRExpr]): IRExpr =
  ## RFC-0005 S8ap. The new value of the field: `op` over its old value and
  ## the already-parsed arguments, exactly as the bare-symbol arm builds it
  ## over `mkVar(recvName)`.
  case op
  of doSeqAdd:    mkSeqAdd(old, args[0])
  of doSeqDel:    mkSeqDel(old, args[0])
  of doSeqInsert: mkSeqInsert(old, args[0], args[1])
  of doSeqInsertGrow: mkSeqInsert(old, args[0], args[1], grow = true)
  of doTabDel:    mkTableDel(old, args[0])
  of doTabSet:    mkTableSet(old, args[0], args[1])
  of doSetIncl:   mkSetIncl(old, args[0])
  of doSetExcl:   mkSetExcl(old, args[0])
  of doStrConcat: mkStrOp(iekStrConcat, "&", @[old, args[0]])
  of doStrUnsupported:
    mkStrOp(iekStrUnsupported, "string add (non-string arg)", @[old] & args)
  of doStrIndexAssign:
    # `s[i] = c` on a string: Phase 15 S11's immutable-string decline
    # (`seUnsupportedStringOp`), the bare arm's own IR.
    mkStrOp(iekStrUnsupported, "string mutation", @[old] & args)

proc dottedRefField(fieldNode: NimNode; operand: var NimNode;
                    fieldName: var string): bool =
  ## RFC-0005 S8ap. True iff `fieldNode` is a ref/ptr object's field
  ## (`p.s`): `operand` is then the ref/ptr expression and `fieldName` the
  ## field. Shared by `dottedFieldMutate` and `dottedFieldIndexAssign`.
  let lhsFW = if fieldNode.kind == nnkCheckedFieldExpr and fieldNode.len >= 1:
                fieldNode[0]
              else: fieldNode
  if lhsFW.kind == nnkDotExpr and lhsFW.len == 2 and
     lhsFW[0].kind in {nnkHiddenDeref, nnkDerefExpr} and lhsFW[0].len >= 1 and
     classifyType(lhsFW[0][0]).ty.kind in {itRef, itPtr}:
    operand = lhsFW[0][0]
    fieldName = lhsFW[1].strVal
    return true
  false

proc dottedFieldMutate(fieldNode: NimNode, op: DottedOp, args: seq[IRExpr],
                       preamble: var seq[IRStmt], ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8ao (S8aj's remainder) for `add`; S8ap for every #145
  ## mutation (was `dottedFieldAdd`). `<fieldPath>.<mutation>(<args>)`
  ## where `fieldPath` (`o.s`, `a.b.s`, a ref/ptr object's `p.s`) has the
  ## mutation's receiver type -- precondition: `dottedFieldShape(fieldNode)`
  ## already holds and `args` are parsed (S8ao's order: arguments first).
  ## A Nim mutation of a field is "read the field, mutate the value, write
  ## the field back", not a new mutation PRIMITIVE, so this reuses whichever
  ## field-write machinery the plain assignment `<fieldPath> = v` already
  ## uses for the SAME lvalue shape: the R6 ref-object field-deref-write
  ## (`mkFieldDeref`/`mkFieldDerefWrite`, mirroring `parseAsgn`'s own R6 arm,
  ## just reading the field first instead of discarding it) for a `ref`/
  ## `ptr` step, or S8p's value-field rebuild (`valueFieldWrite`) for a value
  ## tuple/object step. The mutated value is the bare-symbol arm's own IR
  ## (`dottedOpExpr`), so each mutation's semantics -- `del`'s
  ## `IndexDefect`/`RangeDefect` forks (`seqOobConds`, drained by the write
  ## that lowers it), `insert`'s classified lowering decline -- are the bare
  ## variable's. The field READ this performs to get the OLD value also
  ## forks any variant-arm discriminant check (`valueFieldChecked`'s own
  ## reason for existing) and the nil deref of a ref path for free.
  var operand: NimNode
  var fieldName: string
  if dottedRefField(fieldNode, operand, fieldName):
    let opCls = classifyType(operand)
    let isPtr = opCls.ty.kind == itPtr
    let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
    let fieldTy = classifyType(fieldNode).ty
    let ptrIR = parseExpr(operand, preamble, ctx)
    let synth = freshSynth(ctx, "fderef")
    preamble.add mkFieldDeref(synth, ptrIR, fieldTy, pointeeTy, fieldName, isPtr)
    return mkFieldDerefWrite(ptrIR, dottedOpExpr(op, mkVar(synth), args),
                             fieldTy, pointeeTy, fieldName, isPtr)
  let oldVal = parseExpr(fieldNode, preamble, ctx)
  let fw = valueFieldWrite(fieldNode, dottedOpExpr(op, oldVal, args),
                           preamble, ctx)
  fw.toStmt

proc dottedFieldIndexAssign(n, fieldNode, idxNode: NimNode, rhs: IRExpr,
                            rhsNode: NimNode,
                            preamble: var seq[IRStmt], ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8ap. `<fieldPath>[i] = v` on a seq field (`o.s[i] = v`,
  ## `p.s[i] = v`) -- precondition: `dottedFieldShape(fieldNode)` holds and
  ## the field is a seq. It was "unsupported nnkAsgn shape": the bare arm
  ## (`xs[i] = v`, N14's `isIndexAssign`) needs an env slot to store into,
  ## and a field has none. The field is read into a fresh slot (the
  ## ref-path field deref, or a `let` of the value-path read), the bare
  ## arm's `isIndexAssign` stores the element there -- forking its
  ## `IndexDefect` exactly as for a variable -- and the slot is written
  ## back through the same field-write primitive as `dottedFieldMutate`.
  ## Order: field, index, value, then the bounds check (the bare arm's).
  ## `rhs` is the already-lowered right-hand side when not nil (a var-arg
  ## write-back, `parseAsgn`'s `rhsOverride`); otherwise `rhsNode` is parsed.
  template value(): IRExpr =
    (if rhs != nil: rhs else: parseExpr(rhsNode, preamble, ctx))
  let fieldTy = classifyType(fieldNode).ty
  var operand: NimNode
  var fieldName: string
  if dottedRefField(fieldNode, operand, fieldName):
    let opCls = classifyType(operand)
    let isPtr = opCls.ty.kind == itPtr
    let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
    let ptrIR = parseExpr(operand, preamble, ctx)
    let synth = freshSynth(ctx, "fderef")
    preamble.add mkFieldDeref(synth, ptrIR, fieldTy, pointeeTy, fieldName, isPtr)
    let idxIR = parseExpr(idxNode, preamble, ctx)
    let valIR = value()
    preamble.add mkIndexAssignStmt(synth, idxIR, valIR, siteLoc(n))
    return mkFieldDerefWrite(ptrIR, mkVar(synth), fieldTy, pointeeTy,
                             fieldName, isPtr)
  let tmp = freshSynth(ctx, "fidx")
  let fieldIR = parseExpr(fieldNode, preamble, ctx)   ## RFC-0005 S8ax: first
  preamble.add mkLet(tmp, fieldTy, fieldIR)
  let idxIR = parseExpr(idxNode, preamble, ctx)
  let valIR = value()
  preamble.add mkIndexAssignStmt(tmp, idxIR, valIR, siteLoc(n))
  let fw = valueFieldWrite(fieldNode, mkVar(tmp), preamble, ctx)
  fw.toStmt

proc parseAsgn(n: NimNode, rhsOverride: IRExpr,
               preamble: var seq[IRStmt], ctx: ParseCtx): IRStmt =
  ## The `nnkAsgn` statement (`lhs = rhs`), split out of `parseStmtInner`
  ## by RFC-0005 S8ac so the var-argument write-back (`userCallStmt`) lowers
  ## `<lvalue> = <the callee's final formal>` through the SAME lvalue arms a
  ## source assignment takes. `rhsOverride`, when not nil, is the already
  ## lowered right-hand side and `n[1]` is not read (except to rule out the
  ## `new T` and discriminator-reassign shapes, which a write-back never
  ## is).
  template asgnRhs(): IRExpr =
    (if rhsOverride != nil: rhsOverride else: parseExpr(n[1], preamble, ctx))
  # RFC-0005 S8bc (item 7): `t.mgetOrPut(k, d) = v`. Nim runs the call (the
  # insert of an absent key, with `d` evaluated) before the right-hand side,
  # then stores through the reference: the call's read is parsed for its
  # effect and the store is `t[k] = v`.
  if mgetOrPutCall(n[0]) != nil:
    discard parseExpr(n[0], preamble, ctx)
    return parseAsgn(nnkAsgn.newTree(elemLvalueBracket(n[0]), n[1]),
                     rhsOverride, preamble, ctx)
  # Shapes after semcheck (some forms get re-wrapped):
  #   * `name = expr`                 — simple env reassignment
  #   * `t[k] = v`                    — Table set
  # Var receivers may carry HiddenDeref/HiddenAddr — unwrap (unwrapHidden).
  # Phase 15 R8b (ADR-0010). `p = new T` REBIND of a `var ref T` / `var ptr T`
  # parameter. Because the param is a `var`, the typed LHS is a compiler-
  # inserted `nnkHiddenDeref(sym)` (the lvalue indirection) — NOT an explicit
  # `nnkDerefExpr` (which is the `p[] = v` heap-write shape). So `p = new int`
  # presents as `Asgn[HiddenDeref[Sym p], Command[new, int]]`, whereas
  # `p[] = v` is `Asgn[DerefExpr[HiddenDeref[Sym p]], v]`. Distinguish on the
  # bare `nnkHiddenDeref` (var-ness) + a `new T` RHS: this is a VARIABLE rebind
  # to a freshly allocated cell, lowered to `isNew` under the var name (the R2
  # `freshRef` mints a new `Ref_T` const), NOT a heap store at the old address.
  # The fresh binding flows back to the caller via the #140 `isVar` write-back
  # (R8b extends it to svRef/svPtr in the walker's `isCall` return arm). Checked
  # BEFORE the `nnkDerefExpr|nnkHiddenDeref` deref-write arm (which would treat
  # this as `p[] = new int` and `parseExpr` the unsupported `new` command).
  if n[0].kind == nnkHiddenDeref and n[0].len == 1 and
     n[0][0].kind == nnkSym and (rhsOverride == nil and isNewCall(n[1])):
    let sym = n[0][0]
    let symCls = classifyType(sym)
    if symCls.ty.kind in {itRef, itPtr}:
      return mkNewT(sym.strVal, symCls.ty)
  # Phase 15 R3 (ADR-0010). `p[] = v` — a heap WRITE through a ref/ptr deref.
  # The LHS is an explicit `nnkDerefExpr` (or a compiler-inserted
  # `nnkHiddenDeref`) whose operand classifies as a genuine `ref T`/`ptr T`.
  # Lower it to an `isDerefWrite` stmt (the walker no-ops it at R3; the real
  # `store` lands R4). This MUST be checked BEFORE `unwrap` (which strips a
  # hidden deref down to the pointee and would lose the indirection). A
  # hidden-deref over a NON-ref operand keeps the pre-R unwrap path below.
  # RFC-0005 S8ac: `cur = b` on `cur: var ref T` is
  # `Asgn[HiddenDeref[Sym cur], b]`: a REBIND of the caller's variable
  # (the #140 `isVar` write-back carries it out), not a store into the
  # cell `cur` points at. It takes the plain `name = expr` arm below.
  if n[0].kind in {nnkDerefExpr, nnkHiddenDeref} and n[0].len >= 1 and
     not isVarIndirection(n[0]):
    # Phase 15 R8b: a `var ref T` param's `p[] = v` is
    # `Asgn[DerefExpr[HiddenDeref[Sym p]], v]` — the inner `HiddenDeref` is the
    # `var`-ness lvalue indirection, which `classifyType` unwraps to the
    # pointee (defeating the itRef detection). Strip that ONE var-level
    # hidden-deref so the operand is the ref/ptr symbol (matching the deref-READ
    # arm). For a plain `ref T` param `p[] = v` is `Asgn[DerefExpr[Sym p], v]`
    # (no inner HiddenDeref) and this strip is a no-op.
    var operand = n[0][0]
    if operand.kind == nnkHiddenDeref and operand.len == 1 and
       classifyType(operand[0]).ty.kind in {itRef, itPtr}:
      operand = operand[0]
    let opCls = classifyType(operand)
    if opCls.ty.kind in {itRef, itPtr}:
      let isPtr = opCls.ty.kind == itPtr
      let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
      let ptrIR = parseExpr(operand, preamble, ctx)
      let valIR = asgnRhs()
      # RFC-0005 S8bn (item 6): a whole-object store replaces its proc
      # fields with values this model names no candidate for (-1).
      var pfWrites: seq[IRStmt]
      if pointeeTy.kind == itTuple:
        for i, fname in pointeeTy.fieldNames:
          if isClosureFieldTy(pointeeTy.fields[i]):
            pfWrites.add mkFieldDerefWrite(ptrIR, mkIntLit(-1),
              tInt(64, signed = true), pointeeTy, "@pf_" & fname, isPtr)
      if wholeObjectPointee(pointeeTy):
        # RFC-0005 S8ar: `p[] = v` of an object writes each field's own heap
        # (the read side's reason, `parseExpr`'s deref arm).
        let tmp = freshSynth(ctx, "dw")
        preamble.add mkLet(tmp, pointeeTy, valIR)
        let last = pointeeTy.fields.len - 1
        for i in 0 ..< last:
          preamble.add mkFieldDerefWrite(ptrIR,
            mkField(mkVar(tmp), i, pointeeTy.fieldNames[i]), pointeeTy.fields[i],
            pointeeTy, pointeeTy.fieldNames[i], isPtr)
        let lastWrite = mkFieldDerefWrite(ptrIR,
          mkField(mkVar(tmp), last, pointeeTy.fieldNames[last]),
          pointeeTy.fields[last], pointeeTy, pointeeTy.fieldNames[last], isPtr)
        if pfWrites.len > 0: return mkBlock(@[lastWrite] & pfWrites)
        return lastWrite
      if pfWrites.len > 0:
        return mkBlock(@[mkDerefWrite(ptrIR, valIR, pointeeTy, isPtr)] & pfWrites)
      return mkDerefWrite(ptrIR, valIR, pointeeTy, isPtr)
  # Phase 15 R6 (ADR-0010) + ADR-0013 S3. `p.field = v` — a FIELD WRITE through
  # a `ref object` / `ptr object`. LHS is `nnkDotExpr(nnkHiddenDeref(p), field)`,
  # OR — for a variant ARM field — semcheck wraps that dot-expr in a
  # `nnkCheckedFieldExpr(<dotExpr>, <disc check call>)` (the runtime
  # discriminant guard). Unwrap to the inner dot-expr — the runtime check is
  # modeled symbolically by the walker's arm-field FieldDefect fork (ADR-0013
  # D3), exactly as the READ side does (`of nnkCheckedFieldExpr: parseExpr(n[0])`).
  # Lower to a field-split `isDerefWrite` (`store(heap_<objTid>__<field>, p, v)`
  # — only that field's array changes; an aliased read of the same field sees
  # the write). Checked BEFORE `unwrap` (which would strip the indirection).
  let lhsFW = if n[0].kind == nnkCheckedFieldExpr and n[0].len >= 1: n[0][0]
              else: n[0]
  if lhsFW.kind == nnkDotExpr and lhsFW.len == 2 and
     lhsFW[0].kind in {nnkHiddenDeref, nnkDerefExpr} and lhsFW[0].len >= 1:
    let operand = lhsFW[0][0]
    let opCls = classifyType(operand)
    if opCls.ty.kind in {itRef, itPtr}:
      let isPtr = opCls.ty.kind == itPtr
      let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
      if pointeeTy.kind in {itTuple, itVariant, itMultiVariant}:
        let fieldName = lhsFW[1].strVal
        let fieldTy   = classifyType(lhsFW).ty   ## the field's type
        let ptrIR = parseExpr(operand, preamble, ctx)
        if pointeeTy.kind == itTuple and isClosureFieldTy(fieldTy):
          # RFC-0005 S8bn (item 6): a heap proc field holds its shadow code
          # (`procFieldCallIR`); a value no assignment names is evaluated
          # for its effects and stored as -1 (no candidate).
          let code = pfCode(pfObjKey(lhsFW[0]) & "." & fieldName, n[1])
          if code == -1:
            preamble.add mkLet(freshSynth(ctx, "procFieldRhs"), fieldTy,
                               asgnRhs())
          return mkFieldDerefWrite(ptrIR, mkIntLit(code),
                                   tInt(64, signed = true), pointeeTy,
                                   "@pf_" & fieldName, isPtr)
        let valIR = asgnRhs()
        return mkFieldDerefWrite(ptrIR, valIR, fieldTy, pointeeTy,
                                 fieldName, isPtr)
  let lhs = unwrapHidden(n[0])
  if lhs.kind == nnkBracketExpr and lhs.len == 2 and
     lhs[0].kind in {nnkDerefExpr, nnkHiddenDeref} and lhs[0].len == 1 and
     not isVarIndirection(lhs[0]):
    # RFC-0005 S8bu: `p[][i] = v`, an element of a seq written through a
    # `ref`/`ptr` to the whole seq (`gps = addr s`). It was the
    # "unsupported nnkAsgn shape" decline. The pointer is read once, the
    # seq read through it, the element checked before the value is
    # evaluated (as `s[i] = v`), written (`isIndexAssign`, its IndexDefect
    # fork), and the seq stored back: an in-place write of the cell, which
    # a by-value copy sharing its memory sees (`syncAddrCells`' `view`).
    var operand = lhs[0][0]
    if operand.kind == nnkHiddenDeref and operand.len == 1 and
       classifyType(operand[0]).ty.kind in {itRef, itPtr}:
      operand = operand[0]
    let opCls = classifyType(operand)
    if opCls.ty.kind in {itRef, itPtr}:
      let isPtr = opCls.ty.kind == itPtr
      let pointeeTy = if isPtr: opCls.ty.ptrPointeeTy else: opCls.ty.refPointeeTy
      if pointeeTy.kind == itSeq:
        let pt = freshSynth(ctx, "dixPtr")
        preamble.add mkLet(pt, opCls.ty, parseExpr(operand, preamble, ctx))
        let tmp = freshSynth(ctx, "dixSeq")
        preamble.add(if isPtr: mkPtrDeref(tmp, mkVar(pt), pointeeTy)
                     else: mkDeref(tmp, mkVar(pt), pointeeTy))
        let idxIR = parseExpr(lhs[1], preamble, ctx)
        preamble.add mkIndexStmt(freshSynth(ctx, "awck"), mkVar(tmp), idxIR,
                                 pointeeTy.seqElemTy, siteLoc(n))
        let valIR = asgnRhs()
        preamble.add mkIndexAssignStmt(tmp, idxIR, valIR, siteLoc(n))
        return mkDerefWrite(mkVar(pt), mkVar(tmp), pointeeTy, isPtr)
  if lhs.kind == nnkBracketExpr and lhs.len == 2:
    let recv = unwrapHidden(lhs[0])
    if recv.kind == nnkSym:
      let recvCls = classifyType(recv)
      if recvCls.ty.kind == itTable:
        let key = parseExpr(lhs[1], preamble, ctx)
        let val = asgnRhs()
        return mkAssign(recv.strVal,
          mkTableSet(mkVar(recv.strVal), key, val))
      # Phase 15 S11: `s[i] = c` — string index ASSIGNMENT on an `itString`
      # receiver. Z3 String theory strings are IMMUTABLE (ADR-0006), so this
      # mutation has no sound symbolic encoding and is honestly classified
      # `seUnsupportedStringOp` → `sxUnknown` (Invariant 3 — never a silent
      # UNSAT, never a crash). The reason is immutability, NOT a byte/codepoint
      # mismatch (the model is byte-faithful). Reuse the S9/S3 idiom: bind the
      # receiver to an `iekStrUnsupported` op (carrying the surface op name);
      # the residual `lower` arm raises `SymexUnsupportedStringOpError`, which
      # the `runSymex` boundary maps to `seUnsupportedStringOp`.
      if recvCls.ty.kind == itString:
        let recvIR = mkVar(recv.strVal)
        let idxIR  = parseExpr(lhs[1], preamble, ctx)
        let valIR  = asgnRhs()
        return mkAssign(recv.strVal,
          mkStrOp(iekStrUnsupported, "string mutation",
                  @[recvIR, idxIR, valIR]))
      # N14 (RFC-chapulin-hardening bucket-2): `xs[i] = v` element
      # ASSIGNMENT on a seq[T] receiver. Unlike the `itTable`/`itString`
      # siblings above, this needs a REAL bounds-defect fork (Nim raises
      # `IndexDefect` on an OOB write, exactly like a read) — the fork
      # machinery (`forkDefect`) only exists at WALK time inside the
      # statement dispatch, so this is its own A-normalised statement kind
      # (`isIndexAssign`, mirrors `isIndex`'s own read-side fork), not an
      # `iekXxx` expression evaluated inside the exception-free `lower()`.
      if recvCls.ty.kind == itSeq:
        # RFC-0005 S8am (S8z's remainder, item 2): Nim checks the index
        # BEFORE it evaluates the assigned value (probed against real Nim:
        # `s[5] = raiser()` raises `IndexDefect`, never `raiser`'s
        # exception) -- the array write arm already had this order
        # (`valueFieldChecked`'s discarded read), but a bare seq element
        # assignment did not: the RHS was parsed (and any call it makes
        # hoisted into the preamble) before the `isIndexAssign` statement's
        # own bounds check, which only runs at WALK time. Force the check
        # here, as a discarded `isIndex` read reusing the SAME parsed
        # `idxIR` (never a second parse of the raw index node, which would
        # double-evaluate an impure index), emitted before the RHS is
        # parsed.
        let idxIR = parseExpr(lhs[1], preamble, ctx)
        let checkSynth = freshSynth(ctx, boundsCheckSynthWord)
        preamble.add mkIndexStmt(checkSynth, mkVar(recv.strVal), idxIR,
                                 recvCls.ty.seqElemTy, siteLoc(n))
        let valIR = asgnRhs()
        return mkIndexAssignStmt(recv.strVal, idxIR, valIR, siteLoc(n))
    # RFC-0005 S8ap (S8ao's remainder): an element assignment on a DOTTED
    # field (`o.s[i] = v`, `a.b.s[i] = v`, a ref/ptr object's `p.s[i] = v`)
    # was the "unsupported nnkAsgn shape" decline below. It now takes the
    # same field-write primitive as the dotted mutations (`dottedFieldShape`
    # / `dottedFieldMutate`, above): a seq field through N14's own
    # `isIndexAssign` on a fresh slot holding the field (its IndexDefect
    # fork included) and then written back; a Table field through
    # `mkTableSet` and a string field through S11's `iekStrUnsupported`,
    # exactly the bare arms above.
    elif dottedFieldShape(recv):
      let fk = classifyType(recv).ty.kind
      if fk == itSeq:
        return dottedFieldIndexAssign(n, recv, lhs[1], rhsOverride, n[1],
                                      preamble, ctx)
      if fk in {itTable, itString}:
        let idxIR = parseExpr(lhs[1], preamble, ctx)
        let valIR = asgnRhs()
        return dottedFieldMutate(recv,
          (if fk == itTable: doTabSet else: doStrIndexAssign),
          @[idxIR, valIR], preamble, ctx)
  if lhs.kind == nnkSym:
    let nm = lhs.strVal
    # Phase 15 R8b (ADR-0010): a `new T` RHS REBINDS the var to a freshly
    # allocated cell (`p = new int`). Lower it to an `isNew` stmt under the
    # LHS name — `freshRef` mints a fresh `Ref_T` const and binds it for `nm`,
    # exactly as the let-section `new T` arm does (R2). The classified type
    # comes from the LHS sym (a `var ref T` param classifies to `itRef`, the
    # `var` stripped). Without this the assign would `parseExpr(new int)` and
    # halt on the unsupported `nnkCommand`. The fresh binding flows back to the
    # caller via the #140 `isVar` write-back (R8b extends it to svRef/svPtr).
    if (rhsOverride == nil and isNewCall(n[1])):
      let classified = classifyType(lhs)
      if classified.ty.kind in {itRef, itPtr}:
        return mkNewT(nm, classified.ty)
    let val = asgnRhs()
    # #163 review R27: resolve the target's declared range type by TRUE
    # SYMBOL IDENTITY (`classifyType(lhs)`, `lhs` being the real `nnkSym`
    # this assignment targets — not its printed name) so the walker's
    # RangeDefect fork (`forkAssignRangeCheck`) can find it without the
    # unscoped, name-keyed `WalkCtx` table R22 used to route through.
    # RFC-0005 S8j: nil too when `val` is itself the range-checked
    # conversion into the target's bounds (S8i: the hidden conversion Nim
    # puts on `q = x`, or an explicit `q = R(x)`) -- one check, as Nim
    # makes, not the conversion's and then this site's.
    let assignCls = classifyType(lhs)
    let assignTy = if assignCls.ty.kind == itInt and assignCls.ty.hasRange and
                      not carriesRangeCheck(val, assignCls.ty):
                     assignCls.ty
                   else: nil
    return mkAssign(nm, val, assignTy)
  # Phase 11 cycle 6: `obj.kind = tagLiteral` — discriminator
  # reassignment. Requires (a) the object to be a Sym in env,
  # (b) the field to be the variant's discriminator name, and
  # (c) the RHS to resolve to a static enum constant of the
  # discriminator's enum. Symbolic RHS is a future cycle.
  if lhs.kind == nnkDotExpr and lhs.len == 2 and rhsOverride == nil:
    let recv = unwrapHidden(lhs[0])
    let fieldNode = lhs[1]
    # RFC-0005 S8at: the receiver may be a field chain (`o.v.kind = k`, a
    # ref object's by-value case object `p.bv.kind = k`): the reassignment
    # runs on a copy of the field, which is then written back
    # (`writeBackField`), as any value-field write is. It was the
    # "unsupported nnkAsgn shape" decline.
    var chainOp: NimNode
    var chainField: string
    let chainRecv = recv.kind != nnkSym and fieldNode.kind in {nnkIdent, nnkSym} and
      classifyType(recv).ty.kind in {itVariant, itMultiVariant} and
      (valueFieldTy(recv) != nil or heapFieldRoot(recv, chainOp, chainField))
    if (recv.kind == nnkSym or chainRecv) and fieldNode.kind in {nnkIdent, nnkSym}:
      let recvCls = classifyType(recv)
      if chainRecv:
        var isDiscName = recvCls.ty.kind == itVariant and
                         fieldNode.strVal == recvCls.ty.vDiscName
        if recvCls.ty.kind == itMultiVariant:
          for ax in recvCls.ty.mvAxes:
            if ax.discName == fieldNode.strVal: isDiscName = true
        if isDiscName:
          let tmp = freshSynth(ctx, "dr")
          preamble.add mkLet(tmp, recvCls.ty, parseExpr(recv, preamble, ctx))
          preamble.add discReassignStmt(tmp, recvCls.ty, fieldNode.strVal, n[1],
                                        preamble, ctx)
          return writeBackField(recv, mkVar(tmp), preamble, ctx)
      # Phase 11 + Phase 14 A4. Three cases:
      #   1. itVariant disc reassign with a static enum-constant RHS
      #      → mkVariantReassign (Phase 11 cycle 6 path).
      #   2. itVariant disc reassign with a symbolic RHS → A4's
      #      mkVariantReassignSymbolic (walker forks).
      #   3. itMultiVariant axis-disc reassign → same A4 IR with
      #      vrsDiscName = axis name. Static-tag path on multi-
      #      variant is a future cycle.
      if recvCls.ty.kind == itVariant and
         fieldNode.strVal == recvCls.ty.vDiscName:
        let rhs = unwrapHidden(n[1])
        # Try the static-tag path first.
        let tagIR = discTagLit(parseExpr(rhs, preamble, ctx))
        if tagIR.kind == iekIntLit:
          var tagName = if rhs.kind == nnkSym: rhs.strVal else: ""
          for arm in recvCls.ty.vArms:
            if arm.tagOrdinal == int(tagIR.ival):
              tagName = arm.tagName; break
          return mkVariantReassign(recv.strVal, int(tagIR.ival), tagName,
                                   branchGroups(recvCls.ty.vArms))
        # Symbolic RHS: A4 fork path.
        return mkVariantReassignSymbolic(recv.strVal, "", tagIR,
                                         branchGroups(recvCls.ty.vArms))
      if recvCls.ty.kind == itMultiVariant:
        # Identify which axis owns `fieldNode.strVal` as discName.
        for ax in recvCls.ty.mvAxes:
          if ax.discName == fieldNode.strVal:
            let rhs = unwrapHidden(n[1])
            let tagIR = parseExpr(rhs, preamble, ctx)
            # Multi-axis disc reassign — static or symbolic, both
            # go through the A4 symbolic IR for now (no Phase 11
            # static path was ever implemented for multi-axis).
            return mkVariantReassignSymbolic(
              recv.strVal, ax.discName, tagIR, branchGroups(ax.arms))
  # RFC-0005 S8p: `o.a = v` on a value tuple / object (see
  # `valueFieldWrite`). A ranged int field keeps the decline unless `v` is
  # itself the range-checked conversion: the rebuilt root assignment has no
  # per-field RangeDefect fork.
  let fieldTy = valueFieldTy(lhs)
  if fieldTy != nil:
    # RFC-0005 S8s: a write through a variant arm field checks the
    # discriminant first -- Nim computes the field's address, raising
    # `FieldDefect` out of the arm, before it evaluates the value. The
    # read of `lhs` is that check (its `isVariantField` fork).
    if valueFieldChecked(lhs):
      let checkRead = parseExpr(lhs, preamble, ctx)
      # RFC-0005 S8bw (item 2): the read only checks the index; its value
      # is never used (`ixCheckOnly`).
      if checkRead.kind == iekVar:
        for st in preamble:
          if st.kind == isIndex and st.ixRetName == checkRead.vname:
            st.ixCheckOnly = true
    let val = asgnRhs()
    if not (fieldTy.kind == itInt and fieldTy.hasRange and
            not carriesRangeCheck(val, fieldTy)):
      let fw = valueFieldWrite(lhs, val, preamble, ctx)
      return fw.toStmt
  ctx.declineMarker(feUnsupportedStmtKind, &"unsupported nnkAsgn shape: {n.repr}")

proc yieldedElement(n: NimNode): NimNode =
  ## RFC-0005 S8bu. The typed element `a[i]` an instantiated `mitems` /
  ## `mpairs` yields by address (`yield a[i]`, `yield (i, a[i])`); nil when
  ## the body has no such yield.
  if n.kind == nnkYieldStmt and n.len == 1:
    var e = n[0]
    while e.kind in {nnkHiddenSubConv, nnkHiddenStdConv} and e.len == 2:
      e = e[1]
    if e.kind in {nnkTupleConstr, nnkPar} and e.len == 2: e = e[1]
    if e.kind == nnkHiddenAddr and e.len == 1: e = e[0]
    if e.kind == nnkBracketExpr and e.len == 2 and e[1].kind == nnkSym:
      return e
    return nil
  for c in n:
    let r = yieldedElement(c)
    if r != nil: return r
  nil

proc parseMutIter(n, iterExpr, bodyNode: NimNode; ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bu. `for x in mitems(c)` / `for i, x in mpairs(c)` over a
  ## seq or an array. Nim yields each element by address (`var T`), and its
  ## inline expansion makes the body's `x` that element: `x` is spelled
  ## `c[k]` in the body (`substByRefBody`, as an iterator's `var` formal is),
  ## `k` the iteration's position (a marked copy of the iterator's own
  ## counter, `markByRef`, so the element node keeps its type). A write
  ## through `x`, through another name for the element (`addr c[k]` taken
  ## before the loop), and a read of `c` in the body are all one location.
  ## `c` is a location (`iterArgPath`); its indices are read once, when the
  ## loop starts. A seq is walked as Nim's `while k < L` with `L` its length
  ## when the loop starts; a length that changed by the end of an iteration
  ## (Nim's `assert`) is declined on its paths. An array is unrolled. Before,
  ## the stdlib body was inlined and declined at `unCheckedInc`'s pragma (a
  ## seq) or at `low(IX)` (an array).
  let isPairs = iterExpr[0].strVal == "mpairs"
  if (isPairs and n.len != 4) or (not isPairs and n.len != 3):
    return ctx.declineMarker(feUnsupportedStmtKind,
      &"for-loop over `{iterExpr[0].strVal}` with {n.len - 2} loop " &
      "variable(s): only `for x in mitems(c)` and `for i, x in mpairs(c)` " &
      "are modelled")
  var c = iterExpr[1]
  if c.kind == nnkHiddenAddr and c.len == 1: c = c[0]
  c = openArraySource(c)
  let cls = classifyType(c).ty
  var impl: NimNode = nil
  if iterExpr[0].kind == nnkSym:
    impl = iterExpr[0].getImpl
  let ybr = if impl != nil and impl.kind == nnkIteratorDef: yieldedElement(body(impl))
            else: nil
  var hasIx = false
  if cls.kind notin {itSeq, itArray} or ybr == nil or
     not iterArgPath(c, hasIx):
    return ctx.declineMarker(feUnsupportedStmtKind,
      &"RFC-0005 S8bu: `{iterExpr[0].strVal}` over `{c.repr}` (a " &
      &"{cls.kind}) is not modelled: the walk follows it over a seq or an " &
      "array location only")
  var pre: seq[IRStmt]
  var ok = true
  let fixed = if hasIx: hoistIterIndices(c, pre, ctx, ok) else: c
  let mark = markByRef(ybr[1])
  if not ok or mark.isNil:
    return ctx.declineMarker(feUnsupportedStmtKind,
      &"RFC-0005 S8bu: `{iterExpr[0].strVal}` over `{c.repr}`: an index of " &
      "the location has no name the walk can fix")
  let elem = copyNimNode(ybr)
  elem.add copyNimTree(stripFieldChecks(fixed))
  elem.add mark
  var sub = ByRefSub(isPtr: false, tail: elem)
  sub.addrNode = newNimNode(nnkHiddenAddr)
  sub.addrNode.add copyNimTree(elem)
  let xSym = n[n.len - 3]
  let body0 = substByRefBody(bodyNode, xSym, sub)
  let k = strVal(mark)
  let kTy = classifyType(ybr[1]).ty
  let (body, unrollBrk) = parseLoopBody(body0, ctx,
                                        unrolled = cls.kind == itArray)
  var stmts = pre
  if cls.kind == itArray:
    let lo = arrayIndexLow(c)
    var iters: seq[IRStmt]
    for q in 0 ..< cls.size:
      iters.add mkLet(k, kTy, mkIntLit(lo + int64(q)))
      if isPairs:
        iters.add mkLet(strVal(n[0]), classifyType(n[0]).ty, mkVar(k))
      iters.add body
    if unrollBrk.len > 0: stmts.add mkLabelledBlock(unrollBrk, iters)
    else: stmts.add iters
    return mkBlock(stmts)
  let seqIR = parseExpr(fixed, stmts, ctx)
  let lenName = freshSynth(ctx, "miLen")
  let intTy = tInt(64, signed = true)
  stmts.add mkLet(lenName, intTy, mkSeqLen(seqIR))
  let iv = freshSynth(ctx, "miIv")
  stmts.add mkLet(iv, intTy, mkIntLit(0))
  var loopStmts = @[mkLet(k, kTy, mkVar(iv))]
  if isPairs:
    loopStmts.add mkLet(strVal(n[0]), classifyType(n[0]).ty, mkVar(iv))
  loopStmts.add body
  loopStmts.add mkAssign(iv, mkBinop(bAdd, mkVar(iv), mkIntLit(1)))
  var lp: seq[IRStmt]
  let lenNow = mkSeqLen(parseExpr(fixed, lp, ctx))
  for st in lp: loopStmts.add st
  loopStmts.add mkIf(@[mkBranch(mkBinop(bNe, lenNow, mkVar(lenName)),
    ctx.declineAtSite(feUnsupportedOp,
      siteMsg(n, "RFC-0005 S8bu: the length of `" & c.repr & "` changed " &
              "during an iteration of `" & iterExpr[0].strVal & "`: Nim's " &
              "`assert` there, and the element it yielded by address, are " &
              "not modelled (feUnsupportedOp)"),
      "mitems over a seq whose length changed (feUnsupportedOp)"))])
  stmts.add mkWhile(mkBinop(bLt, mkVar(iv), mkVar(lenName)), mkBlock(loopStmts))
  mkBlock(stmts)

proc parseBorrowViewedStmt(rw: NimNode,
                           views: seq[tuple[node, baseTy: NimNode]],
                           preamble: var seq[IRStmt], ctx: ParseCtx): IRStmt =
  ## RFC-0005 S8bc (item 2). `parseBorrowViewedExpr`'s statement form.
  let mark = borrowBaseViews.len
  borrowBaseViews.add views
  result = parseStmtInner(rw, preamble, ctx)
  borrowBaseViews.setLen mark

proc parseStmtInner(n: NimNode,
                    preamble: var seq[IRStmt],
                    ctx: ParseCtx): IRStmt =
  ## The `preamble` accumulates A-normalised calls from any expression
  ## the surrounding statement contains; callers wrap the resulting
  ## stmt with the preamble before returning.
  # RFC-0005 S8bc (item 2): a statement-position borrowed routine call
  # (`inc(m)`, `d.add(3)`), as `parseExpr`'s.
  block borrowRoutine:
    let (rw, views) = borrowRoutineRewrite(n)
    if rw != nil: return parseBorrowViewedStmt(rw, views, preamble, ctx)
  # RFC-0005 S8bc (item 5): `newSeq(s, n)` is `s = newSeq[T](n)`. The length
  # is evaluated (and its guard forked) before `s` is written.
  if n.kind in {nnkCall, nnkCommand} and n.len == 3 and
     n[0].kind == nnkSym and n[0].strVal == "newSeq" and
     isStdlibDecl(n[0]) and classifyType(n[1]).ty.kind == itSeq:
    let target = unwrapHidden(n[1])
    return parseAsgn(nnkAsgn.newTree(target, newEmptyNode()),
      parseSeqNew("newSeq", n[2], classifyType(n[1]).ty, preamble, ctx),
      preamble, ctx)
  # RFC-0005 S8bl (item 1): the system magics with a `var` parameter.
  block:
    let vm = parseVarMagicStmt(n, preamble, ctx)
    if vm != nil: return vm
  case n.kind
  # Phase 15 E6. A raw `assert cond, msg` / `doAssert cond` lowers (after
  # semcheck) to gensym scaffolding (`const loc…`, `bind`, `mixin`) plus a
  # `PragmaBlock[Pragma, IfStmt[ElifBranch[not (cond), Call failedAssertImpl]]]`.
  # The scaffolding statements are not in the supported fragment and the
  # `failedAssertImpl` call would land `isUnsupported`; instead, recognise the
  # whole expansion and lower it to an implicit `AssertionDefect` raise guarded
  # by the assert-FAILS condition (`not cond`), so a reachable assert violation
  # surfaces as `sxRaised{isDefect: true}` rather than silently. This is the
  # raw-`assert` path; the `symexAssert(...)` MARKER (→ `mkAssert`/`isAssert`)
  # and its `tAssertionViolation` semantics are UNCHANGED.
  # CR-22 fix: the detection is SCOPED to the nnkPragmaBlock node that IS the
  # assert expansion — NOT applied greedily to any enclosing StmtList that
  # merely CONTAINS an assert.  Sibling statements (e.g. symexTarget labels)
  # are parsed normally in their original order by the StmtList arm below.
  of nnkPragmaBlock:
    let failsCond = findAssertFailsCond(n)
    if failsCond != nil:
      let condIR = parseExpr(failsCond, preamble, ctx)
      return mkIf(@[mkBranch(condIR, mkRaise("AssertionDefect", nil))])
    # Fallthrough: a PragmaBlock that is NOT an assert expansion — treat as
    # a transparent wrapper around its body (the last child).
    parseStmt(n[n.len - 1], ctx)
  of nnkStmtList, nnkStmtListExpr, nnkBlockStmt:
    let inner = if n.kind == nnkBlockStmt: n[1] else: n
    parseDeferList(stmtListItems(inner), 0, ctx)
  of nnkIfStmt, nnkIfExpr:
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    for arm in n:
      case arm.kind
      of nnkElifBranch, nnkElifExpr:
        # Each branch's condition gets its own preamble; we surface it
        # into the outer preamble so the call runs *before* the if.
        var condPreamble: seq[IRStmt]
        let condIR = parseExpr(arm[0], condPreamble, ctx)
        # The condition's preamble must run before the if for the
        # branch's then-body to see the bindings. For Phase 3 a
        # single if's preamble flows into the enclosing block.
        for cs in condPreamble: preamble.add cs
        branches.add mkBranch(condIR, parseStmt(arm[1], ctx))
      of nnkElse, nnkElseExpr:
        elseBody = parseStmt(arm[0], ctx)
      else:
        error(&"symex: unexpected if-arm kind {arm.kind}", arm)
    mkIf(branches, elseBody)
  of nnkAsgn:
    return parseAsgn(n, nil, preamble, ctx)
  of nnkWhileStmt:
    var preamble2: seq[IRStmt]
    # RFC-chapulin-hardening Q1 (ADR-0025) / B3 / B4 / B6 (ADR-0028): try the
    # bounded scan-idiom lifts BEFORE building the ordinary k-unrolled
    # `mkWhile` — see `tryRecognizeScanIdiom`'s, `tryRecognizeScanPairIdiom`'s,
    # `tryRecognizeAccumulatingScan`'s, and `tryRecognizePairLoopIdiom`'s doc
    # comments for the exact recognized shapes; first `some` wins (mutually
    # exclusive shapes by construction — Q1/B3/B4 by guard/body-statement-
    # count, B6 by its own distinct 5-statement pair-loop body, which none of
    # Q1/B3/B4 can match). B6 is wired ONLY at this top-level call site (its
    # own doc comment records why — chapulin's `readOptions` is always a
    # plain top-level loop, never for/iterator-nested).
    let scanLift = tryRecognizeScanIdiom(n, preamble2, ctx)
    let pairLift = if scanLift.isNone: tryRecognizeScanPairIdiom(n, preamble2, ctx)
                   else: none(IRStmt)
    let accLift = if scanLift.isNone and pairLift.isNone:
                    tryRecognizeAccumulatingScan(n, preamble2, ctx)
                  else: none(IRStmt)
    let pairLoopLift = if scanLift.isNone and pairLift.isNone and accLift.isNone:
                          tryRecognizePairLoopIdiom(n, preamble2, ctx)
                        else: none(IRStmt)
    if scanLift.isSome or pairLift.isSome or accLift.isSome or pairLoopLift.isSome:
      # Closed-form replacement for the whole loop (not a `while` at all) —
      # any preamble it needs (e.g. the hoisted `find` call) runs once,
      # exactly as before.
      let whileSt = if scanLift.isSome: scanLift.get
                    elif pairLift.isSome: pairLift.get
                    elif accLift.isSome: accLift.get
                    else: pairLoopLift.get
      if preamble2.len == 0:
        whileSt
      else:
        var both = preamble2
        both.add whileSt
        mkBlock(both)
    else:
      # `preamble2` is still empty here (tryRecognizeScanIdiom only appends
      # to it on the `some(...)` path above) and unused below — R14 routes
      # through the shared `mkShortCircuitWhile` helper — when the RAW guard
      # is a top-level `A and B` with the fault in `B`, it desugars to `while
      # A: <B's preamble>; if not B: break; body` so guard `A` (a real,
      # SAT-able loop guard) and B's preamble both re-run on every real
      # iteration — including after `continue`, by construction; otherwise it
      # emits the plain `mkWhile(cond, body)` fast path, or a sound
      # `mkUnsupported` degrade for the rare or-with-fault / nested-fault
      # shapes it cannot cleanly split. Identical helper used by the
      # `parseIterBodyStmt` for/iterator-body arm above.
      let body = parseStmt(n[1], ctx)
      mkShortCircuitWhile(n[0], n[1], body, ctx)
  of nnkCaseStmt:
    # Lower to if-elif chain: each `of label: body` becomes
    # `elif scrutinee == label: body`, with multiple labels chained via OR.
    var preamble3: seq[IRStmt]
    let scrutinee = parseExpr(n[0], preamble3, ctx)
    var branches: seq[IRBranch]
    var elseBody: IRStmt = nil
    for i in 1 ..< n.len:
      let arm = n[i]
      case arm.kind
      of nnkOfBranch:
        # arm[0..arm.len-2] = labels; arm[arm.len-1] = body
        var cond: IRExpr = nil
        var narrowTags: seq[int] = @[]
        var narrowOk = true
        for j in 0 ..< arm.len - 1:
          let labelIR = parseExpr(arm[j], preamble3, ctx)
          let eq = mkBinop(bEq, scrutinee, labelIR)
          if cond == nil: cond = eq
          else: cond = mkBinop(bOr, cond, eq)
          # Round-6 A3 (ADR-0029): mine this branch's LITERAL tag ordinals for
          # `ctx.procScoped.caseNarrow` — a label that doesn't parse to a plain int
          # literal (e.g. a `low..high` range label) makes this branch's
          # narrowing set unknowable, so it is simply not pushed (the
          # constructor's own fallback to the full declared arm count is
          # always sound, just less precise).
          let labelTag = discTagLit(labelIR)
          if labelTag.kind == iekIntLit: narrowTags.add int(labelTag.ival)
          else: narrowOk = false
        # Push BEFORE parsing the body so a variant constructor nested
        # anywhere inside it (not just at the top level) sees the narrowing;
        # pop immediately after so a SIBLING branch never inherits it.
        let pushNarrow = narrowOk and narrowTags.len > 0
        if pushNarrow:
          ctx.procScoped.caseNarrow.add (subjectRepr: scopedRepr(n[0]), tags: narrowTags)  ## RFC-0005 S8e: symbol-keyed
        let armBody = parseStmt(arm[arm.len - 1], ctx)
        if pushNarrow: discard ctx.procScoped.caseNarrow.pop()
        branches.add mkBranch(cond, armBody)
      of nnkElse, nnkElseExpr:
        elseBody = parseStmt(arm[0], ctx)
      else:
        error(&"unexpected case-arm kind {arm.kind}", arm)
    let ifNode = mkIf(branches, elseBody)
    if preamble3.len == 0: ifNode
    else:
      var all = preamble3
      all.add ifNode
      mkBlock(all)
  of nnkForStmt:
    # Phase 6: desugar common shapes to while loops.
    # Common cases (after semcheck):
    #   * `for i in a..b: body`  → Infix(.., a, b) — inclusive
    #   * `for i in a..<b: body` → Infix(..<, a, b) — exclusive
    #   * `for x in arr: body`   → Sym arr — static-N array
    #   * `for x in s: body`     → Sym s — seq[T]
    # RFC-0005 S8bc (item 6): a Table's `pairs` / `keys` / `values`, ahead of
    # the loop-variable shape check below (its `for (k, v)` form is a
    # `nnkVarTuple`).
    block tableFor:
      let tf = parseTableForLoop(n, ctx)
      if tf != nil: return tf
    let iterVar = n[0]
    let iterExpr = n[^2]
    let bodyNode = n[^1]
    iterVar.expectKind nnkSym
    let iterName = iterVar.strVal
    # RFC-0005 S8c: the range and container desugarings below model the
    # STDLIB iterators; a user iterator that shares the name (a non-generic
    # `items` beating `system.items[T]`, a user `..`) is not one of them.
    if iterExpr.kind == nnkInfix and iterExpr[0].kind == nnkSym and
       isBuiltinNamed(iterExpr[0], [".." , "..<"]):
      let inclusive = iterExpr[0].strVal == ".."
      var preamble3: seq[IRStmt]
      let loIR = parseExpr(iterExpr[1], preamble3, ctx)
      let hiIR = parseExpr(iterExpr[2], preamble3, ctx)
      let body = parseLoopBody(bodyNode, ctx).body   # RFC-0005 S8m
      # Build: { var __iv = lo; while __iv <op> hi: { let i = __iv; body; __iv = __iv + 1 } }
      let ivName = freshSynth(ctx, "iv")
      let intTy = tInt(64, signed = true)
      let initStmt = mkLet(ivName, intTy, loIR)
      let cmpOp = if inclusive: bLe else: bLt
      let cond = mkBinop(cmpOp, mkVar(ivName), hiIR)
      # Wrap body with: let i = __iv; <body>; __iv = __iv + 1
      let bindIter = mkLet(iterName, intTy, mkVar(ivName))
      let incIv = mkAssign(ivName,
        mkBinop(bAdd, mkVar(ivName), mkIntLit(1)))
      let loopBody = mkBlock(@[bindIter, body, incIv])
      let whileSt = mkWhile(cond, loopBody)
      var allStmts = preamble3
      allStmts.add initStmt
      allStmts.add whileSt
      mkBlock(allStmts)
    elif iterExpr.kind == nnkCall and iterExpr.len == 2 and
         iterExpr[0].kind == nnkSym and
         isBuiltinNamed(iterExpr[0], ["mitems", "mpairs"]):
      parseMutIter(n, iterExpr, bodyNode, ctx)   # RFC-0005 S8bu
    elif iterExpr.kind == nnkCall and iterExpr.len == 2 and
         iterExpr[0].kind == nnkSym and isBuiltinNamed(iterExpr[0], ["items", "pairs"]):
      # `for x in container` semchecks to `for x in items(container)`.
      let container = iterExpr[1]
      let recvCls = classifyType(container)
      # RFC-0005 S8z: `for i, x in pairs(c)` (n.len == 4) binds `i` to the
      # INDEX and `x` to the element. Before S8z this arm read only `n[0]`,
      # so `i` was bound to the element and `x` was never bound: a label
      # reading `i` alone (`if i == 0`) was a false `sxSat` over any array
      # or seq, and one reading `x` a `feGlobalReadUnmodelled`. A
      # single-variable `pairs` binds a `(key, val)` tuple, which this
      # desugaring does not build: a scoped decline.
      let isPairs = iterExpr[0].strVal == "pairs"
      if (isPairs and n.len != 4) or (not isPairs and n.len != 3):
        return ctx.declineMarker(feUnsupportedStmtKind,
          &"for-loop over `{iterExpr[0].strVal}` with {n.len - 2} loop " &
          "variable(s): only `for x in c` and `for i, x in pairs(c)` are modelled")
      if isPairs: n[1].expectKind nnkSym
      let valName = if isPairs: n[1].strVal else: iterName
      if recvCls.ty.kind == itString:
        # Phase 15 S3 (ADR-0006): `for c in s` over a *symbolic* string is
        # unsupported — NOT for a byte/codepoint reason (byte-faithful makes
        # iteration positional and well-defined), but because the iteration
        # count is the string's unknown symbolic length: there is no sound
        # bounded encoding of an unbounded-length positional walk. We classify
        # it here (BEFORE parsing the body — the body may itself reference the
        # loop var in ways that only typecheck inside the loop) so the walker
        # marks the path uncertain (sxUnknown), never a silent UNSAT
        # (Invariant 3).
        # Phase 16 INV: wire to structured seByteIterUnsupported — the parse-time
        # error is added to ctx.parseErrors (drained into prog.parseErrors →
        # r.errors at runtime), then mkUnsupported yields w.sawUnknown = true in
        # the walker, together producing sxUnknown + classified kind (Invariant 3).
        return ctx.declineAtSite(
          seByteIterUnsupported,
          "Phase 15 S3: `for c in s` over a symbolic string — unbounded " &
                 "iteration length has no sound bounded encoding (ADR-0006, " &
                 "seByteIterUnsupported)",
          "symex Phase 15 S3: `for c in s` over a symbolic " &
            "string is unsupported (unbounded symbolic iteration length, " &
            "not a byte/codepoint mismatch — ADR-0006)")
      # RFC-0005 S8m: an array is unrolled (a `break` leaves the block
      # around the whole unroll); a seq is a `while` whose increment follows
      # the body (a `continue` leaves the body's block).
      let (body, unrollBrk) = parseLoopBody(bodyNode, ctx,
                                            unrolled = recvCls.ty.kind == itArray)
      let intTy = tInt(64, signed = true)
      case recvCls.ty.kind
      of itArray:
        # Static unroll: N iterations, each with `let i = arr[k]; body`.
        # RFC-0005 S8z: under `pairs`, iteration `k` binds the index to
        # Nim's `lo + k` (the array's first index plus the position), in the
        # index variable's own type (an enum, `char`, a `range`).
        var preamble3: seq[IRStmt]
        var arrIR = parseExpr(container, preamble3, ctx)
        if arrIR.kind notin {iekVar, iekField}:
          # RFC-0005 S8bl (item 4): an array literal (`for x in [a, b]`) or
          # any other computed array is bound once, then indexed; the
          # index statement reads a variable or a field (it was a walker
          # fault: `lowerLeafInExpr` met an `iekArrayLit`).
          let arrTmp = freshSynth(ctx, "farr")
          preamble3.add mkLet(arrTmp, recvCls.ty, arrIR)
          arrIR = mkVar(arrTmp)
        var stmts = preamble3
        var iters: seq[IRStmt]
        let lo = arrayIndexLow(container)
        let idxTy = if isPairs: classifyType(iterVar).ty else: nil
        for k in 0 ..< recvCls.ty.size:
          # bind `valName = arr[k]`
          let synth = freshSynth(ctx, "fa")
          iters.add mkIndexStmt(synth, arrIR, mkIntLit(int64(k)),
                                recvCls.ty.elemTy)
          if isPairs:
            iters.add mkLet(iterName, idxTy, mkIntLit(lo + int64(k)))
          iters.add mkLet(valName, recvCls.ty.elemTy, mkVar(synth))
          iters.add body
        if unrollBrk.len > 0: stmts.add mkLabelledBlock(unrollBrk, iters)
        else: stmts.add iters
        mkBlock(stmts)
      of itSeq:
        # Desugar: var __iv = 0; while __iv < s.len: let x = s[__iv]; body; __iv += 1
        var preamble3: seq[IRStmt]
        let seqIR = parseExpr(container, preamble3, ctx)
        let ivName = freshSynth(ctx, "iv")
        let initStmt = mkLet(ivName, intTy, mkIntLit(0))
        let lenExpr = mkSeqLen(seqIR)
        let cond = mkBinop(bLt, mkVar(ivName), lenExpr)
        let synth = freshSynth(ctx, "fs")
        # A-normalised index: isIndex stmt + bind via let
        let idxStmt = mkIndexStmt(synth, seqIR, mkVar(ivName),
                                  recvCls.ty.seqElemTy)
        let bindIter = mkLet(valName, recvCls.ty.seqElemTy, mkVar(synth))
        let incIv = mkAssign(ivName,
          mkBinop(bAdd, mkVar(ivName), mkIntLit(1)))
        var loopStmts = @[idxStmt]
        if isPairs:   # RFC-0005 S8z: `i` is the position
          loopStmts.add mkLet(iterName, intTy, mkVar(ivName))
        loopStmts.add @[bindIter, body, incIv]
        let loopBody = mkBlock(loopStmts)
        let whileSt = mkWhile(cond, loopBody)
        var allStmts = preamble3
        allStmts.add initStmt
        allStmts.add whileSt
        mkBlock(allStmts)
      else:
        # itString is handled by the early return above (before body parse).
        ctx.declineMarker(feUnsupportedStmtKind, &"unsupported for-loop container kind: {recvCls.ty.kind}")
    elif iterExpr.kind == nnkCall and iterExpr.len >= 1 and
         iterExpr[0].kind == nnkSym:
      # Phase 16 A7-S3: intercept `for r in s.runes` / `for r in lit.runes`
      # BEFORE A3 attempts to getImpl/inline the std/unicode `runes` iterator.
      # Origin guard (owner == "unicode") ensures a user-defined `runes` iterator
      # falls through to A3 (or degrades) unchanged — regression-safe.
      # This block uses `return` to exit early; the A3 code below runs only if
      # `break runesA7s3` fires (non-unicode origin → fall through).
      block runesA7s3:
        if iterExpr.len == 2 and iterExpr[0].strVal == "runes":
          let runeIterSym = iterExpr[0]
          let runeIterOwner = runeIterSym.owner
          if runeIterOwner.kind == nnkSym and runeIterOwner.strVal == "unicode":
            let container = iterExpr[1]
            if container.kind in {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
              # Concrete literal: decode runes in Nim at parse time → static unroll.
              # Each rune is bound to iterName as an svInt (Rune → tInt(64), A7-S1).
              # Exact vs Nim: we call Nim's own toRunes (Invariant 3 §Soundness).
              let runeSeq = unicode.toRunes(container.strVal)
              let runeTy = tInt(64, signed = true)
              # RFC-0005 S8m: unrolled -- jumps leave labelled blocks.
              let (body, unrollBrk) = parseLoopBody(bodyNode, ctx, unrolled = true)
              var stmts: seq[IRStmt]
              for rune in runeSeq:
                stmts.add mkLet(iterName, runeTy,
                                mkIntLit(int64(rune.ord)))
                stmts.add body
              return wrapJumpBlock(unrollBrk, mkBlock(stmts))
            else:
              # Symbolic string: UTF-8 grouping over an unknown byte stream has
              # no quantifier-free Z3 encoding → seRuneDecodeSymbolic (ADR-0017;
              # RFC-0005 S5 split it off seZ3StringIncomplete: the loop statement
              # is DROPPED here -- dcSubstituted, not a fresh symbol).
              # Must NEVER reach the A3 inline path (avoid body parse → possible hang).
              return ctx.declineAtSite(
                seRuneDecodeSymbolic,
                "A7-S3: `for r in s.runes` over symbolic string — UTF-8 " &
                       "grouping over unknown byte stream; no quantifier-free Z3 " &
                       "encoding (ADR-0017)",
                "symex A7-S3: `for r in s.runes` over " &
                                     "symbolic string unsupported (seRuneDecodeSymbolic)")
          # Non-unicode origin: break to fall through to A3 path below.
      # ---- A3-S1/S2a (ADR-0014): inline direct-call closure/inline iterator ------
      # Placed AFTER the items/pairs arm (which already claimed those iterator
      # syms optimally); fires only for unrecognised direct iterator calls.
      # Collect all loop-variable names. Single-var (S1): n.len == 3, [iterName].
      # Multi-var tuple-yield (S2a): n.len > 3, each n[vi] nnkSym for vi in 0..n.len-3.
      var loopVarNames: seq[string]
      for vi in 0 ..< n.len - 2:
        if n[vi].kind != nnkSym:
          return ctx.declineMarker(feUnsupportedStmtKind, "A3-S2a: loop variable at index " & $vi &
            " is " & $n[vi].kind & " (expected nnkSym; ADR-0014 S2)")
        loopVarNames.add n[vi].strVal
      let itSym = iterExpr[0]
      # Try to resolve the callee's implementation. A builtin/magic/unresolvable
      # sym causes getImpl to raise; catch and fall through (→ sxUnknown, sound).
      var impl: NimNode = nil
      try: impl = itSym.getImpl
      except CatchableError: discard
      if impl != nil and impl.kind == nnkIteratorDef:
        let implBody = body(impl)
        # ---- Step 0: soundness pre-scans — ALL must pass; any failure → degrade
        # (a) Require ≥1 surface yield (catches post-transf state-machine lowering)
        if not hasYieldShallow(implBody):
          return ctx.declineMarker(feUnsupportedStmtKind, "iterator " & itSym.strVal & " has no surface " &
            "nnkYieldStmt — may be post-transf lowered; cannot inline " &
            "(ADR-0014 D2-0a, CRIT-4)")
        # (b) No bare `return` in body — early-finish mis-modeled by proc-return
        if hasReturnShallow(implBody):
          return ctx.declineMarker(feUnsupportedStmtKind, "iterator " & itSym.strVal & " contains `return` " &
            "— early-finish not yet modeled in A3-S1 (ADR-0014 D2-0b, CRIT-1)")
        # (c) No break/continue in the raw for-body (unsound for finite iterators)
        if hasBreakContinueShallow(bodyNode):
          return ctx.declineMarker(feUnsupportedStmtKind, "for-body contains `break`/`continue` — unsound " &
            "for finite iterators in A3-S1; lifted in S2 (ADR-0014 D2-0c, CRIT-2)")
        # (d) Recursion guard: if this iterator is already being inlined, degrade
        let itSymName = itSym.strVal
        if itSymName in ctx.activeIterators:
          return ctx.declineMarker(feUnsupportedStmtKind, "recursive iterator " & itSymName &
            " — cannot inline (ADR-0014 D2-0d, CRIT-3)")
        # (e) Non-trivial default params that can't safely be evaluated out-of-scope
        let formal = impl[3]  # nnkFormalParams: [retTy, IdentDefs…]
        block checkDefaults:
          var argIdx = 0  # tracks supplied call arg index
          for fi in 1 ..< formal.len:
            let paramDef = formal[fi]
            if paramDef.kind != nnkIdentDefs: continue
            let defaultNode = paramDef[paramDef.len - 1]
            for pj in 0 ..< paramDef.len - 2:
              if argIdx >= iterExpr.len - 1:
                # This param is absent from the call — check its default
                let isLit = defaultNode.kind in
                  {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit,
                   nnkUIntLit, nnkUInt8Lit, nnkUInt16Lit, nnkUInt32Lit, nnkUInt64Lit,
                   nnkFloat32Lit, nnkFloat64Lit, nnkStrLit, nnkRStrLit,
                   nnkTripleStrLit, nnkCharLit, nnkNilLit}
                let isConst = defaultNode.kind == nnkSym and
                              symKind(defaultNode) in {nskConst, nskEnumField}
                if not isLit and not isConst:
                  return ctx.declineMarker(feUnsupportedStmtKind, "iterator " & itSymName & " param " &
                    paramDef[pj].strVal & " has non-trivial default — cannot " &
                    "safely evaluate out-of-scope (ADR-0014 D2-0e, N-2)")
              inc argIdx
        # ---- Steps 1-4: inline transform ----
        # RFC-0005 S8e: the inlined body runs in THIS routine's env, so its
        # params and locals are claimed in this naming scope: an iterator
        # local spelled like a caller local gets its own slot (and a body
        # local shadowing an iterator param is not substituted as the param).
        claimRoutine(impl)
        # D2 step 2: bind each formal param to a `let` of its own scoped
        # name. RFC-0005 S8bc: the body keeps its TYPED parameter symbols.
        # They were replaced by untyped `__sym_itp_N` idents
        # (`substIteratorParams`), so every site that reads an operand's
        # type (a conversion's source width, a hidden widening) could not:
        # `int(n)` of a parameter declined (S8at), and a hidden `int32 ->
        # int` widening of one was a walker fault. `claimRoutine(impl)`
        # above already gives each formal a name unique in this scope (a
        # caller local of the same spelling claimed first, so the formal is
        # the one renamed), so the substitution bought nothing the scoped
        # name does not.
        ctx.activeIterators.incl itSymName
        var preambleStmts: seq[IRStmt]
        var iterBody = implBody   ## RFC-0005 S8bs: formals bound by name
        var argIdx2 = 0
        for fi in 1 ..< formal.len:
          let paramDef = formal[fi]
          if paramDef.kind != nnkIdentDefs: continue
          let tyNode = paramDef[paramDef.len - 2]
          let cls = classifyType(tyNode)
          let defaultNode = paramDef[paramDef.len - 1]
          for pj in 0 ..< paramDef.len - 2:
            let bindName = paramDef[pj].strVal   # scoped (RFC-0005 S8e)
            let argNode =
              if argIdx2 < iterExpr.len - 1: iterExpr[argIdx2 + 1]
              else: defaultNode  # use the pre-checked literal/const default
            if argIdx2 < iterExpr.len - 1 and
               bindIterArg(impl, paramDef[pj], tyNode, argNode, iterBody,
                           preambleStmts, ctx):
              inc argIdx2
              continue
            var argPre: seq[IRStmt]
            let argIR = parseExpr(argNode, argPre, ctx)
            for s in argPre: preambleStmts.add s
            preambleStmts.add mkLet(bindName, cls.ty, argIR)
            inc argIdx2
        # D2 step 3+4: substitute params in body, rewrite yields, parse.
        # Compute the iterator element type from its DECLARED return type in
        # nnkFormalParams[0]. Using classifyType on the yield EXPRESSION itself
        # (n[0] inside the body) fails for literal yields (e.g. `yield 1`) whose
        # pre-transf AST nodes do not carry runtime type annotations (ADR-0014).
        let yieldElemTyTop = classifyType(formal[0]).ty
        # Build per-variable bindings. Single-var (S1) uses the whole type.
        # Multi-var (A3-S2a) destructures the itTuple fields positionally.
        # Both arity-mismatch and non-itTuple degrade soundly (Invariant 3).
        var iterVarBindings: seq[(string, IRType)]
        if loopVarNames.len == 1:
          iterVarBindings.add (loopVarNames[0], yieldElemTyTop)
        else:
          # Require itTuple return type with matching arity — degrade otherwise.
          if yieldElemTyTop.kind != itTuple:
            ctx.activeIterators.excl itSymName
            return ctx.declineMarker(feUnsupportedStmtKind, "A3-S2a: multi-var for requires itTuple iterator " &
              "return type; got " & $yieldElemTyTop.kind &
              " (ADR-0014 S2, Invariant 3)")
          if yieldElemTyTop.fields.len != loopVarNames.len:
            ctx.activeIterators.excl itSymName
            return ctx.declineMarker(feUnsupportedStmtKind, "A3-S2a: arity mismatch — iterator tuple has " &
              $yieldElemTyTop.fields.len & " fields, for-loop has " &
              $loopVarNames.len & " vars (ADR-0014 S2, Invariant 3)")
          for k, name in loopVarNames:
            iterVarBindings.add (name, yieldElemTyTop.fields[k])
        let bodyIR = parseIterBodyStmt(iterBody, iterVarBindings, bodyNode, ctx)
        ctx.activeIterators.excl itSymName
        # Combine preamble + inlined body
        if preambleStmts.len > 0:
          preambleStmts.add bodyIR
          mkBlock(preambleStmts)
        else:
          bodyIR
      else:
        ctx.declineMarker(feUnsupportedStmtKind, &"unsupported for-loop iterable: {itSym.strVal} is not a " &
          "resolvable direct iterator call (ADR-0014 D1)")
    else:
      ctx.declineMarker(feUnsupportedStmtKind, &"unsupported for-loop iterable shape: {iterExpr.kind}")
  of nnkBreakStmt:
    resolveBreak(n, ctx)        # RFC-0005 S8m
  of nnkContinueStmt:
    resolveContinue(ctx)        # RFC-0005 S8m
  of nnkReturnStmt:
    # Semchecked AST forms for `return EXPR`:
    #   * `return EXPR` directly (untyped)         → ReturnStmt[EXPR]
    #   * `return EXPR` in a value-returning proc  → ReturnStmt[Asgn(result, EXPR)]
    # Phase 3 handles both.
    let inner = n[0]
    if inner.kind == nnkEmpty:
      mkReturn()
    elif inner.kind == nnkAsgn and inner[0].kind == nnkSym and
         inner[0].strVal == "result":
      mkReturnVal(parseExpr(inner[1], preamble, ctx))
    else:
      mkReturnVal(parseExpr(inner, preamble, ctx))
  of nnkLetSection, nnkVarSection:
    var stmts: seq[IRStmt]
    for id0 in n:
      id0.expectKind nnkIdentDefs
      # RFC-0005 S8ay: a name with a pragma also arrives from the `std/re`
      # `=~` template's expansion (`var matches {.inject.}: ...`); it is an
      # ordinary local under its symbol (the non-global case below).
      # RFC-0005 S8be. A name with a pragma (`var c {.global.} = 0`) is a
      # `PragmaExpr`, which has no type: `classifyType` below hard-errored
      # on it (a compile-time crash of the whole `symexFind`). A
      # `{.global.}` name is a module-level variable (`isRoutineGlobal`):
      # Nim runs its initialiser once, at program start, not here, so its
      # declaration is no statement of the walk, and every use of it reads
      # the global. Any other pragma leaves an ordinary local, under its
      # symbol; `{.noinit.}` without an initialiser has no defined value
      # and declines.
      var id = id0
      var hasPragma = false
      for j in 0 ..< id0.len - 2:
        if id0[j].kind == nnkPragmaExpr: hasPragma = true
      if hasPragma:
        id = newNimNode(nnkIdentDefs)
        for j in 0 ..< id0.len - 2:
          let d = id0[j]
          if d.kind != nnkPragmaExpr:
            id.add d
            continue
          if isModuleGlobal(d[0]): continue
          var noInit = false
          if d.len > 1:
            for p in d[1]:
              if p.kind in {nnkIdent, nnkSym} and p.strVal == "noinit":
                noInit = true
          if noInit and id0[^1].kind == nnkEmpty:
            stmts.add ctx.declineMarker(feUnsupportedStmtKind,
              "`{.noinit.}` variable `" & d[0].strVal & "` with no " &
              "initialiser: its value is undefined")
            continue
          id.add d[0]
        if id.len == 0: continue
        id.add id0[^2]
        id.add id0[^1]
      let valNode = id[id.len - 1]
      # Phase 15 R11 (ADR-0010, RFC §R11). An unsafe POINTER MATERIALISATION RHS
      # (`cast[ptr T](...)`, `addr x`, `unsafeAddr x`) is unmodelable in the
      # logical-heap model — classify `heUnsafeCast` (sevError) so the verdict
      # degrades to `sxUnknown` (Invariant 3 — never a silent sat/unsat) and emit
      # `isUnsafeCast`. We do NOT model the address. The guard keys strictly on
      # the pointer-materialisation node shapes (`nnkCast` to `ptr T`, `nnkAddr`),
      # so a no-cast binding is unaffected. Without this, the cast/addr node would
      # hit parseExpr's hard `error()` (a compile-time failure, not a classified
      # halt); R11 converts it to the classified-error path.
      block:
        # RFC-0005 S8ax: `addr x` of a routine's variable is an ordinary
        # pointer value (its address cell, `addrCellLocal`).
        # RFC-0005 S8be: so is `addr s[i]` of a routine's seq (its
        # element cell, `elemCellOf`).
        let ucReason = if addrCellLocal(valNode) != nil or
                          elemCellOf(valNode).root != nil: ""
                       else: unsafeCastReason(valNode)
        if ucReason.len > 0:
          stmts.add ctx.declineUnsafeCast(
            "unsafe pointer materialisation (" & ucReason & ") not modeled",
            ucReason)
          continue
      # Phase 15 R2 (ADR-0010): a `new T` RHS is an ALLOCATION, not an ordinary
      # expression. Lower it to an `isNew` stmt per bound name — `freshRef` mints
      # a fresh `Ref_T` const for the let-name in the walker. The binding's
      # classified type is the `ref T` itself (`itRef(pointee)`), which is exactly
      # `mkNewT`'s `nRefTy` (the walker extracts the pointee for the ref sort).
      if isNewCall(valNode):
        for j in 0 ..< id.len - 2:
          let classified = classifyType(id[j])
          stmts.add mkNewT(id[j].strVal, classified.ty)
        continue
      # RFC-0005 S8bq (item 3): `let r = re"..."` with a pattern PCRE
      # accepts -- a regex call given `r` reads the literal.
      if n.kind == nnkLetSection and id.len == 3 and id[0].kind == nnkSym:
        let rc = regexCtorCall(valNode)
        if rc != nil:
          let (flag, pat) = regexLiteralOf(rc)
          if flag != "?" and
             parsePcre(pat, flag == "rex").status in {psOk, psUnmodelled}:
            ctx.regexLetLiterals.add (sym: id[0], flag: flag, pattern: pat)
      # ADR-0014 D6: a bare iterator sym in VALUE position (`let it = someIter`)
      # has no supported IR scalar type — `classifyType` would hard-error on the
      # `iterator(...): T` type. Emit an mkUnsupported to set sawUnknown and skip
      # the binding entirely. The subsequent `for x in it(…)` also degrades:
      # D1 uses getImpl at AST level (not the IR env), so the missing env entry
      # is irrelevant; getImpl on a nskLet sym returns IdentDefs, not nnkIteratorDef,
      # so D1 emits mkUnsupported too → sxUnknown (CRIT-5, D6 deferred).
      if valNode.kind == nnkSym and symKind(valNode) == nskIterator:
        stmts.add ctx.declineMarker(feUnsupportedStmtKind, "iterator value binding `" & valNode.strVal &
          "` not supported (ADR-0014 D6 deferred)")
        continue
      # Uninitialized `var x: T` (no initializer): the value node is nnkEmpty.
      # Nim zero-initializes, so bind each name to its type's ZERO value rather
      # than reaching parseExpr's hard `error()` on nnkEmpty (which aborts macro
      # expansion — strictly worse than a classified halt). Unmodeled defaults
      # degrade to mkUnsupported → sxUnknown (sound, Invariant 3).
      if valNode.kind == nnkEmpty:
        for j in 0 ..< id.len - 2:
          let classified = classifyType(id[j])
          # RFC-0005 S8z: an array, object / tuple or variant local is
          # Nim's `default(T)` too (`iekZeroValue` -> `defaultZero`, or an
          # in-band `feUnsupportedOpHavoc` when an element or field has no
          # modelled zero). It was this decline, which left the name
          # unbound: `var a: array[3, int]; a[1] = x` then faulted in
          # `isIndex` (`recv.kind == svArray` on the catch-all's int), and
          # `var r: Obj; ord(r.e)` in `lowerConvIntWidth`. S8z special-cased
          # this call site rather than `zeroValueForType` itself, out of
          # caution for its other (catch-all-dummy) callers; RFC-0005 S8aj
          # audited every one of those callers (each already discards its
          # dummy under an SND-1 taint before it is ever read) and moved the
          # fix into `zeroValueForType` directly, which also covers `itSeq`
          # (`var s: seq[int]`, not fixed by the special case here) for
          # free. Plain delegation below.
          let zero = zeroValueForType(classified.ty)
          if zero != nil:
            stmts.add mkLet(id[j].strVal, classified.ty, zero)
          elif classified.ty.kind == itUninterp:
            # RFC-0005 S8ap (S8ao's remainder): an `itUninterp` local has
            # no zero (`zeroValueForType`'s own argument), and the decline
            # now names WHY with the placeholder's own kind -- the one
            # `allocateSym` raises for the same placeholder anywhere else --
            # instead of the generic `feUnsupportedStmtKind`, which said
            # only that some statement shape was unparsed.
            let (k, why) = uninterpVarDecline(classified.ty)
            stmts.add ctx.declineMarker(k, "uninitialized `var` `" &
              id[j].strVal & "`: " & why & " (no zero value)")
          else:
            stmts.add ctx.declineMarker(feUnsupportedStmtKind, "uninitialized `var` of unmodeled type " &
              $classified.ty.kind & " (zero-init not modeled this cycle)")
        continue
      let valIR = parseExpr(valNode, preamble, ctx)
      # Phase 15 Cluster C (C1): a proc-valued binding (`let f = proc(...) = …`)
      # has no scalar IRType — `classifyType` would reject the proc type. The
      # binding's value IR is an `iekLambda`; bind it under a placeholder type
      # (the walker stubs the `iekLambda` rvalue with `ceNotImplemented` before
      # the binding's type is ever consumed). C2a gives it a real closure type.
      if valIR != nil and valIR.kind in {iekLambda, iekClosureCall}:
        for j in 0 ..< id.len - 2:
          stmts.add mkLet(id[j].strVal, tBool(), valIR)
      else:
        for j in 0 ..< id.len - 2:
          let classified = classifyType(id[j])
          # Round-6 B7r2: a literal-seeded scan/pair-loop counter (see
          # `collectIntOffsetLiteralLocals`'s doc comment) gets `svInt`
          # instead of the type-driven BV default at THIS binding site.
          # Round-6 R4: symbol-identity consult (`containsSym`), not bare
          # name — see `ProcScopedCollectors.intOffsetLiteralLocals`'s own doc comment.
          stmts.add mkLet(id[j].strVal, classified.ty, valIR,
                          containsSym(ctx.procScoped.intOffsetLiteralLocals, id[j]))
    if stmts.len == 1: stmts[0] else: mkBlock(stmts)
  of nnkCall, nnkCommand:
    # nnkCommand is the command-syntax form of a call (e.g.
    # `echo "x"` vs `echo("x")`). Same shape, same dispatch.
    if isMarkerCall(n, "symexTarget"):
      let argNode = n[1]
      if argNode.kind notin {nnkStrLit, nnkRStrLit, nnkTripleStrLit}:
        error("symex: `symexTarget` requires a string literal", argNode)
      mkTargetLabel(argNode.strVal)
    elif isMarkerCall(n, "symexAssert"):
      mkAssert(parseExpr(n[1], preamble, ctx))
    elif isMarkerCall(n, "symexAssume"):
      ## Phase 16 SND-2: `symexAssume` is filter/prune, NOT assert — it must
      ## NOT fork an `AssertionDefect`. Previously byte-identical to
      ## `symexAssert` (`mkAssert`), which masked `sxUnsat` with a false
      ## `sxRaised(AssertionDefect)` for a violatable assume ahead of a
      ## genuinely-unreachable target. Distinct IR kind: `mkAssume`.
      ##
      ## RFC-0005 S8q: a boolean `and` chain is one assume per conjunct, in
      ## source order. `symexAssume(a and b)` and `symexAssume(a);
      ## symexAssume(b)` are the same program in Nim: `a` is evaluated; if
      ## it is false the run is filtered either way, and `b` is evaluated
      ## (and may raise) only when `a` is true. Parsed whole, D1c's guard
      ## temporaries (`let sc = a; if sc: sc = b`) forked every path at
      ## every conjunct with a raising read, so n conjuncts gave 2^(n-1)
      ## paths (B7R-6: 16 conjuncts, 32,768 target solves); split, each
      ## conjunct is one path constraint and only its own raises fork.
      ## Conjunct k's preamble runs after assume k-1, as its evaluation does.
      var conjuncts: seq[NimNode]
      proc flattenAnd(c: NimNode) =
        let u = if c.kind == nnkPar and c.len == 1: c[0] else: c
        if u.kind == nnkInfix and u.len == 3 and u[0].kind in {nnkIdent, nnkSym} and
           u[0].strVal == "and" and
           (u[0].kind == nnkIdent or isBooleanShortCircuitInfix(u)):
          flattenAnd(u[1])
          flattenAnd(u[2])
        else:
          conjuncts.add c
      flattenAnd(n[1])
      if conjuncts.len <= 1:
        mkAssume(parseExpr(n[1], preamble, ctx))
      else:
        var stmts = @[mkAssume(parseExpr(conjuncts[0], preamble, ctx))]
        for k in 1 ..< conjuncts.len:
          var pre: seq[IRStmt]
          let c = parseExpr(conjuncts[k], pre, ctx)
          stmts.add pre
          stmts.add mkAssume(c)
        mkBlock(stmts)
    elif n.len == 2 and isNewCall(n) and
         (block:
            let recv = unwrapHidden(n[1])
            recv.kind == nnkSym and
              recv.symKind in {nskVar, nskResult, nskParam, nskLet} and
              classifyType(recv).ty.kind in {itRef, itPtr}):
      # RFC-0005 S8u. `new(x)` -- system's `proc new[T](a: var ref T)` --
      # allocates a fresh cell and stores its address in `x`: the same
      # rebind as `x = new T` (Phase 15 R8b's `mkNewT` under `x`'s name,
      # every field of the fresh cell zero-initialised). Before S8u the
      # statement was not modelled, so a callee's `new(result)` left
      # `result` as it was and `retBindEq` faulted on the kind mismatch
      # (`weInternalWalkerFault`, "svRef vs svBV64").
      let recv = unwrapHidden(n[1])
      mkNewT(recv.strVal, classifyType(recv).ty)
    elif n.len == 3 and n[0].kind == nnkSym and
         isBuiltinNamed(n[0], ["incl", "excl"]) and
         unwrapHidden(n[1]).typeKind != ntyNone and
         classifyType(unwrapHidden(n[1])).ty.kind == itBitSet:
      # RFC-0005 S8bq (item 2). `incl` / `excl` on a builtin set.
      parseBitSetInclExcl(n, preamble, ctx)
    elif n.len >= 2 and n[0].kind == nnkSym and isBuiltinNamed(n[0], ["inc", "dec"]) and
         (block:
            let recv = unwrapHidden(n[1])
            recv.kind == nnkSym and classifyType(recv).ty.kind == itInt):
      # Phase 15 R8. `inc(i)`/`dec(i)` on an INT receiver — the normal ordinal
      # mutation. Lower to the equivalent env rebind `i = i ± y` (`y` defaults to
      # 1) so the int case symexes natively (the `{.magic.}` body is not walked).
      # RFC-0005 S8c: the R8 `ptr`-operand guard that preceded this arm is
      # deleted -- `system.inc` takes an Ordinal, so an `inc(p: ptr T)` is a
      # USER overload, which the user-callee gate walks before this chain.
      let recv = unwrapHidden(n[1])
      let nm = recv.strVal
      let stepIR = if n.len >= 3: parseExpr(n[2], preamble, ctx) else: mkIntLit(1)
      let bop = if n[0].strVal == "inc": bAdd else: bSub
      # #163 review R27: `inc`/`dec` on a ranged receiver raises RangeDefect
      # in real Nim exactly like a plain assignment — resolve by true
      # symbol identity, same as the plain-assign arm above.
      let incCls = classifyType(recv)
      # #163 review (rev item 3, R30): match the five sibling `aty` sites'
      # gate (plain-assign, aug-assign, and the three scan-recognizer sites)
      # by also checking `.kind == itInt` rather than `hasRange` alone — a
      # `hasRange` type always classifies `itInt` at THIS site today (the
      # `inc`/`dec` receiver gate above already requires `itInt`), so this is
      # a consistency fix, not a behavior change: one way this check is done.
      let incTy = if incCls.ty.kind == itInt and incCls.ty.hasRange:
                    incCls.ty
                  else: nil
      mkAssign(nm, mkBinop(bop, mkVar(nm), stepIR), incTy)
    elif n.len >= 2 and n[0].kind == nnkSym and
         isBuiltinNamed(n[0], ["inc", "dec"]):
      # RFC-0005 S8bc (item 7): every other system `inc`/`dec`.
      parseIncDecLvalue(n, preamble, ctx)
    else:
      # User-proc call as a statement (void-return). Only resolvable
      # against typed AST — isolation-mode falls to `isUnsupported`.
      let calleeSym = n[0]
      if isProcFieldCall(n):
        # RFC-0005 S8bn (item 6): a call through a proc field.
        let cc = procFieldCallIR(n, preamble, ctx)
        if cc.hoisted: mkBlock(@[])
        else: mkLet(freshSynth(ctx, "closureCallSink"), tBool(), cc.e)
      elif calleeSym.kind != nnkSym:
        ctx.declineMarker(feUnsupportedStmtKind, &"call to `{n[0].repr}` not in supported fragment")
      # Phase 15 R13 (sub-track A). A CLOSURE CALL through a proc-valued
      # variable/param in STATEMENT position (e.g. `capture()` — a `let`-bound
      # closure called for its effect, with NO args). The expression-position
      # `earlyClosureCallDetect` only fires through `parseExpr`; a void-return
      # closure call reaches here. Detect it structurally (callee's impl is NOT
      # a routine def AND its type is `nnkProcTy`) and route to `iekClosureCall`
      # — the same C2b dispatch — so a captured ref/closure call symexes BEFORE
      # the `ensureProcRegistered` proc-call fall-through (which would
      # `getImpl`-fail on the variable's `nnkIdentDefs`).
      elif (block:
              let impl = calleeSym.getImpl
              impl.kind notin routineShapedForClosureDetect and
                calleeSym.getTypeInst.kind == nnkProcTy):
        # The closure call is value-producing IR; in statement position its
        # EFFECTS (a `symexTarget`/write inside the lowered body) are what matter,
        # so bind it to a synthetic sink `let` (the `discardExn` idiom) — the
        # walker descends the closure body and the binding's value is dropped.
        # RFC-0005 S8bh: a call with `var`/`addr` effects is already a
        # statement of the preamble (`closureCallIR`).
        let cc = closureCallIR(n, calleeSym, calleeSym.strVal, preamble, ctx)
        if cc.hoisted: mkBlock(@[])
        else: mkLet(freshSynth(ctx, "closureCallSink"), tBool(), cc.e)
      else:
        let calleeName = calleeSym.strVal
        # Unwrap semcheck-inserted HiddenDeref / HiddenAddr / HiddenStdConv
        # on the first argument (receiver position for method-call syntax
        # like `s.add(v)`).
        let recv1 = if n.len > 1: unwrapHidden(n[1]) else: nil
        # RFC-0005 S8c: a user callee -- whatever its name -- and every
        # transparent/opaque/foreign callee take the routine-call path; only
        # a stdlib callee may complete one of the builtin mutation shapes
        # below (`add`/`del`/`insert`/`incl`/`excl`/`[]=`).
        let userCallee = isUserCallee(calleeSym)
        let m = getStdlibModelFor(calleeName, itBool)  ## kind ignored
        if userCallee or hasSymexTransparentPragma(calleeSym) or
           m.kind == smkOpaqueEffectful or hasSymexOpaquePragma(calleeSym) or
           isBodilessForeign(calleeSym):
          parseRoutineCallStmt(n, calleeSym, preamble, ctx)
        # #145 mutations recognised by name + receiver kind.
        elif recv1 != nil and recv1.kind == nnkSym:
          let recvName = recv1.strVal
          let recvCls = classifyType(recv1)
          # Phase 16 M4 (RFC-chapulin-hardening, Cluster 3): `s.add(x)` — string
          # APPEND on an `itString` receiver — is modeled as the in-place
          # concat-assign `s := s & x`, reusing the EXISTING `iekStrConcat` IR
          # (the same ctor the binary `s & x` expression arm builds, above)
          # rather than inventing a new IR kind. Z3 String theory strings are
          # immutable (ADR-0006), but the MUTATION is soundly modeled by
          # rebinding the receiver's env slot to the concatenation result — no
          # new encoding is needed beyond what `&` already has.
          #
          # Type-classify the ARGUMENT too. `s.add('c')` (a char arg)
          # classifies to `itInt` (Phase 15 Z3c: char = uint8); RFC-0005 S8p
          # models it by its Nim type (`ntyChar`): `iekStrConcat`'s lowering
          # turns a char right operand into the 1-byte string (`needleAsStr`,
          # exact under the byte-faithful model, ADR-0006). Any other
          # non-string arg keeps the clean `iekStrUnsupported` degrade
          # (sound — Invariant 3).
          # This arm must precede the `itSeq` `add` arm below (a string is NOT
          # an itSeq, but the explicit guard keeps the classification
          # intentional and self-documenting).
          if calleeName == "add" and recvCls.ty.kind == itString and n.len == 3:
            # RFC-0005 S8p: a `char` argument is the 1-byte string with that
            # byte -- `iekStrConcat` bridges a char operand on its right
            # (`needleAsStr`), so `s.add('z')` is `s := s & "z"`.
            if classifyType(n[2]).ty.kind == itString or
               unwrapHidden(n[2]).typeKind == ntyChar:
              let argIR = parseExpr(n[2], preamble, ctx)
              return mkAssign(recvName,
                mkStrOp(iekStrConcat, "&", @[mkVar(recvName), argIR]))
            else:
              let argIR = parseExpr(n[2], preamble, ctx)
              return mkAssign(recvName,
                mkStrOp(iekStrUnsupported, "string add (non-string arg)",
                        @[mkVar(recvName), argIR]))
          # `s.add(v)` on a seq
          if calleeName == "add" and recvCls.ty.kind == itSeq and n.len == 3:
            let val = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSeqAdd(mkVar(recvName), val))
          # `s.del(i)` on a seq (Nim's swap-with-last)
          elif calleeName == "del" and recvCls.ty.kind == itSeq and n.len == 3:
            let idx = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSeqDel(mkVar(recvName), idx))
          # RFC-0005 S8bl: `s.delete(i)` on a seq (system's order-keeping
          # removal; its body's `high(x)` declined).
          elif calleeName == "delete" and recvCls.ty.kind == itSeq and
               n.len == 3 and isStdlibDecl(calleeSym):
            let idx = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSeqDel(mkVar(recvName), idx, shift = true))
          # `s.insert(v, i)` on a seq
          elif calleeName == "insert" and recvCls.ty.kind == itSeq and n.len == 4:
            # RFC-0005 S8ar: the grow phase, then the place phase (see
            # `insertArgs` and `IRExpr.insGrow`).
            let args = insertArgs(recvCls.ty.seqElemTy,
                                  @[parseExpr(n[2], preamble, ctx),
                                    parseExpr(n[3], preamble, ctx)],
                                  preamble, ctx)
            preamble.add mkAssign(recvName,
              mkSeqInsert(mkVar(recvName), args[0], args[1], grow = true))
            mkAssign(recvName, mkSeqInsert(mkVar(recvName), args[0], args[1]))
          # `t.del(k)` on a Table
          elif calleeName == "del" and recvCls.ty.kind == itTable and n.len == 3:
            let key = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkTableDel(mkVar(recvName), key))
          # `s.incl(x)` on a HashSet
          elif calleeName == "incl" and recvCls.ty.kind == itSet and n.len == 3:
            let v = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSetIncl(mkVar(recvName), v))
          # `s.excl(x)` on a HashSet
          elif calleeName == "excl" and recvCls.ty.kind == itSet and n.len == 3:
            let v = parseExpr(n[2], preamble, ctx)
            mkAssign(recvName, mkSetExcl(mkVar(recvName), v))
          # `[]=(t, k, v)` on a Table
          elif calleeName == "[]=" and recvCls.ty.kind == itTable and n.len == 4:
            let key = parseExpr(n[2], preamble, ctx)
            let val = parseExpr(n[3], preamble, ctx)
            mkAssign(recvName, mkTableSet(mkVar(recvName), key, val))
          else:
            userOrMethodCallStmt(n, calleeSym, preamble, ctx)   ## RFC-0005 S8bn
        # N49 (RFC-chapulin-hardening bucket-2, design round). A DOTTED-FIELD
        # lvalue receiver (`obj.seqField.add(x)`, `w.items.del(i)`, ...) never
        # matches the bare-symbol `#145 mutations` arm above (`recvName` there
        # is a genuine env-slot name the rebind machinery can reassign;
        # `obj.seqField` has no such slot). Pre-fix this fell straight through
        # to the generic `ensureProcRegistered` call below, which then tried
        # to register/classify Nim's own compiler-magic `seq`/`string`/
        # `Table`/`HashSet` mutator (`add`/`del`/`insert`/`incl`/`excl`/`[]=`)
        # as though it were an ordinary user proc — its `monomorphize()`d
        # formal-parameter type nodes carry no resolved type, so
        # `parseCalleeImpl`'s own `classifyType(tyNode)` call hit the exact
        # "node has no type" non-catchable compile error the `sink`/`lent`/
        # `owned`/`static[N]`-array/`nnkProcTy` guards at the TOP of
        # `classifyType` already exist to route around for THEIR OWN shapes —
        # this is that same class one layer removed, reached through a path
        # none of those guards anticipated. Adjudicated: a genuine value-typed
        # field-write REBIND (reconstructing the whole enclosing record with
        # one field replaced) is a real new engine capability, out of
        # proportion for this fix; a dotted-field mutation is instead declined
        # HONESTLY and PARSE-TIME, exactly like `obj.plainField = value`'s own
        # pre-existing sibling decline (the `nnkAsgn` arm's
        # "unsupported nnkAsgn shape" catch-all, below) — RED (compile crash)
        # to GREEN (classified `sxUnknown`, never a crash), never a silent
        # wrong verdict.
        #
        # RFC-0005 S8ao (S8aj's remainder): `add` on a dotted SEQ field
        # (`o.s.add v`, `a.b.s.add v`, a ref/ptr object's `p.s.add v`) is no
        # longer blanket-declined here — `dottedSeqAddShape` recognises the
        # field-write primitive the plain assignment `<fieldPath> = v` would
        # use for the same lvalue, and `dottedFieldAdd` reuses it (see both,
        # just above `parseAsgn`).
        #
        # RFC-0005 S8ap (S8ao's remainder): EVERY mutation the bare-symbol
        # arm above models now takes that field-write primitive on a dotted
        # field too -- `del`/`insert` on a seq field, `del`/`[]=` on a Table
        # field, `incl`/`excl` on a HashSet field, and `add` on a STRING
        # field (`iekStrConcat` for a string or char argument, the bare
        # arm's `iekStrUnsupported` otherwise). The helpers were generalised
        # to `dottedFieldShape`/`dottedFieldMutate`, and each mutation's
        # value is the bare arm's own IR over the field's old value
        # (`dottedOpExpr`), so the dotted and the bare form cannot diverge
        # (`insert` declines in lowering for both). What still lands on the
        # N49 decline below is a dotted shape `dottedFieldShape` rejects (a
        # field reached through something other than a local/param value
        # chain or one ref/ptr step).
        elif recv1 != nil and
             (block:
                # A variant ARM field (`v.armField`, e.g. `v2.items2` above)
                # semchecks to `nnkCheckedFieldExpr(dotExpr, discCheck)` — the
                # SAME wrapper the `nnkAsgn` field-write arm (R6/D3, above)
                # already unwraps for its own analogous case; a plain
                # (non-variant) object field is the bare `nnkDotExpr`
                # directly.
                let fieldNode = if recv1.kind == nnkCheckedFieldExpr and
                                   recv1.len >= 1: recv1[0]
                                 else: recv1
                fieldNode.kind == nnkDotExpr and
                isKnownMutatingReceiverCall(calleeName, fieldNode, n.len)):
          let fieldNode = if recv1.kind == nnkCheckedFieldExpr and
                             recv1.len >= 1: recv1[0]
                           else: recv1
          if dottedFieldShape(fieldNode):
            # RFC-0005 S8ap. `isKnownMutatingReceiverCall` already fixed the
            # (name, receiver kind, arity) triple to one the bare arm models;
            # pick that arm's IR. Arguments are parsed left to right, before
            # the field is read (S8ao's order, and the bare arm's).
            let op = mutationOp(calleeName, classifyType(fieldNode).ty.kind, n)
            var args: seq[IRExpr]
            for i in 2 ..< n.len: args.add parseExpr(n[i], preamble, ctx)
            if op == doSeqInsert:
              # RFC-0005 S8ar: the grow phase is its own field write, so the
              # place phase's IndexDefect sees the grown field.
              args = insertArgs(classifyType(fieldNode).ty.seqElemTy, args,
                                preamble, ctx)
              let grow = dottedFieldMutate(fieldNode, doSeqInsertGrow, args,
                                           preamble, ctx)
              preamble.add grow
            dottedFieldMutate(fieldNode, op, args, preamble, ctx)
          else:
            ctx.declineAtSite(
              feUnsupportedOp,
              siteMsg(n, "N49: dotted-field lvalue mutation `" &
                                recv1.repr & "." & calleeName &
                                "(...)` unsupported (feUnsupportedOp)"),
              "N49: dotted-field lvalue mutation `" & calleeName &
                            "` unsupported (feUnsupportedOp)")
        elif recv1 != nil and pureLvalueTarget(recv1) != nil and
             isKnownMutatingReceiverCall(calleeName, recv1, n.len):
          # RFC-0005 S8at: a mutation of an ARRAY ELEMENT (`a[1].add x`,
          # `p.a[i].del j`, a Table/HashSet element likewise), or of a
          # TABLE VALUE (`t["a"].add x`, `t[k].incl y`: `[]`'s `var`
          # overload raises `KeyError` for an absent key, as the read here
          # does, and the write back is then to a present key). It fell to
          # the generic call below, which inlined the system `add` down to
          # the NimSeqV2 payload cast (`heUnsafeCast`). Nim takes the
          # element's address first (its IndexDefect), then evaluates the
          # arguments, then mutates in place; here the element is read
          # (forking the IndexDefect), the bare arm's IR is applied to it
          # (`dottedOpExpr`) and the result is written back through the
          # same lvalue arm `a[i] = v` takes (`parseAsgn`). The index is a
          # literal or a variable (`arrayElemLvalue`), so reading it twice
          # is reading it once.
          # RFC-0005 S8bl (item 1): and of a SEQ ELEMENT at a pure index
          # (`s[0].add 'x'`, `s[i].add v`) or a dereference (`p[].add v`):
          # any `pureLvalueTarget`. Those reached the generic call, where the
          # system `add` magic was registered with an empty body -- the
          # append was dropped, a false sxSat.
          let oldTmp = freshSynth(ctx, "aelt")
          let eltTy = classifyType(recv1).ty
          preamble.add mkLet(oldTmp, eltTy, parseExpr(recv1, preamble, ctx))
          let op = mutationOp(calleeName, eltTy.kind, n)
          var args: seq[IRExpr]
          for i in 2 ..< n.len: args.add parseExpr(n[i], preamble, ctx)
          var placeFrom = oldTmp
          if op == doSeqInsert:
            # RFC-0005 S8bc (item 4): `a[i].insert(x, j)`, the bare arm's and
            # the dotted field's two phases (S8ar, `IRExpr.insGrow`). It fell
            # to the generic call (`system.insert` inlined to an unsupported
            # `when` and the seq payload cast). The arguments are bound once
            # (`insertArgs`); the grow phase is its own element write, and
            # the place phase reads the grown element back, so its
            # IndexDefect (`j > len`) is judged against the seq the grow
            # left, as Nim's single in-place call does.
            args = insertArgs(eltTy.seqElemTy, args, preamble, ctx)
            let grownTmp = freshSynth(ctx, "aeltGrow")
            preamble.add mkLet(grownTmp, eltTy,
              dottedOpExpr(doSeqInsertGrow, mkVar(oldTmp), args))
            preamble.add parseAsgn(
              nnkAsgn.newTree(pureLvalueTarget(recv1), newEmptyNode()),
              mkVar(grownTmp), preamble, ctx)
            placeFrom = freshSynth(ctx, "aeltPlace")
            preamble.add mkLet(placeFrom, eltTy, parseExpr(recv1, preamble, ctx))
          let newTmp = freshSynth(ctx, "aeltNew")
          preamble.add mkLet(newTmp, eltTy, dottedOpExpr(op, mkVar(placeFrom), args))
          parseAsgn(nnkAsgn.newTree(pureLvalueTarget(recv1), newEmptyNode()),
                    mkVar(newTmp), preamble, ctx)
        else:
          userOrMethodCallStmt(n, calleeSym, preamble, ctx)   ## RFC-0005 S8bn
  of nnkDiscardStmt:
    # v68 (round 5, chapulin CRITICAL finding): a discarded expression is
    # WALKED, not dropped. Every `discard <expr>` is lowered to a synthetic
    # sink `let`, so its raise/defect forks are searched exactly as a bound
    # use would be. Previously this arm dropped everything except an
    # allowlisted handful (E8's exception intrinsics, then M2's parseInt/
    # parseBiggestInt) to `mkBlock(@[])` — `discard f(x)` never walked `f`,
    # leaving the surrounding verdict vacuously narrow (Invariant 3
    # unsoundness for the call-and-discard idiom). The parseInt allowlist
    # entry is subsumed by the general path (same iekStrToInt via parseExpr,
    # same tInt(64) via classifyType); the exception-intrinsic entry is kept
    # because its sink types are bespoke (`getCurrentException()` binds under
    # `tUninterp("")`, not the ref classification).
    if n.len == 1 and n[0].kind == nnkCall and n[0].len == 1 and
       n[0][0].kind == nnkSym and
       isBuiltinNamed(n[0][0], ["getCurrentException", "getCurrentExceptionMsg"]):
      let exprIR = parseExpr(n[0], preamble, ctx)
      let sinkTy = if n[0][0].strVal == "getCurrentExceptionMsg": tString()
                   else: tUninterp("")
      mkLet(freshSynth(ctx, "discardExn"), sinkTy, exprIR)
    elif n.len == 1 and n[0].kind != nnkEmpty:
      # The sink's type follows the let-section discipline (`classifyType`
      # on the value node; unmodeled types map to the classified
      # `__unsupported` placeholder, not a macro error). A no-scalar-type
      # value IR (lambda/closure) binds under the let-section arm's
      # placeholder-type precedent. `discard` of a `void` expression cannot
      # occur (Nim rejects it), so the node has a type.
      let sinkIR = parseExpr(n[0], preamble, ctx)
      if sinkIR == nil:
        mkBlock(@[])
      elif sinkIR.kind in {iekLambda, iekClosureCall}:
        mkLet(freshSynth(ctx, "discardSink"), tBool(), sinkIR)
      else:
        mkLet(freshSynth(ctx, "discardSink"), classifyType(n[0]).ty, sinkIR)
    else:
      # Bare `discard` (empty child) — genuinely a no-op.
      mkBlock(@[])
  of nnkEmpty, nnkCommentStmt:
    # RFC-0005 S8ax: `staleElemUseMarker`'s comment is a decline.
    if n.kind == nnkCommentStmt and n.strVal.startsWith(staleElemMarkerTag):
      return ctx.declineAtSite(feUnsupportedOp,
        n.strVal[staleElemMarkerTag.len .. ^1],
        "pointer to a seq element used after a resize (feUnsupportedOp)")
    mkBlock(@[])
  of nnkConstSection, nnkBindStmt, nnkMixinStmt:
    # SND-1 (RFC-chapulin-hardening Cluster 1) fallout fix. These three node
    # kinds are ALWAYS pure compile-time hygiene with zero runtime footprint —
    # `bind`/`mixin` only affect identifier resolution inside templates/
    # generics (never emit code), and a proc-local `const` is fully erased by
    # Nim's semantic pass (every reference is constant-folded to a literal at
    # its use site; the `ConstDef` itself binds nothing at runtime). Before
    # SND-1 these fell through to the generic `mkUnsupported` catch-all below,
    # which was harmless because `isUnsupported` was a no-op continuation. But
    # every `assert`/`doAssert` expansion's typed AST is
    # `StmtList[ConstSection(loc, ploc), BindStmt(instantiationInfo),
    # MixinStmt(failedAssertImpl), PragmaBlock[...]]` (verified via
    # `getImpl.treeRepr`) — i.e. EVERY assert unconditionally carries these
    # three siblings immediately before the real `PragmaBlock` the
    # `nnkPragmaBlock` arm above lowers to the `AssertionDefect` raise. Once
    # `isUnsupported` taints `Path.uncertain` (SND-1), those three inert
    # scaffolding statements would poison every subsequent statement on the
    # path — including the assert's own raise, via the `routeRaise`
    # chokepoint — silently demoting every `doAssert`/`assert` to `sxUnknown`.
    # These are genuinely SUPPORTED (safe to skip), not unsupported: treat
    # them as the same no-op as `nnkEmpty`/`nnkCommentStmt` above.
    mkBlock(@[])
  of nnkRaiseStmt:
    # Phase 15 E1. `raise newException(T, msg)` or bare `raise` (re-raise).
    # Typed-AST shape of `raise newException(ValueError, "x")`:
    #   RaiseStmt[ StmtListExpr[ Empty, ObjConstr[ Par[RefTy[Sym "T"]],
    #              ExprColonExpr[msg, <msgExpr>], ExprColonExpr[parent, nil] ]]]
    # Bare `raise`: RaiseStmt[Empty].
    if n.len == 0 or n[0].kind == nnkEmpty:
      mkReraise()
    else:
      var oc = n[0]
      while oc.kind in {nnkStmtListExpr, nnkStmtList} and oc.len > 0:
        oc = oc[oc.len - 1]
      if oc.kind == nnkObjConstr:
        var tn = oc[0]
        while tn.kind in {nnkPar, nnkRefTy, nnkPtrTy} and tn.len > 0:
          tn = tn[0]
        tn = canonicalExnTypeSym(tn)   ## RFC-0005 S8b: an alias is its target
        let typeId =
          if tn.kind in {nnkSym, nnkIdent}: tn.strVal else: tn.repr
        # Phase 15 E4a. Capture the RAISED type's inheritance chain (beyond the
        # RFC's nnkExceptBranch-only wording): a SUT may raise a user subtype
        # `MyError` here yet catch its stdlib base `ValueError` — the link only
        # appears at this raise site, so we must walk getImpl on `tn`.
        collectUserExnAncestors(tn, ctx)
        var msgIR: IRExpr = nil
        for k in 1 ..< oc.len:
          if oc[k].kind == nnkExprColonExpr and oc[k][0].repr == "msg":
            msgIR = parseExpr(oc[k][1], preamble, ctx)
        mkRaise(typeId, msgIR)
      else:
        # `raise <existing exception value>` (not the newException form) —
        # E1 has no value-tracking; classify so the walker stubs it.
        mkRaise(oc.repr, nil)
  of nnkTryStmt:
    # Phase 15 E1. `try: body  (except [T,…]: h)*  [finally: f]`.
    # Typed-AST shape: TryStmt[ <body>, ExceptBranch[<Type>* , <handlerBody>]*,
    #                  [Finally[<finallyBody>]] ]. A bare `except:` ExceptBranch
    # has no leading Type nodes (typeIds empty = catch-all).
    let tBody = parseStmt(n[0], ctx)
    var handlers: seq[ExceptHandler]
    var finallyBody: IRStmt = nil
    for k in 1 ..< n.len:
      let arm = n[k]
      case arm.kind
      of nnkExceptBranch:
        var typeIds: seq[string]
        for j in 0 ..< arm.len - 1:
          let tnode = canonicalExnTypeSym(arm[j])   ## RFC-0005 S8b
          typeIds.add (if tnode.kind in {nnkSym, nnkIdent}: tnode.strVal
                       else: tnode.repr)
          # Phase 15 E4a. Capture the HANDLER type's inheritance chain too
          # (RFC §E4a's stated source) — e.g. a SUT catching a user base that
          # is itself a subtype of a stdlib exn.
          collectUserExnAncestors(tnode, ctx)
        handlers.add ExceptHandler(typeIds: typeIds,
                                   body: parseStmt(arm[arm.len - 1], ctx))
      of nnkFinally:
        finallyBody = parseStmt(arm[0], ctx)
      else:
        discard
    mkTry(tBody, handlers, finallyBody)
  of nnkInfix:
    # RFC-0005 S8c: a statement-position operator whose head resolved to a
    # USER routine (a user `+=`, a void user operator) is a routine call, not
    # the augmented-assignment model below, which reads the operator's
    # spelling (`+=` -> `bAdd`).
    if isUserCallee(n[0]):
      return parseRoutineCallStmt(n, n[0], preamble, ctx)
    # Augmented-assignment statement: `<simpleVar> <op>= <rhs>`.
    # After semcheck, `s += x` presents as `nnkInfix(Sym "+=", <lhs>, <rhs>)`.
    # This is the ONLY `nnkInfix` shape that reaches statement-level dispatch —
    # expression-position infixes go through parseExpr, not parseStmtInner.
    #
    # Supported subset: `+=` | `-=` | `*=` with a plain `nnkSym` LHS (after
    # unwrapping hidden var/deref wrappers). Desugars to the same IR that
    # `<var> = <var> <op> <rhs>` would produce, so the walker sees
    # byte-identical IR for both forms (Invariant: same verdict/witness).
    #
    # Phase 16 M4 (RFC-chapulin-hardening, Cluster 3; closes SND-1's Class-B
    # `&=` case): `s &= x` on a STRING LHS is modeled as the in-place
    # concat-assign `s := s & x`, reusing the EXISTING `iekStrConcat` IR (the
    # same ctor the binary `s & x` expression arm builds, ~line 1081) —
    # string concat is a DIFFERENT IR family (`mkStrOp`, not `IRBinop`), so
    # this is a type-classify branch, NOT an addition to `binopForInfix`
    # (which has no `"&"` case and must stay that way — adding one would
    # wrongly imply `&` composes with the numeric-binop family). The branch
    # is taken BEFORE `binopForInfix` is ever called with `"&"`, so its
    # `error()` catch-all is never reached for this op.
    #
    # A non-string LHS (or non-string RHS — `iekStrConcat`'s runtime lowering
    # `doAssert`s both operands `svString`; a char RHS classifies `itInt` and
    # has no char→1-char-string IR, out of scope per M4's round-2 note) keeps
    # the prior clean `mkUnsupported` degrade rather than routing through
    # `binopForInfix("&")`, which would macro-time `error()` (a hard compile
    # abort, NOT a sound sxUnknown degrade — would be a regression).
    #
    # ALL other shapes degrade to mkUnsupported (sound — Invariant 3):
    #   * field LHS (`obj.f += y`) other than a value tuple/object field
    #     (RFC-0005 S8p models that one: `valueFieldWrite`)
    #   * index LHS (`a[i] += y`) — non-nnkSym after unwrap
    #   * any other `<op>=` not in {+=, -=, *=, &=}
    #   * (a user-defined `op=` proc is an `nnkInfix` too; RFC-0005 S8c routes
    #     it to `parseRoutineCallStmt` at the top of this arm)
    let augOp = n[0]
    if n.len == 3 and augOp.kind == nnkSym and
       augOp.strVal in ["+=", "-=", "*=", "&="]:
      let lhs = unwrapHidden(n[1])
      if lhs.kind == nnkSym:
        let nm       = lhs.strVal
        let baseOpStr = augOp.strVal[0 .. ^2]  # strip trailing "=": "+=" → "+"
        if baseOpStr == "&":
          let lhsCls = classifyType(lhs)
          if lhsCls.ty.kind == itString and classifyType(n[2]).ty.kind == itString:
            let rhsIR = parseExpr(n[2], preamble, ctx)
            return mkAssign(nm,
              mkStrOp(iekStrConcat, "&", @[mkVar(nm), rhsIR]))
          else:
            return ctx.declineMarker(
              feUnsupportedStmtKind, &"augmented assign: `&=` with non-string LHS/RHS " &
              &"(lhs kind={lhsCls.ty.kind}) not modeled; degrade to " &
              &"sxUnknown (sound, Invariant 3)")
        let bop      = binopForInfix(baseOpStr)
        let rhsIR    = parseExpr(n[2], preamble, ctx)
        # #163 review R27: `+=`/`-=`/`*=` on a ranged receiver raises
        # RangeDefect in real Nim exactly like a plain assignment —
        # resolve by true symbol identity, same as the plain-assign arm.
        let augCls = classifyType(lhs)
        let augTy = if augCls.ty.kind == itInt and augCls.ty.hasRange:
                      augCls.ty
                    else: nil
        return mkAssign(nm, mkBinop(bop, mkVar(nm), rhsIR), augTy)
      elif lhs.kind == nnkDerefExpr and lhs.len == 1 and
           augOp.strVal != "&=" and
           ((classifyType(lhs).ty.kind == itInt and
             not classifyType(lhs).ty.hasRange) or
            classifyType(lhs).ty.kind in {itFloat32, itFloat64}):
        # RFC-0005 S8an: `p[] += v` -- the read, the operation and the
        # write `p[] = p[] + v` (`parseAsgn`'s dereference arm), so a
        # `ptr` formal bound to an `addr` cell is updated in place. A
        # ranged pointee declines (the write has no RangeDefect fork).
        let old = parseExpr(lhs, preamble, ctx)
        let rhsIR = parseExpr(n[2], preamble, ctx)
        let newVal = mkBinop(binopForInfix(augOp.strVal[0 .. ^2]), old, rhsIR)
        return parseAsgn(nnkAsgn.newTree(lhs, newEmptyNode()), newVal,
                         preamble, ctx)
      else:
        # RFC-0005 S8p: `o.a += v` on a value tuple / object field -- the
        # same rebuilt-root write as `o.a = o.a + v` (`valueFieldWrite`).
        # `&=` needs a string field; a ranged int field declines (the
        # rebuilt write has no per-field RangeDefect fork).
        # RFC-0005 S8am: hoisted out of the `fieldTy != nil` branch below
        # so the seq-element arm further down (which `fieldTy` never
        # matches -- `valueFieldTy`/`fieldStep` has no `itSeq` case) can
        # read it too.
        let baseOpStr = augOp.strVal[0 .. ^2]
        let fieldTy = valueFieldTy(lhs)
        if fieldTy != nil:
          let fits =
            if baseOpStr == "&":
              fieldTy.kind == itString and classifyType(n[2]).ty.kind == itString
            else:
              (fieldTy.kind == itInt and not fieldTy.hasRange) or
                fieldTy.kind in {itFloat32, itFloat64}
          if fits:
            let old = parseExpr(lhs, preamble, ctx)
            let rhsIR = parseExpr(n[2], preamble, ctx)
            let newVal =
              if baseOpStr == "&": mkStrOp(iekStrConcat, "&", @[old, rhsIR])
              else: mkBinop(binopForInfix(baseOpStr), old, rhsIR)
            let fw = valueFieldWrite(lhs, newVal, preamble, ctx)
            return fw.toStmt
        # RFC-0005 S8am (S8z's remainder, item 1): `s[i] += v` (and -=, *=,
        # &=) on a SEQ ELEMENT. `valueFieldTy`/`fieldStep` has no `itSeq`
        # case -- a seq element is a REAL `isIndexAssign` store (a Z3
        # `store` into the seq's backing array), not a value chain rebuilt
        # root-to-leaf the way a tuple/object/array field is -- so it falls
        # through `fieldTy == nil` above and needs its own arm here, mirroring
        # `parseAsgn`'s plain `s[i] = v` `itSeq` arm (same receiver/element
        # gate) plus this proc's own array arm just above (same
        # read-old/build-new/write-back shape).
        #
        # Evaluation order (RFC-0005 S8z's remainder, item 2 -- probed
        # against real Nim: `s[5] += raiser()` raises `IndexDefect`, never
        # `raiser`'s exception): the index is parsed ONCE into `idxIR` and
        # reused for both the bounds-checked READ (`mkIndexStmt`, its result
        # discarded as `old`) and the final store (`mkIndexAssignStmt`) --
        # never re-parsed from the raw node, which would evaluate an
        # IMPURE index expression (one that calls a routine) twice. The
        # discarded `isIndex` read is emitted BEFORE the RHS (`n[2]`) is
        # parsed, so its `IndexDefect` fork lands in the preamble ahead of
        # any call the RHS makes — the same ordering fix the plain-assign
        # `itSeq` arm below applies for the same reason.
        if lhs.kind == nnkBracketExpr and lhs.len == 2:
          let seqRecv = unwrapHidden(lhs[0])
          if seqRecv.kind == nnkSym:
            let seqRecvCls = classifyType(seqRecv)
            if seqRecvCls.ty.kind == itSeq:
              let seqElemTy = seqRecvCls.ty.seqElemTy
              let seqFits =
                if baseOpStr == "&":
                  seqElemTy.kind == itString and
                    classifyType(n[2]).ty.kind == itString
                else:
                  (seqElemTy.kind == itInt and not seqElemTy.hasRange) or
                    seqElemTy.kind in {itFloat32, itFloat64}
              if seqFits:
                let idxIR = parseExpr(lhs[1], preamble, ctx)
                let checkSynth = freshSynth(ctx, "awck")
                preamble.add mkIndexStmt(checkSynth, mkVar(seqRecv.strVal),
                                         idxIR, seqElemTy, siteLoc(n))
                let old = mkVar(checkSynth)
                let rhsIR = parseExpr(n[2], preamble, ctx)
                let newVal =
                  if baseOpStr == "&": mkStrOp(iekStrConcat, "&", @[old, rhsIR])
                  else: mkBinop(binopForInfix(baseOpStr), old, rhsIR)
                return mkIndexAssignStmt(seqRecv.strVal, idxIR, newVal, siteLoc(n))
        # RFC-0005 S8bc (item 7): `a[i] += v` on an ARRAY element not
        # reached above, `t[k] += v` on a TABLE value, and `t.mgetOrPut(k,
        # d) += v` on the cell `mgetOrPut` returns a reference to -- the
        # S8at element arms' read / operate / write-back, with the write
        # through `t[k]` (`elemLvalueBracket`). The read is bound before the
        # right-hand side is parsed: `[]`'s `KeyError` (an absent key) and
        # `mgetOrPut`'s insert come first, as Nim takes the address first.
        # Declined before (this arm's final decline).
        if arrayElemLvalue(n[1]):
          let eltTy = classifyType(n[1]).ty
          let eltFits =
            if baseOpStr == "&":
              eltTy.kind == itString and classifyType(n[2]).ty.kind == itString
            else:
              (eltTy.kind == itInt and not eltTy.hasRange) or
                eltTy.kind in {itFloat32, itFloat64}
          if eltFits:
            let oldTmp = freshSynth(ctx, "augElt")
            preamble.add mkLet(oldTmp, eltTy, parseExpr(n[1], preamble, ctx))
            let rhsIR = parseExpr(n[2], preamble, ctx)
            let newVal =
              if baseOpStr == "&":
                mkStrOp(iekStrConcat, "&", @[mkVar(oldTmp), rhsIR])
              else: mkBinop(binopForInfix(baseOpStr), mkVar(oldTmp), rhsIR)
            return parseAsgn(nnkAsgn.newTree(elemLvalueBracket(n[1]),
                                             newEmptyNode()),
                             newVal, preamble, ctx)
        return ctx.declineMarker(
          feUnsupportedStmtKind, &"augmented assign: LHS `{n[1].repr}` is not a simple variable " &
          &"(kind={n[1].kind}); degrade to sxUnknown (sound, Invariant 3)")
    ctx.declineMarker(
      feUnsupportedStmtKind, &"augmented assign: operator `{n[0].repr}` not in supported set " &
      &"{{+=,-=,*=,&=}} or wrong AST shape (len={n.len}); " &
      &"degrade to sxUnknown (sound, Invariant 3)")
  of routineShapedForClosureDetect:
    # RFC-0005 S8an. A routine declared inside the code under test does
    # nothing where it is declared: a call reaches its body through
    # `ensureProcRegistered` (a callee, with its captures threaded), and a
    # use as a value builds the closure (`parseProcAsValue`); an iterator
    # is inlined at its `for`, and a template or macro is already expanded
    # at its uses. It was `feUnsupportedStmtKind`, which tainted every path
    # past the declaration.
    mkBlock(@[])
  else:
    ctx.declineMarker(feUnsupportedStmtKind, &"statement kind {n.kind} not in supported fragment")

proc scanForHiddenMarkers(n: NimNode): seq[tuple[kind: string, name: string]] =
  ## Phase 14 cycle B67. Recursively scan a Nim sub-AST for
  ## `symexTarget(...)` / `symexAssert(...)` / `symexAssume(...)`
  ## calls so the parse-time diagnostic can list them when the
  ## statement they live in lands as `isUnsupported`. The IR scan
  ## can't see past `isUnsupported` (the body wasn't parsed), so
  ## this lives on the raw Nim AST.
  if n.isNil: return
  if n.kind in {nnkCall, nnkCommand}:
    if n.len >= 1 and n[0].kind in {nnkIdent, nnkSym}:
      let nm = n[0].strVal
      if nm in ["symexTarget", "symexAssert", "symexAssume"]:
        var arg = ""
        if n.len >= 2 and n[1].kind in {nnkStrLit..nnkTripleStrLit}:
          arg = n[1].strVal
        result.add (kind: nm, name: arg)
  for child in n: result.add scanForHiddenMarkers(child)

proc parseStmt*(n: NimNode, ctx: ParseCtx): IRStmt =
  # RFC-0005 S8m: a `while` and a `block` are jump targets while their
  # bodies parse (`resolveBreak` / `resolveContinue`); a block some `break`
  # names becomes a labelled `isBlock`.
  if n.kind in {nnkWhileStmt, nnkBlockStmt}:
    if n.kind == nnkWhileStmt:
      ctx.pushJumpTarget(isLoop = true)
    else:
      ctx.pushJumpTarget(isLoop = false,
        blockSym = (if n[0].kind in {nnkSym, nnkIdent}: n[0] else: nil))
    let body = parseStmtBare(n, ctx)
    let jt = ctx.popJumpTarget()
    return wrapJumpBlock(jt.brkLabel, body)
  parseStmtBare(n, ctx)

proc parseStmtBare(n: NimNode, ctx: ParseCtx): IRStmt =
  var preamble: seq[IRStmt]
  let inner = parseStmtInner(n, preamble, ctx)
  # Phase 14 B67. If a parse landed on `isUnsupported`, scan the
  # raw Nim sub-AST for symex markers and emit a {.hint.} for each
  # so the user knows their target/assert is invisible to the
  # analysis. Does NOT close Phase 12 deferral #3 — semantics are
  # unchanged; markers are still ignored — but observability is up.
  if inner != nil and inner.kind == isUnsupported:
    for m in scanForHiddenMarkers(n):
      let arg = if m.name.len > 0: "(\"" & m.name & "\")" else: "(...)"
      hint("symex: `" & m.kind & arg & "` is inside an unsupported " &
           "statement (" & inner.reason & ") and will NOT be " &
           "discovered by symex analysis", n)
  if preamble.len == 0:
    inner
  else:
    mkBlock(preamble & @[inner])

# ---- Untyped-friendly wrappers for the DSL isolation tests -------------------
#
# Phase 1's tsymex_phase1_dsl tests call `parseExpr(node)` / `parseStmt(node)`
# with no ctx. We preserve those signatures by creating a throwaway ctx.

proc parseExpr*(n: NimNode): IRExpr =
  var preamble: seq[IRStmt]
  let ctx = newParseCtx()
  let e = parseExpr(n, preamble, ctx)
  if preamble.len > 0:
    error("symex: isolation parseExpr cannot lift A-normalised calls; " &
          "the input contains a user-proc call which only the full " &
          "parseProc/parseStmt entry points handle.", n)
  e

proc parseStmt*(n: NimNode): IRStmt =
  parseStmt(n, newParseCtx())

# ---- Callee resolution -------------------------------------------------------

proc parseCalleeImpl(impl: NimNode, ctx: ParseCtx,
                     typeSubst: Table[string, NimNode] =
                       initTable[string, NimNode](),
                     instTy: NimNode = nil;
                     byRef: seq[ByRefSub] = @[]): ProcSig

# ---- Phase 15 G6: stdlib concept membership (trust boundary) ---------------
#
# Nim's standard type-class concepts are closed, statically-known sets of
# concrete types. We mirror them as a compile-time membership table so a
# concept-constrained generic instantiated at a NON-conforming concrete type
# emits `geConceptViolation` at parse time (Invariant 3 — never silent).
#
# TRUST BOUNDARY: this table covers ONLY the stdlib concepts below. A
# USER-DEFINED concept name is NOT in the table; `conformsToStdlibConcept`
# returns `true` (= "no violation to assert") for it, so the parse-time
# validator SKIPS it and TRUSTS the Nim semchecker, which already enforced the
# constraint at the call site before the macro saw the typed AST. From REAL
# Nim source the semchecker likewise guarantees stdlib-concept conformance, so
# the stdlib check here is belt-and-suspenders — it is the test-injectable
# Invariant-3 guard, and never fires on real source.

const
  someUnsignedIntTypes = ["uint", "uint8", "uint16", "uint32", "uint64"]
  someSignedIntTypes   = ["int", "int8", "int16", "int32", "int64"]
  someFloatTypes       = ["float", "float32", "float64"]
  # `SomeOrdinal` = signed ints + unsigned ints + char + bool + enums. We list
  # the closed scalar members; enum types are recognised structurally below.
  someOrdinalExtra     = ["char", "bool"]

proc stdlibConceptMembers(conceptName: string): seq[string] =
  ## The concrete type names that satisfy a stdlib type-class concept.
  ## Empty seq ⇒ `conceptName` is NOT a known stdlib concept (→ user-defined,
  ## trusted to the semchecker).
  case conceptName
  of "SomeUnsignedInt": @someUnsignedIntTypes
  of "SomeSignedInt":   @someSignedIntTypes
  of "SomeInteger":     @someSignedIntTypes & @someUnsignedIntTypes
  of "SomeFloat":       @someFloatTypes
  of "SomeNumber":      @someSignedIntTypes & @someUnsignedIntTypes &
                        @someFloatTypes
  of "SomeOrdinal":     @someSignedIntTypes & @someUnsignedIntTypes &
                        @someOrdinalExtra
  else:                 @[]

proc isStdlibConcept*(conceptName: string): bool =
  ## True iff `conceptName` is one of the stdlib type-class concepts G6
  ## validates. A `false` here means "trust the semchecker" (user concept).
  stdlibConceptMembers(conceptName).len > 0

proc isEnumTypeNode*(node: NimNode): bool =
  ## CR-15: structural recognition of user enum types. Returns true iff `node`
  ## is a typed AST node whose `getImpl` is an nnkTypeDef over an nnkEnumTy (and
  ## is not `bool`, which is enum-shaped but handled separately). Used by
  ## `conformsToStdlibConcept` to allow user enums for `SomeOrdinal` — Nim's
  ## semchecker already guarantees a `T: SomeOrdinal` call site is valid, and
  ## user enums ARE ordinal types (Nim's definition of SomeOrdinal explicitly
  ## includes enum types). This is purely a TRUST check (the semchecker already
  ## validated the constraint at the call site); adding structural detection just
  ## prevents a spurious `geConceptViolation` in the Invariant-3 guard.
  if node == nil: return false
  let sym = try:
    if node.kind in {nnkSym, nnkIdent}: node
    else: node.getTypeInst
  except: return false
  if sym.kind notin {nnkSym, nnkIdent}: return false
  let impl = try: sym.getImpl except: return false
  if impl.kind != nnkTypeDef or impl.len < 3: return false
  if impl[2].kind != nnkEnumTy: return false
  # Exclude `bool` — it is enum-shaped in the typed AST but is already in
  # someOrdinalExtra as an explicit member, so no special case needed for it.
  let nm = if sym.kind in {nnkSym, nnkIdent}: sym.strVal else: sym.repr
  nm != "bool"

proc conformsToStdlibConcept*(conceptName, resolvedTypeName: string): bool =
  ## The single conformance-check entry point used both by the parse-time
  ## validator (`parseCalleeImpl`) AND by the G6 negative test (which injects a
  ## non-conforming pair directly — there is NO `isGenericCall` IR node to
  ## malform, so this helper IS the real, test-reachable check).
  ##
  ## Returns:
  ##   * for a STDLIB concept: `true` iff `resolvedTypeName` is a member;
  ##   * for a USER-DEFINED (non-stdlib) concept: ALWAYS `true` — there is no
  ##     violation to assert (the semchecker already validated it). This is the
  ##     trust boundary made explicit.
  ##
  ## NOTE: for `SomeOrdinal` with a user enum type, see the call site in
  ## `parseCalleeImpl` — structural enum detection via `isEnumTypeNode` runs
  ## BEFORE this helper and short-circuits to `true` (no violation) when the
  ## resolved node is a user enum. This string-based overload thus never sees
  ## user enum names; the Invariant-3 guard remains intact for non-enum types.
  let members = stdlibConceptMembers(conceptName)
  if members.len == 0:
    return true   ## user-defined concept → trust the semchecker
  resolvedTypeName in members

proc monomorphize(node: NimNode, subst: Table[string, NimNode]): NimNode =
  ## Walk `node`, replacing `Ident "T"` references with the concrete
  ## type node when `T` is in the substitution map. Used to lower a
  ## generic proc body to its monomorphic form before parsing.
  if node.kind in {nnkIdent, nnkSym} and node.strVal in subst:
    return subst[node.strVal]
  if node.kind in {nnkEmpty} or node.len == 0:
    return node
  if node.kind == nnkSym:
    return node
  result = copyNimNode(node)
  for c in node:
    result.add monomorphize(c, subst)

type
  GenericParam* = tuple[name: string, isStatic: bool, constraint: NimNode]
    ## One generic parameter of a routine impl: its identifier, whether its
    ## constraint marks it `static[T]` (a compile-time-constant param whose
    ## VALUE the semchecker has already baked into the body — see
    ## `staticParamNames`'s doc comment for the consequence), and the raw
    ## constraint node itself. The constraint stays a raw node (an
    ## arbitrary type expression); only the identDefs walk that FINDS it is
    ## centralised here, not its shape.
  GenericDescriptor* = object
    params*: seq[GenericParam]   ## empty when `impl` is not generic (or is
                                  ## not a `walkableRoutineKinds` impl at all)

proc genericParamsNode(impl: NimNode): NimNode =
  ## The `nnkGenericParams` node of a generic `impl`, or `nil`. In the typed
  ## AST generic params live either in `impl[2]` (untyped form) or nested in
  ## `impl[5][1]` (typed form). RFC-parser-normalization C2: this dual-
  ## location lookup now lives in exactly one place repo-wide — this proc,
  ## whose ONLY caller is `resolveGenericDescriptor`. Every consumer that
  ## used to re-derive it independently (`staticParamNames`, `gatherTypeSubst`,
  ## `parseCalleeImpl`'s concept-constraint capture) now reads
  ## `resolveGenericDescriptor(impl).params` instead.
  if impl.kind notin walkableRoutineKinds: return nil
  if impl[2].kind == nnkGenericParams: return impl[2]
  if impl[5].kind == nnkBracket and impl[5].len >= 2 and
     impl[5][1].kind == nnkGenericParams: return impl[5][1]
  nil

proc resolveGenericDescriptor*(impl: NimNode): GenericDescriptor =
  ## RFC-parser-normalization N1/C2. Holds BOTH the `impl[2]`-vs-`impl[5][1]`
  ## dual-location lookup (via `genericParamsNode`) AND the single
  ## `nnkIdentDefs` walk (per-param name / isStatic / constraint). Every
  ## consumer — `hasGenericParams`, `staticParamNames`, `gatherTypeSubst`,
  ## and `parseCalleeImpl`'s concept-constraint capture — reads `params`
  ## instead of re-walking identDefs; the walk now exists in exactly one
  ## place repo-wide (C2 completes the threading N1 designed this for).
  result = GenericDescriptor(params: @[])
  let gp = genericParamsNode(impl)
  if gp == nil: return
  for idDefs in gp:
    if idDefs.kind != nnkIdentDefs: continue
    let constraint = idDefs[idDefs.len - 2]
    let isStatic =
      (constraint.kind == nnkStaticTy) or
      (constraint.kind == nnkCommand and constraint.len == 2 and
       constraint[0].kind in {nnkIdent, nnkSym} and
       constraint[0].strVal == "static")
    for i in 0 ..< idDefs.len - 2:
      result.params.add (name: idDefs[i].strVal, isStatic: isStatic,
                          constraint: constraint)

proc hasGenericParams(impl: NimNode): bool =
  ## True when `impl` carries generic params. Rebased on
  ## `resolveGenericDescriptor` (RFC-parser-normalization N1/C2) — the same
  ## descriptor `staticParamNames`, `gatherTypeSubst`, `parseCalleeImpl`, and
  ## (transitively, via `staticParamNames`) `instKeyFor` now all read; the
  ## dual-location lookup and the identDefs walk live in exactly one place
  ## repo-wide.
  resolveGenericDescriptor(impl).params.len > 0

proc staticParamNames(impl: NimNode): HashSet[string] =
  ## Phase 15 G7. The names of generic params whose CONSTRAINT is `static[T]`.
  ## In the typed generic-params AST the constraint surfaces as an
  ## `nnkCommand[Ident "static", <T>]` (probed on the typed AST — NOT the
  ## `nnkStaticTy` the RFC §G7 GREEN guessed; `nnkStaticTy` is the untyped /
  ## `static[int]`-bracket form, which we also accept defensively).
  ## RFC-parser-normalization C2: reads `isStatic` off the shared
  ## `resolveGenericDescriptor` instead of re-walking identDefs. `instKeyFor`
  ## is descriptor-backed transitively through this proc — it never
  ## re-derived generic-param structure directly.
  result = initHashSet[string]()
  for p in resolveGenericDescriptor(impl).params:
    if p.isStatic: result.incl p.name

proc gatherTypeSubst(callSite: NimNode, impl: NimNode): Table[string, NimNode] =
  ## RFC-parser-normalization N2: `impl` is always already resolved by the
  ## sole caller (`ensureProcRegistered`, via `resolveRoutineImpl`) — a
  ## membership-only check, so it routes onto `walkableRoutineKinds`.
  result = initTable[string, NimNode]()
  if impl.kind notin walkableRoutineKinds: return
  # RFC-parser-normalization C2: generic-param names come from the shared
  # `resolveGenericDescriptor` — the `impl[2]`/`impl[5][1]` dual-location
  # lookup and the identDefs walk that finds these names both live there now,
  # not re-derived here.
  var genericNames: HashSet[string]
  for p in resolveGenericDescriptor(impl).params:
    genericNames.incl p.name
  if genericNames.len == 0: return
  # Phase 15 G7: `static[T]` params (e.g. `N` in `proc foo[N: static int]`).
  # Their VALUE is a compile-time constant; Nim's semchecker has already baked
  # it into the proc BODY (`x[N-1]` → `x[2]`), so the body needs no further
  # substitution. The one un-substituted spot is a FORMAL param TYPE that names
  # the static param as an array DIMENSION (`array[N, int]`), which
  # `classifyType` cannot size until `N` resolves to a literal. We recover the
  # literal from the matching ARRAY ARG's range type below.
  let staticNames = staticParamNames(impl)
  proc staticValFromArrayArg(formalTy, argTy: NimNode, sname: string): NimNode =
    ## If `formalTy` is `array[<sname>, _]`, read the concrete dimension from
    ## `argTy` (`array[range[lo..hi], _]` after `getType`) and return it as an
    ## `nnkIntLit`; else nil.
    if formalTy.kind != nnkBracketExpr or formalTy.len != 3: return nil
    # RFC-0005 S8d: both the formal's head and the argument's must be the
    # builtin `array` -- a user generic named `array` has no index range.
    if not isBuiltinTypeHead(formalTy[0], ["array"]): return nil
    if not (formalTy[1].kind in {nnkIdent, nnkSym} and
            formalTy[1].strVal == sname): return nil
    if argTy.kind != nnkBracketExpr or argTy.len != 3 or
       not isBuiltinTypeHead(argTy[0], ["array"]): return nil
    let idx = argTy[1]
    # `getType` renders the index as `range[lo .. hi]` (a BracketExpr) or, in
    # some forms, a bare `lo .. hi` Infix.
    var lo, hi: NimNode = nil
    if idx.kind == nnkBracketExpr and idx.len == 3 and
       isBuiltinTypeHead(idx[0], ["range"]):
      lo = idx[1]; hi = idx[2]
    elif idx.kind == nnkInfix and idx.len == 3 and idx[0].strVal == "..":
      lo = idx[1]; hi = idx[2]
    if lo != nil and hi != nil and
       lo.kind in nnkIntLit..nnkInt64Lit and hi.kind in nnkIntLit..nnkInt64Lit:
      return newLit(int(hi.intVal - lo.intVal + 1))
    nil
  # Phase 15 G3: a formal type may WRAP the generic param in an ownership /
  # lvalue annotation — `var T`, `sink T`, `lent T`. The typed AST presents
  # these as `nnkVarTy[T]` or (for sink/lent) `nnkBracketExpr[sink|lent, T]`.
  # Unwrap them so the BARE generic name is recovered and `T` actually binds
  # (without this, `proc foo[T](x: sink T)` never records `T` and the body's
  # `T` references stay un-monomorphised → `classifyType` errors on `T`).
  proc unwrapGenericTy(n: NimNode): NimNode =
    if n.kind == nnkVarTy and n.len == 1:
      return unwrapGenericTy(n[0])
    # `sink T` / `lent T` present in the typed generic AST as an
    # `nnkCommand[sink|lent, T]` (NOT a bracket — see G3 AST dump); a
    # post-substitution form may also surface as `nnkBracketExpr`.
    if n.kind in {nnkBracketExpr, nnkCommand} and n.len == 2 and
       isBuiltinTypeHead(n[0], ["sink", "lent"]):   ## RFC-0005 S8d
      return unwrapGenericTy(n[1])
    n
  let formal = impl[3]
  # Walk formal params, matching to call args
  var argIx = 1   ## skip n[0] = callee
  for i in 1 ..< formal.len:
    let id = formal[i]
    let rawTy = id[id.len - 2]
    let tyNode = unwrapGenericTy(rawTy)
    for j in 0 ..< id.len - 2:
      if argIx < callSite.len:
        let argTy = callSite[argIx].getType
        if tyNode.kind in {nnkIdent, nnkSym} and tyNode.strVal in genericNames:
          result[tyNode.strVal] = argTy
        else:
          # Phase 15 G7: a STATIC param used as an array dimension
          # (`array[N, int]`). Bind `N` to its concrete literal so
          # `monomorphize` rewrites the formal to `array[3, int]` (which
          # `classifyType` can size) and any residual body `N` to the literal.
          for sname in staticNames:
            let v = staticValFromArrayArg(rawTy, argTy, sname)
            if v != nil:
              result[sname] = v
      inc argIx
  # RFC-0005 S8at: a generic name no argument binds -- one only the RETURN
  # type mentions (`proc mk[T](): seq[T]`, the stdlib's `initTable[A, B]()`)
  # -- is bound from the call's own instantiated type, matched structurally
  # against the formal return type. Unbound, the return formal stayed
  # generic, no instance type was handed to `parseCalleeImpl` (`typeSubst`
  # was empty), and `classifyType` aborted macro expansion on the untyped
  # formal ("node has no type").
  proc bindFromReturn(f, a: NimNode; acc: var Table[string, NimNode]) =
    if f.kind in {nnkIdent, nnkSym} and f.strVal in genericNames:
      if f.strVal notin acc: acc[f.strVal] = a
    elif f.kind == nnkBracketExpr and a.kind == nnkBracketExpr and
         f.len == a.len:
      for i in 1 ..< f.len: bindFromReturn(f[i], a[i], acc)
  if formal.len > 0 and formal[0].kind != nnkEmpty and
     callSite.typeKind notin {ntyNone, ntyVoid}:
    bindFromReturn(unwrapGenericTy(formal[0]), callSite.getTypeInst, result)

proc bodyHashPart(calleeSym, impl: NimNode): string =
  ## Module-disambiguating stable identity for a proc body (ADR-0008 D2).
  ## `symBodyHash` encodes the full module path + body identity, so two
  ## same-named procs in different modules hash differently. The `lineInfo`
  ## fallback (file path + proc name) preserves module disambiguation when
  ## `symBodyHash` is unavailable/empty; it is NOT `repr.hash` (structurally
  ## ambiguous across modules — ADR-0008 Alt 2).
  if calleeSym.kind == nnkSym:
    let h = symBodyHash(calleeSym)
    if h.len > 0: return h
  impl.lineInfoObj.filename & ":" & calleeSym.strVal

proc instKeyFor(calleeSym: NimNode, typeSubst: Table[string, NimNode],
                impl: NimNode): string =
  ## The instantiation key under which a (callee, concrete-type-tuple) pair is
  ## registered in `ctx.procs` AND dispatched by the walker (`mkCall` callee
  ## name). Registration and dispatch MUST compute this identically, so both
  ## go through THIS one proc.
  ##
  ## Non-generic procs (empty `typeSubst`) → bare proc name, preserving the
  ## pre-G1a behavior exactly. Generic procs → `name#<bodyHash>#<typeTuple>`
  ## where the type tuple is sorted by formal-param name (ADR-0008 D2/D6:
  ## order-independent canonical identity) so two instantiations at the same
  ## types share one entry, and two instantiations at DIFFERENT types do not
  ## collide on the bare name (the G1a bug).
  ##
  ## Phase 15 G7: a `static[T]` param's VALUE is part of the instantiation
  ## identity, so two static instantiations (`foo[3]`/`foo[5]`) must NOT share
  ## a key. When the static value is bound as an array dimension it is already
  ## in `typeSubst` (`N=3` vs `N=5` → distinct type tuples). When it is a
  ## SCALAR static param (`bar[N: static int](x:int)` / `gate[B: static bool]`)
  ## it appears in NO formal-type position, so `typeSubst` stays EMPTY — but
  ## Nim instantiates each value as a DISTINCT symbol whose `symBodyHash`
  ## differs (the literal is baked into the body), so we discriminate on that
  ## bodyHash. RECONCILIATION NOTE: the RFC §G7 asserts the exact key string
  ## `"foo#int;static=3"`; the REAL key carries a per-instantiation `bodyHash`
  ## (`name#<bodyHash>#<tuple>` or `name#<bodyHash>#static`), so the test asserts
  ## BEHAVIOR (distinct dispatch + per-instantiation literal), not that string.
  let name = calleeSym.strVal
  if typeSubst.len == 0:
    if staticParamNames(impl).len > 0:
      # Scalar static param: force a per-instantiation-distinct, non-bare key.
      return name & "#" & bodyHashPart(calleeSym, impl) & "#static"
    # RFC-0005 S8an: a routine declared inside another is keyed by its
    # declaration site. Two nested routines of one spelling (`h` inside
    # `a`, another `h` inside `b`) are different routines -- the bare name
    # dispatched both calls to whichever registered first.
    if isNestedRoutine(calleeSym):
      return name & "#" & nestedSiteKey(calleeSym, impl)
    return name
  var keys: seq[string]
  for k in typeSubst.keys: keys.add k
  keys.sort()
  var parts: seq[string]
  for k in keys:
    parts.add k & "=" & typeSubst[k].repr
  name & "#" & bodyHashPart(calleeSym, impl) & "#" & parts.join(";")

proc conceptViolationMsg(impl: NimNode;
                         typeSubst: Table[string, NimNode]): string =
  ## Phase 15 G6, hoisted by RFC-0005 S8 out of `parseCalleeImpl` so the
  ## decline is decided before registration (`ensureProcRegistered`). For
  ## each generic param constrained by a STDLIB concept whose resolved
  ## concrete type (from `typeSubst`) does not conform, one diagnostic line;
  ## "" when every binding conforms. USER-DEFINED concepts are trusted to the
  ## semchecker (`isStdlibConcept` is false for them).
  var parts: seq[string]
  for p in resolveGenericDescriptor(impl).params:
    if p.constraint.kind == nnkEmpty: continue
    let constraintName =
      if p.constraint.kind in {nnkIdent, nnkSym}: p.constraint.strVal
      else: p.constraint.repr
    if p.name in typeSubst and isStdlibConcept(constraintName):
      let resolvedNode = typeSubst[p.name]
      let resolved = resolvedNode.repr
      # CR-15: a user enum satisfies `SomeOrdinal` structurally (the
      # semchecker validated it); flagging it would be a spurious decline.
      let isOrdinalEnum = constraintName == "SomeOrdinal" and
                          isEnumTypeNode(resolvedNode)
      if not isOrdinalEnum and
         not conformsToStdlibConcept(constraintName, resolved):
        parts.add "generic param `" & p.name & "` of proc `" &
                  impl.name.strVal & "` is constrained by stdlib concept `" &
                  constraintName & "` but was instantiated at non-conforming " &
                  "type `" & resolved & "` — result is sxUnknown (Invariant 3)"
  parts.join("; ")

proc ensureProcRegistered(ctx: ParseCtx, calleeSym: NimNode,
                          callSite: NimNode = nil;
                          byRef: seq[ByRefSub] = @[]): string =
  ## Registers the (monomorphized) callee under its instantiation key and
  ## returns that key. The CALLER must use the returned key as the `mkCall`
  ## callee name so the walker's `w.procs[stmt.callee]` dispatch lands on the
  ## exact `ProcSig` registered here (G1a: registration and dispatch share one
  ## key).
  ## RFC-0005 S8ba: with `byRef`, the callee is registered specialised to
  ## those by-reference formals (`ByRefSub`), under its own key.
  if calleeSym.kind notin {nnkSym, nnkIdent}:
    error("symex Phase 3: callee position is not a symbol — got " &
          $calleeSym.kind & " in `" & calleeSym.repr & "`", calleeSym)
  let name = calleeSym.strVal
  var impl = resolveRoutineImpl(calleeSym)  ## RFC-parser-normalization N2
  if impl == nil:
    # v67 (§0 clause (b), dev item 1): this was a macro-time `error()` —
    # the LAST compile wall on the natural seq-slice value path
    # (`getImpl`-inlining system's `[]` died here on its `len` callee).
    # CR-2a-style classified degrade instead: record the parse error
    # (sevError, anchored at the key; RFC-0005 S9 counts it only if a walked
    # path reaches the call -- was the whole-run `capForcedUnknown`) and return a
    # synthetic key that is never registered, so the walker's
    # missing-callee arm degrades the path (exactly the geDistinctBarrier
    # / over-cap-instantiation precedent above and below).
    # RFC-0005 S1b: the never-registered key encodes this decline's kind, so
    # the walker's missing-callee arm records it at the walk site.
    # RFC-0005 S8: `declineCallee` anchors the record at that same key.
    return ctx.declineCallee(feUnsupportedOp,
      "cannot resolve `getImpl` for callee `" & name &
      "` (generic / private cross-module / built-in / func) — call " &
      "degraded to sxUnknown (feUnsupportedOp)", name)
  # RFC-0005 S8bl (item 1). A system magic with a `var` parameter that no
  # parser arm modelled. Its semantics are the compiler's; its body is empty
  # (or documentation, or a VM fallback), so registering it walked a no-op:
  # the write to the argument was dropped without a record (`swap`, a
  # string's `setLen`, `add` to a seq element: false sxSat), or the
  # monomorphised magic's formals crashed `parseCalleeImpl` (`wasMoved`,
  # `move`). It declines, naming the magic.
  block:
    let magic = implMagic(impl)
    if magic.len > 0 and hasVarFormal(impl):
      return ctx.varMagicDecline(name, magic, name & "#varMagic")
    if isGeneratedHook(calleeSym):
      return ctx.declineCallee(feUnsupportedOp,
        "compiler-generated lifetime hook `" & name & "` is not modelled " &
        "here -- path degraded to sxUnknown (feUnsupportedOp)",
        name & "#hook")
  # Phase 15 G5. `geDistinctBarrier` (Invariant 3 — never a silent fallback). A
  # NON-borrowed proc taking a `distinct T` param whose body is NOT parseable
  # (`impl[6] == nnkEmpty`, e.g. an `{.importc.}` / magic on a distinct type)
  # cannot be walked: the type wall forbids silently treating the distinct value
  # as its base. (A `{.borrow.}` op IS routed through the borrow path at parse
  # time and never reaches `ensureProcRegistered`, so this fires only for the
  # genuine no-borrow, no-body case.) Emit `geDistinctBarrier` (sevError) and do
  # NOT register — the call's `mkCall` key is absent from `w.procs`, so the
  # walker's missing-callee arm degrades the path to sxUnknown, and the sevError
  # forces the verdict to sxUnknown (never silent).
  if impl[6].kind == nnkEmpty and not hasBorrowPragma(impl):
    let distinctParam = distinctParamOf(impl)
    if distinctParam.len > 0:
      # RFC-0005 S1b: kind-encoding unregistered key (see `types.nim`);
      # RFC-0005 S8: the record is anchored at that key (`declineCallee`).
      return ctx.declineCallee(geDistinctBarrier,
        "proc `" & name & "` operates on distinct type `" & distinctParam &
        "` with no parseable body and no `{.borrow.}` pragma — the " &
        "distinct type wall forbids walking it (Invariant 3); result is " &
        "sxUnknown",
        instKeyFor(calleeSym, initTable[string, NimNode](), impl))
  # Detect generic procs. In typed AST, the generic-params live in
  # impl[2] (untyped) or nested in impl[5] (typed). Either way, we
  # use the call's `getType` reads to derive the substitution.
  var typeSubst: Table[string, NimNode]
  if hasGenericParams(impl) and callSite != nil:
    typeSubst = gatherTypeSubst(callSite, impl)
  var key = instKeyFor(calleeSym, typeSubst, impl)
  # RFC-0005 S8an: a non-generic callee's key is its bare name, so two
  # overloads (`ov(int)`, `ov(string)`) shared one registration and every
  # call ran the first one's body -- a silent wrong verdict. A different
  # symbol under a key already taken gets its own (`#<bodyHash>#ovl`); the
  # first keeps the bare name, so a program without overloads is keyed as
  # before.
  if calleeSym.kind == nnkSym and key == name:
    if ctx.keySyms.hasKey(key) and
       not containsSym(@[ctx.keySyms[key]], calleeSym):
      key = name & "#" & bodyHashPart(calleeSym, impl) & "#ovl"
    if not ctx.keySyms.hasKey(key): ctx.keySyms[key] = calleeSym
  # RFC-0005 S8ba: a by-reference specialisation is its own routine, keyed
  # by the formals it replaces and the shape of each lvalue (its base type
  # and field path), not by the caller's variable. A recursive call that
  # passes the same shape on reaches this key while it is being parsed.
  # RFC-0005 S8bd: the key of a generic callee's specialisation extends its
  # instantiation's key, so each instantiation has its own; its body is
  # specialised after monomorphisation (`parseCalleeImpl`).
  if byRef.len > 0:
    for b in byRef: key.add "#byref" & $b.idx & ":" & b.keyPart
    if key notin ctx.procs and key notin ctx.parsing and typeSubst.len == 0:
      impl = substByRefImpl(impl, byRef)
  if key in ctx.procs or key in ctx.parsing:
    return key  ## already known, or actively being parsed (mutual-recursion)
  # Phase 15 G6 / RFC-0005 S8 (§2.5 point 3). A stdlib-concept violation is
  # decided HERE, before registration, so the violating instantiation is
  # never registered: its record is anchored at the never-registered key the
  # walker's missing-callee arm reaches (`declineCallee`). Before S8 the
  # check ran inside `parseCalleeImpl`, AFTER the callee was already being
  # registered -- the record named a key the walker could call, i.e. no
  # anchor at all.
  let conceptMsg = conceptViolationMsg(impl, typeSubst)
  if conceptMsg.len > 0:
    return ctx.declineCallee(geConceptViolation, conceptMsg, key)
  # Phase 15 G1c (ADR-0008 D7 / OQ5): per-BASE-proc instantiation cap. Every
  # DISTINCT instantiation of ONE generic proc shares a counter (keyed by the
  # generic's definition site, below) while different generic procs count
  # independently. A non-generic proc has exactly one instKey (empty typeSubst)
  # and trivially never exceeds the cap.
  let cap = ctx.maxInstantiationsPerProc
  # RFC-0005 S8ba: a by-reference specialisation of a non-generic routine is
  # not an instantiation. RFC-0005 S8bd: one of a generic routine is (its
  # own body, registered once per instantiation and lvalue shape), and
  # counts against the cap.
  if cap > 0 and (byRef.len == 0 or typeSubst.len > 0):
    # Base-proc identity must be STABLE across instantiations of the SAME
    # generic, so the per-proc counter actually accumulates. `symBodyHash`
    # (used by `bodyHashPart` for the instKey) is per-INSTANTIATION (each
    # monomorphized `szof[int8]`/`szof[int16]` symbol hashes differently), so
    # it CANNOT key the base count. The generic's DEFINITION site —
    # `lineInfoObj` (file:line:column) — is invariant across instantiations
    # (verified: all three `szof` calls report the one `szof[T]` def line) and
    # is module-disambiguating (the file path differs across modules), so it is
    # the correct base identity. Proc name is included for readability.
    let li = impl.lineInfoObj
    let baseId = name & "#" & li.filename & ":" & $li.line & ":" & $li.column
    let prior = ctx.instCounts.getOrDefault(baseId, 0)
    if prior >= cap:
      # Over-cap: do NOT register this instantiation. The call site still emits
      # `mkCall` with `key`, which is absent from `w.procs`, so the walker's
      # missing-callee arm sets `w.sawUnknown = true` → sxUnknown. We attach a
      # `geInstantiationCapped` (sevError) so the unknown is never silent
      # (Invariant 3). `observedCount`/`procSym` live in `msg` (the
      # `SymexErrorInfo` record carries no dedicated fields for them).
      # RFC-0005 S1b: kind-encoding unregistered key (see `types.nim`), so
      # the walker's missing-callee arm records `geInstantiationCapped` at
      # the walk site instead of a kindless taint. RFC-0005 S8: the parse
      # record is anchored at that same key (`declineCallee`).
      return ctx.declineCallee(geInstantiationCapped,
        "generic proc `" & name & "` exceeded maxInstantiationsPerProc=" &
        $cap & " (observedCount=" & $(prior + 1) & "); instantiation `" &
        key & "` not registered — result is sxUnknown", key)
    ctx.instCounts[baseId] = prior + 1
  ctx.parsing.incl key
  # D4 (design finding, accepted): every field of `ctx.procScoped` — a
  # `ProcScopedCollectors` (see its own doc comment beside `ParseCtx`) —
  # gets the EXACT SAME save/clear/restore treatment around a callee's
  # recursive body parse, for the same reason in every case: each field is
  # populated (either via a pre-pass collector, or via ordinary push/pop
  # during the body walk — `caseNarrow`'s own idiom) for whichever ONE proc
  # body is currently being walked, and consulted only during THAT proc's
  # own walk. Left unscoped, a caller's ambient value would leak into an
  # unrelated callee parsed here — `caseNarrow` NEVER leaking across a proc
  # boundary is ADR-0029's own recorded invariant; `stringBackedParams`/
  # `intOffsetLiteralLocals` leaking this way is exactly Round-6 R4's W1
  # (High, cross-proc leak) finding (a callee whose OWN formal happens to
  # share a name with one of the entry's qualifying params/locals — chapulin's
  # own corpus: every SUT names its receiver `data` — would inherit that
  # classification by bare name collision, bypassing the callee's own
  # vetting, including the mutation veto / W2's crash route);
  # `pairLoopCounterConsumedAfter` leaking this way is Round-6 R5's finding
  # S4, fixed with the same discipline from the start. None of this
  # interferes with B7r's DELIBERATE one-level call-trace promotion: that
  # promotion composes into the ENTRY's OWN `stringBackedParams` value
  # BEFORE the entry's body walk ever begins
  # (`collectStringBackedByteSeqParamsImpl`'s static analysis of the
  # callee's NimNode shape, entirely independent of `ctx`); what this
  # scoping guards is the AMBIENT CONSULT during the live recursive PARSE
  # below, a different mechanism entirely — "deliberate promotion via the
  # trace" vs "accidental inheritance via ambient state". Grouping every
  # proc-scoped collector into the one `procScoped` sub-record turns this
  # into a single save/clear/restore: a NEW proc-scoped collector joins by
  # becoming a field of `ProcScopedCollectors` and is automatically covered
  # here — there is no separate five-touchpoint save/restore line for it to
  # omit.
  # RFC-0005 S8x: a `var`, not a `let`. In the compile-time VM a `let` of
  # `ctx.procScoped` aliases the record, which the callee's parse fills in
  # place; only the whole-record reset below detached it. A `var` copies.
  var savedProcScoped = ctx.procScoped
  ctx.procScoped = ProcScopedCollectors()
  # RFC-0005 S8e: a callee runs in its own env frame, so it is its own
  # naming scope -- claimed before `parseCalleeImpl`'s pre-passes read a
  # name, discarded (with its renames) once its IR is built.
  # RFC-0005 S8an: a routine declared inside another reaches the enclosing
  # variables it captures (`ProcSig.captures`), named as the enclosing scope
  # names them (computed before the callee's scope opens; it would inherit
  # the same renames). Its own locals and parameters keep clear of those
  # names, so the walker can copy them into the callee's env.
  let captures = nestedCaptureNames(calleeSym, resolveRoutineImpl(calleeSym))
  let savedNames = enterNameScope()
  reserveScopedNames(captures)
  claimRoutine(impl)
  # RFC-0005 S8e: the call site's callee symbol is the generic INSTANCE; its
  # own proc type carries the instantiated formals as typed nodes (see
  # `instantiatedFormalTypes`).
  # RFC-0005 S8bc: a callee's body is parsed outside any borrowed call's
  # argument views (a node of the callee spelled like the caller's argument
  # is not that argument).
  # Swapped out, not `let`-copied: a compile-time `let` of a global seq
  # aliases it in the VM, so the `setLen 0` emptied the saved views too
  # (`vm_alias_guard`, RFC-0005 S8ab).
  var savedViews: seq[tuple[node: NimNode, baseTy: NimNode]]
  swap(savedViews, borrowBaseViews)
  var sig = parseCalleeImpl(impl, ctx, typeSubst,
    if typeSubst.len > 0 and calleeSym.kind == nnkSym: calleeSym.getTypeInst
    else: nil, byRef)
  swap(savedViews, borrowBaseViews)
  sig.captures = captures
  # RFC-0005 S8ba: each by-reference formal's slot holds the ref its lvalue
  # is reached through, under the name the specialised body reads.
  for b in byRef:
    if b.idx < sig.params.len:
      sig.params[b.idx] = IRParam(name: b.name, ty: b.baseTy)
  leaveNameScope(savedNames)
  ctx.procScoped = savedProcScoped
  ctx.procs[key] = sig
  ctx.parsing.excl key
  key

proc instantiatedFormalTypes(instTy: NimNode): tuple[params: seq[NimNode], ret: NimNode] =
  ## RFC-0005 S8e. The typed formal types of a generic INSTANCE, flattened one
  ## per parameter in declaration order, from the instance symbol's own proc
  ## type (`calleeSym.getTypeInst`). Empty when `instTy` is not a proc type.
  if instTy == nil or instTy.kind != nnkProcTy or instTy.len == 0 or
     instTy[0].kind != nnkFormalParams:
    return
  let f = instTy[0]
  result.ret = f[0]
  for i in 1 ..< f.len:
    let id = f[i]
    if id.kind != nnkIdentDefs: continue
    for j in 0 ..< id.len - 2: result.params.add id[id.len - 2]

proc typedFormal(mono, inst: NimNode): NimNode =
  ## RFC-0005 S8e (the `classifyType` "node has no type" crash). A STRUCTURED
  ## generic formal -- `openArray[T]`, `seq[T]`, `var seq[T]` -- is a tree
  ## `monomorphize` rebuilt: it used to come back with no type at all (and
  ## `classifyType`'s `getTypeInst` aborted macro expansion on it), and even
  ## with node types kept it carries the GENERIC declaration's type, not the
  ## instance's. A leaf is either untouched or replaced by an already-typed
  ## instance node. `x in s` / `s.add x` over a user alias of `seq` reach the
  ## stdlib generic `contains`/`add`, whose first formal is `openArray[T]` /
  ## `var seq[T]`. The instance's own typed formal is that type as
  ## instantiated, so it is classified instead -- its real model, or the
  ## recorded decline its shape already gets.
  ##
  ## RFC-0005 S8at: an EMPTY formal type -- a parameter declared by its
  ## default alone, `newSeq[T](len = 0.Natural)` -- is the instance's typed
  ## formal too. It was classified empty (the same "node has no type" abort)
  ## once a generic bound only by its return type reached here.
  if inst != nil and inst.kind != nnkEmpty and
     mono.kind notin {nnkSym, nnkIdent}:
    inst
  else:
    mono

proc parseCalleeImpl(impl: NimNode, ctx: ParseCtx,
                     typeSubst: Table[string, NimNode] =
                       initTable[string, NimNode](),
                     instTy: NimNode = nil;
                     byRef: seq[ByRefSub] = @[]): ProcSig =
  ## Build a `ProcSig` from a callee's `nnkProcDef`. Recursively parses
  ## the body; the parsing-set in `ctx` short-circuits mutual recursion.
  ## For generic procs, `typeSubst` carries `T → concreteTypeNode`
  ## bindings; types and the body are monomorphised before parsing.
  ## RFC-parser-normalization N2: `impl` is always already resolved by the
  ## sole caller (`ensureProcRegistered`, via `resolveRoutineImpl`) — a
  ## membership-only assertion, so it routes onto `walkableRoutineKinds`.
  impl.expectKind walkableRoutineKinds
  var monoImpl = if typeSubst.len > 0: monomorphize(impl, typeSubst)
                 else: impl
  # RFC-0005 S8bd: a generic callee is specialised to its by-reference
  # formals (`ByRefSub`) once monomorphised, so the lvalue the caller
  # passes (already concrete) is not rewritten with the type parameters.
  if byRef.len > 0 and typeSubst.len > 0:
    monoImpl = substByRefImpl(monoImpl, byRef)
  # Phase 15 G6: capture concept constraints + validate stdlib conformance.
  # `resolveGenericDescriptor(impl)` (RFC-parser-normalization C2) resolves
  # each param on the ORIGINAL (pre-monomorphize) impl. For each param whose
  # constraint node is NOT `nnkEmpty` (i.e. `T: SomeConcept`), record the
  # constraint sym name; then, for STDLIB concepts, validate the RESOLVED
  # concrete type bound to that param (from `typeSubst`) against the membership
  # table. A non-conforming binding → `geConceptViolation` (sevError) into
  # `ctx.parseErrors` (G1c/G5 plumbing → sxUnknown). USER-DEFINED concepts are
  # trusted to the semchecker (`conformsToStdlibConcept` returns true for them).
  var conceptConstraints: seq[string]
  block captureConstraints:
    # RFC-parser-normalization C2: the `impl[2]`/`impl[5][1]` dual-location
    # lookup and the identDefs walk both live in `resolveGenericDescriptor`
    # now; this block only consumes the per-param constraint node it hands
    # back (on the ORIGINAL, pre-monomorphize `impl`, same as before).
    for p in resolveGenericDescriptor(impl).params:
      if p.constraint.kind == nnkEmpty: continue   ## bare `T` — no constraint
      # The constraint may be a single sym (`SomeNumber`) or a compound the
      # semchecker already elaborated (`A and B` → nnkInfix). We capture the
      # constraint's textual form and, for a single stdlib-concept sym, validate.
      let constraintName =
        if p.constraint.kind in {nnkIdent, nnkSym}: p.constraint.strVal
        else: p.constraint.repr
      conceptConstraints.add constraintName
      # RFC-0005 S8: stdlib-conformance validation moved to
      # `conceptViolationMsg`, run by `ensureProcRegistered` BEFORE
      # registration -- a non-conforming instantiation never reaches here.
  let formal = monoImpl[3]
  formal.expectKind nnkFormalParams
  # Round-6 B5 (ADR-0028 Leg 1, chained composition): `parseProc*`'s
  # TOP-LEVEL entry-proc params get this same `collectIntOffsetParams`
  # marking (its own doc comment above); a CALLEE parsed here never did —
  # so a scan-lifted callee's OWN `offset` param stayed the type-driven BV
  # default whenever THIS parse (not the top-level entry's own
  # one-call-boundary trace) is the one that owns the marking, e.g. a
  # LITERAL call argument (`readCStringHelper(s, 0)`), which the
  # `intLitProto`-shaping call-argument lowering site (`runtime.nim`)
  # consults per-formal via `isIntOffset` alongside this fix.
  let intOffsetParams = collectIntOffsetParams(monoImpl)
  # Round-6 R4 (W1 fix, corrected — TDD RED caught this): a callee's OWN
  # string-backed/int-offset-literal classification must be RECOMPUTED
  # here, scoped to `monoImpl` (this callee's own, now-monomorphized body)
  # — `ensureProcRegistered`'s save/CLEAR/restore of these two ctx fields
  # (mirroring `caseNarrow`'s discipline) is necessary but NOT sufficient:
  # unlike `caseNarrow` (rebuilt fresh via ordinary push/pop DURING the
  # normal recursive body walk, for every proc alike), `stringBackedParams`/
  # `intOffsetLiteralLocals` are populated by a SEPARATE PRE-PASS that must
  # be explicitly invoked — `parseProc*` already does this for the
  # top-level entry, immediately before its own body walk; a callee parsed
  # here needs the SAME pre-pass run on ITS OWN (monomorphized) body below,
  # or its own genuinely-qualifying scan/pair-loop receiver never gets the
  # closed-form treatment at all — `scanReceiverOk`/`receiverIsStringBacked`
  # consult `ctx.procScoped.stringBackedParams` during the body walk just below
  # exactly like the entry's own walk does, and a cleared-to-empty set
  # (this proc's caller, `ensureProcRegistered`, clears it defensively
  # before calling here) would silently degrade every callee's own
  # closed-form scan to the k-unroll fallback. Scoped by
  # `ensureProcRegistered`'s save/restore around this whole call.
  ctx.procScoped.stringBackedParams = collectStringBackedByteSeqParams(monoImpl)
  ctx.procScoped.intOffsetLiteralLocals = collectIntOffsetLiteralLocals(monoImpl)
  ctx.procScoped.assumedBoundVars = collectAssumedBoundVars(monoImpl)
  # Round-6 R5 (finding S4, walker v93): same recompute-per-callee discipline
  # as the two collectors just above — a pair-loop can appear in a callee's
  # own body too, not just the top-level entry.
  ctx.procScoped.pairLoopCounterConsumedAfter = collectPairLoopCounterConsumedAfter(monoImpl)
  # Params
  var params: seq[IRParam]
  let inst = instantiatedFormalTypes(instTy)   ## RFC-0005 S8e
  var flatIx = 0
  for i in 1 ..< formal.len:
    let id = formal[i]
    id.expectKind nnkIdentDefs
    var tyNode = typedFormal(id[id.len - 2],
      if flatIx < inst.params.len: inst.params[flatIx] else: nil)
    # RFC-0005 S8at: a parameter declared by its default alone, with no
    # instance formal to read (a non-generic callee): its default's type.
    if tyNode.kind == nnkEmpty and id[id.len - 1].kind != nnkEmpty and
       id[id.len - 1].typeKind != ntyNone:
      tyNode = id[id.len - 1].getTypeInst
    let cls = classifyType(tyNode)
    let isVar = tyNode.kind == nnkVarTy
    flatIx += id.len - 2
    for j in 0 ..< id.len - 2:
      params.add IRParam(name: id[j].strVal, ty: cls.ty,
                         rangeLo: cls.range.lo,
                         rangeHi: cls.range.hi,
                         hasRange: cls.range.hasRange,
                         isVar: isVar,
                         isIntOffset: id[j].strVal in intOffsetParams)
  # Return type
  var retTy = tBool()
  var isVoid = true
  if formal[0].kind != nnkEmpty:
    let cls = classifyType(typedFormal(formal[0], inst.ret))   ## RFC-0005 S8e
    retTy = cls.ty
    isVoid = false
  else:
    # Phase 15 G3 auto-return guard. A monomorphised proc whose return node is
    # `nnkEmpty` is ordinarily a genuine `void` proc. But if the ORIGINAL impl
    # DECLARED a (generic / `auto`) return type that vanished to `nnkEmpty`
    # under substitution, that is a type-substitution FAILURE — Nim's
    # semchecker resolves `auto` to a concrete type before `getImpl`, so a
    # surviving `nnkEmpty` means the resolution did not happen and a default
    # would be unsound (Invariant 3 — never silently fall back). Error cleanly
    # instead of treating it as `void`. (Defensive: not expected to fire under
    # the current semcheck-then-getImpl pipeline.)
    if impl[3].kind == nnkFormalParams and impl[3][0].kind != nnkEmpty:
      error("symex G3: type-substitution produced nnkEmpty retTy for proc `" &
            impl[0].repr & "` (declared return `" & impl[3][0].repr &
            "` did not resolve to a concrete type under monomorphization)",
            impl)
  # Body. Value-returning Nim procs of the form
  #
  #     proc f(...): T = expr
  #
  # semcheck to `result = expr`. We detect this single-assignment-to-
  # result shape and rewrite as `return expr` so the runtime walker
  # doesn't need to model `result` as a mutable local for cycle 1.
  # Procs with conditional / multi-step result-assignment land via
  # the general parser path (parseStmt below) — those cases need
  # cycle-2 work to model `result` as a mutable binding.
  let bodyNode = monoImpl[6]
  proc resultRhs(n: NimNode): NimNode =
    ## If `n` is a single `result = expr` assignment (possibly wrapped
    ## in a one-element nnkStmtList), return the expr; else nil.
    let inner = if n.kind == nnkStmtList and n.len == 1: n[0] else: n
    if inner.kind == nnkAsgn and
       inner[0].kind == nnkSym and inner[0].strVal == "result":
      inner[1]
    else:
      nil
  let rhs = if isVoid: nil else: resultRhs(bodyNode)
  let body =
    if rhs != nil:
      # `proc f(...): T = expr` shape: rewrite as `return expr`.
      var preamble: seq[IRStmt]
      let valIR = parseExpr(rhs, preamble, ctx)
      if preamble.len == 0:
        mkReturnVal(valIR)
      else:
        # Phase 15 G7: the single-expr RHS A-normalised into preamble
        # statements (e.g. an array index `x[N-1]` lifts a bounds-checked
        # element read). Emit the preamble before the return rather than
        # asserting it away — the value is still `valIR`.
        mkBlock(preamble & @[mkReturnVal(valIR)])
    else:
      parseStmt(bodyNode, ctx)
  let nameStr = monoImpl.name.strVal
  ProcSig(name: nameStr, params: params, body: body,
          retTy: retTy, isVoid: isVoid,
          conceptConstraints: conceptConstraints)   ## Phase 15 G6

# ---- Top-level: procDef → SymexProgram-emitting NimNode ----------------------

type
  ParseResult* = object
    params*: seq[IRParam]
    bodyNimNode*: NimNode
    paramsNimNode*: NimNode
    procsNimNode*: NimNode    ## emit-time AST: yields `Table[string, ProcSig]`
                              ## with all transitively-reachable callees
    body*: IRStmt             ## Phase 12 cycle 7: parsed IR body, kept
                              ## as a Nim value at macro time so the
                              ## `irHasAssert` / `irHasIndex` /
                              ## `irHasVariantField` / `irCollectLabels`
                              ## scan helpers can inspect it directly
                              ## without re-parsing.
    procs*: Table[string, ProcSig]
                              ## Macro-time copy of the callee table so
                              ## the cycle-4 scan helpers can recurse
                              ## through `isCall` bodies. Mirrors the
                              ## emit-time AST in `procsNimNode`.
    userExnHierarchyNimNode*: NimNode
                              ## Phase 15 E4a. Emit-time AST yielding a
                              ## `Table[string, string]` of captured
                              ## child -> parent user-exn links.
    parseErrorsNimNode*: NimNode
                              ## Phase 15 G1c. Emit-time AST yielding a
                              ## `seq[SymexErrorInfo]` of parse-time errors
                              ## (generic instantiation-cap overflow). Threaded
                              ## into `SymexProgram.parseErrors`.
    parseErrors*: seq[SymexErrorInfo]
                              ## RFC-0005 S8. Macro-time copy of the same
                              ## records, AFTER the placement check
                              ## (`placeDeclineScopes`).
    annotationViolationsNimNode*: NimNode
                              ## RFC-0005 S8 (§13.3, i3). Emit-time AST
                              ## yielding `seq[AnnotationViolation]`, threaded
                              ## into `SymexProgram.annotationViolations`.
    annotationViolations*: seq[AnnotationViolation]
                              ## RFC-0005 S8. Macro-time copy.
    retTy*: IRType            ## RFC-0005 S8p. The SUT's return type; nil
                              ## for a void SUT.
    retTyNimNode*: NimNode    ## RFC-0005 S8p. Emit-time AST of `retTy`,
                              ## threaded into `SymexProgram.retTy`.
    globals*: seq[IRGlobal]   ## RFC-0005 S8as. The module-level variables
                              ## the parse named (`seenModuleGlobals`).
    globalsNimNode*: NimNode  ## RFC-0005 S8as. Emit-time AST of `globals`,
                              ## threaded into `SymexProgram.globals`.

func isLiteralInit(v: NimNode): bool =
  ## RFC-0005 S8as. `v` is a literal, possibly behind the conversion Nim
  ## inserts to fit it to the declared type (`let g: int8 = 9`).
  case v.kind
  of nnkCharLit .. nnkFloat128Lit, nnkStrLit .. nnkTripleStrLit: true
  of nnkHiddenStdConv, nnkConv:
    v.len == 2 and isLiteralInit(v[1])
  else: false

proc collectGlobals(ctx: ParseCtx): seq[IRGlobal] =
  ## RFC-0005 S8as. The module-level variables the parse named, each with
  ## its entry-value model (`IRGlobal`). Only an immutable `let` has a value
  ## the property can rely on, and only when its initialiser is a literal:
  ## the walk then reads that literal. A `var` may hold anything by the
  ## time the property runs -- other code, an earlier test, may have
  ## assigned it -- so its entry value is free (the walker's
  ## `entryValueOf`), as is a `let` whose initialiser is computed.
  for g in seenModuleGlobals():
    let ty = classifyType(g.getTypeInst).ty
    var init: IRExpr = nil
    if g.symKind == nskLet and
       ty.kind in {itInt, itBool, itFloat32, itFloat64, itString}:
      let impl = g.getImpl
      if impl.kind == nnkIdentDefs and impl.len >= 3 and
         isLiteralInit(impl[^1]):
        var pre: seq[IRStmt]
        let ir = parseExpr(impl[^1], pre, ctx)
        if pre.len == 0: init = ir
    result.add mkIRGlobal(globalIRName(g), ty, g.symKind == nskVar, init)

proc emitGlobals(gs: seq[IRGlobal]): NimNode =
  ## RFC-0005 S8as.
  var lit = newTree(nnkBracket)
  for g in gs:
    lit.add newCall(bindSym"mkIRGlobal", newLit(g.name), emitIRType(g.ty),
                    newLit(g.isVar),
                    (if g.init == nil: newNilLit() else: emitExpr(g.init)))
  if gs.len == 0:
    return newCall(newTree(nnkBracketExpr, ident"newSeq", bindSym"IRGlobal"))
  prefix(lit, "@")

proc emitParam(p: IRParam): NimNode =
  newTree(nnkObjConstr,
    bindSym"IRParam",
    newColonExpr(ident"name",     newLit(p.name)),
    newColonExpr(ident"ty",       emitIRType(p.ty)),
    newColonExpr(ident"rangeLo",  newLit(p.rangeLo)),
    newColonExpr(ident"rangeHi",  newLit(p.rangeHi)),
    newColonExpr(ident"hasRange", newLit(p.hasRange)),
    newColonExpr(ident"isVar",    newLit(p.isVar)),
    newColonExpr(ident"isStringBacked", newLit(p.isStringBacked)),
    newColonExpr(ident"isIntOffset", newLit(p.isIntOffset)),
    newColonExpr(ident"isScanOffset", newLit(p.isScanOffset)))

proc emitParamSeq(ps: seq[IRParam]): NimNode =
  var lit = newTree(nnkBracket)
  for p in ps:
    lit.add emitParam(p)
  prefix(lit, "@")

proc emitProcSig(sig: ProcSig): NimNode =
  newTree(nnkObjConstr,
    bindSym"ProcSig",
    newColonExpr(ident"name",    newLit(sig.name)),
    newColonExpr(ident"params",  emitParamSeq(sig.params)),
    newColonExpr(ident"body",    emitStmt(sig.body)),
    newColonExpr(ident"retTy",   emitIRType(sig.retTy)),
    newColonExpr(ident"isVoid",  newLit(sig.isVoid)),
    # RFC-0005 S8an: the walker copies the captures in and out.
    newColonExpr(ident"captures", newLit(sig.captures)))

proc emitProcs(procs: Table[string, ProcSig]): NimNode =
  ## Emit a Table[string, ProcSig] builder. Uses a `block:` with an
  ## explicit assignment per entry — the Nim literal syntax for Table
  ## values via `{ … }.toTable` is brittle for object-rich payloads.
  let tableId = genSym(nskVar, "tbl")
  result = newStmtList()
  result.add newVarStmt(tableId,
    newCall(newTree(nnkBracketExpr, bindSym"initTable",
                                     bindSym"string", bindSym"ProcSig")))
  for name, sig in procs:
    result.add newAssignment(
      newTree(nnkBracketExpr, tableId, newLit(name)),
      emitProcSig(sig))
  result.add tableId
  result = newTree(nnkBlockStmt, newEmptyNode(), result)

proc emitStrStrTable(t: Table[string, string]): NimNode =
  ## Phase 15 E4a. Emit a `Table[string, string]` builder (child -> parent
  ## user-exn links). Same `block:` + per-entry assignment shape as
  ## `emitProcs`, which is robust for object-rich payloads.
  let tableId = genSym(nskVar, "uxh")
  result = newStmtList()
  result.add newVarStmt(tableId,
    newCall(newTree(nnkBracketExpr, bindSym"initTable",
                                     bindSym"string", bindSym"string")))
  for child, parent in t:
    result.add newAssignment(
      newTree(nnkBracketExpr, tableId, newLit(child)),
      newLit(parent))
  result.add tableId
  result = newTree(nnkBlockStmt, newEmptyNode(), result)

proc emitScope(sc: DeclineScope): NimNode =
  ## RFC-0005 S8. Emit a `DeclineScope` value through its constructors.
  case sc.kind
  of dskSiteAnchored: newCall(bindSym"siteAnchored", newLit(sc.markerId))
  of dskCalleeKey:    newCall(bindSym"calleeKeyed", newLit(sc.calleeKey))
  of dskSignature:    newCall(bindSym"signatureScope")
  of dskWalkSite:     newCall(bindSym"walkSite")
  of dskUnplaced:     nnkObjConstr.newTree(bindSym"DeclineScope",
                        newColonExpr(ident"kind", newLit(dskUnplaced)))

proc emitErrorSeq(errs: seq[SymexErrorInfo]): NimNode =
  ## Phase 15 G1c. Emit a `seq[SymexErrorInfo]` literal of parse-time errors
  ## (generic instantiation-cap overflow). `kind`/`severity` are enum values,
  ## emitted through `newLit` (RFC-0005 S8e: a conversion via the enum
  ## type's symbol, not the member's name, which the caller's scope need not
  ## hold); `msg` is a string literal. RFC-0005 S8:
  ## `scope` rides along (`emitScope`).
  var br = newTree(nnkBracket)
  for e in errs:
    br.add nnkObjConstr.newTree(
      bindSym"SymexErrorInfo",
      newColonExpr(ident"kind", newLit(e.kind)),
      newColonExpr(ident"severity", newLit(e.severity)),
      newColonExpr(ident"msg", newLit(e.msg)),
      newColonExpr(ident"scope", emitScope(e.scope)))
  prefix(br, "@")

proc emitAnnotationViolations(avs: seq[AnnotationViolation]): NimNode =
  ## RFC-0005 S8 (§13.3, i3). Emit the `seq[AnnotationViolation]` literal
  ## threaded into `SymexProgram.annotationViolations`.
  var br = newTree(nnkBracket)
  for a in avs:
    br.add nnkObjConstr.newTree(
      bindSym"AnnotationViolation",
      newColonExpr(ident"pragma", newLit(a.pragma)),
      newColonExpr(ident"kind", newLit(a.kind)),
      newColonExpr(ident"callee", newLit(a.callee)),
      newColonExpr(ident"site", newLit(a.site)),
      newColonExpr(ident"msg", newLit(a.msg)))
  prefix(br, "@")

proc callNameOf(n: NimNode): string =
  ## The routine name at call position `n[0]`, through a bound sym-choice.
  let c = n[0]
  case c.kind
  of nnkSym, nnkIdent: c.strVal
  of nnkClosedSymChoice, nnkOpenSymChoice:
    if c.len > 0: c[0].strVal else: ""
  else: ""

proc collectEmittedAnchors(n: NimNode; markers: var HashSet[int];
                           keys: var HashSet[string]) =
  ## RFC-0005 S8 (§2.5 point 4). Every anchor the EMITTED program carries:
  ## the marker literal of each `mkUnsupported(kind, reason, marker)` /
  ## `mkUnsafeCast(reason, marker)` call, and each never-registered callee
  ## key string literal (`unregisteredCalleeKey`).
  if n == nil: return
  case n.kind
  of nnkStrLit..nnkTripleStrLit:
    if n.strVal.startsWith(unregisteredCalleePrefix):
      keys.incl n.strVal
  of nnkCall:
    let nm = callNameOf(n)
    if nm == "mkUnsupported" and n.len == 4 and
       n[3].kind in nnkIntLit..nnkInt64Lit:
      markers.incl int(n[3].intVal)
    elif nm == "mkUnsafeCast" and n.len == 3 and n[2].kind in nnkIntLit..nnkInt64Lit:
      markers.incl int(n[2].intVal)
    for c in n: collectEmittedAnchors(c, markers, keys)
  else:
    for c in n: collectEmittedAnchors(c, markers, keys)

proc placeDeclineScopes(errs: var seq[SymexErrorInfo]; emitted: openArray[NimNode]) =
  ## RFC-0005 S8 (§2.5 point 4). The placement check: a parse-time decline
  ## whose anchor did NOT survive into the emitted program the walker will
  ## walk (a marker a caller dropped, a callee key no `mkCall` carries) is
  ## rescoped `dskUnplaced` -- bucket 4, where the S8 totality pin counts it.
  ## Checked against the EMITTED NimNode, not the IR value, because the
  ## emitted form is the one the walker rebuilds and walks.
  var markers: HashSet[int]
  var keys: HashSet[string]
  for e in emitted: collectEmittedAnchors(e, markers, keys)
  for e in errs.mitems:
    case e.scope.kind
    of dskSiteAnchored:
      if e.scope.markerId notin markers: e.scope = DeclineScope(kind: dskUnplaced)
    of dskCalleeKey:
      if e.scope.calleeKey notin keys: e.scope = DeclineScope(kind: dskUnplaced)
    else: discard

const emitHoistHeight* = 24
  ## RFC-0005 S8t2. The tallest call subtree `boundEmittedDepth` leaves
  ## inline in an emitted IR builder; a taller one is bound to a `let`.

proc boundEmittedDepth*(root: NimNode): NimNode =
  ## RFC-0005 S8t2. The emitted IR builder (`emitStmt`/`emitProcs`) nests one
  ## Nim call per IR node, so its AST is as deep as the IR, and the compiler
  ## semchecks it by native recursion. S8t's nested short-circuit guards made
  ## the IR ~7 AST levels deeper per chain operand, which overflowed the 1 MB
  ## main-thread stack of the Windows `nim.exe` on a 10-operand chain
  ## (`tsymex_r6_nulwitness`, STATUS_STACK_OVERFLOW compiling
  ## `tsymex_rfc0005_s8t_termination`); a 40-operand chain overflowed 1 MB on
  ## Linux too.
  ##
  ## Bounds the depth without changing the value built: any call subtree
  ## taller than `emitHoistHeight` is bound, innermost first, to a fresh
  ## `let` in a statement-list expression around `root`, and referenced by
  ## that symbol where it stood. Every call in an emitted builder is a pure
  ## constructor (`mk*` in `types.nim`, over literals and bound symbols, no
  ## locals), so evaluating a subtree ahead of its left siblings builds the
  ## same IR. A builder no taller than the bound is returned unchanged.
  ## Walks the tree iteratively (post-order with an explicit stack).
  if root == nil: return root
  var lets = newNimNode(nnkLetSection)
  # Frame: a node, the next child to visit, the tallest child so far.
  var stack: seq[tuple[n: NimNode, i, h: int]] = @[(root, 0, 0)]
  var done = 0            # height of the subtree just finished
  while true:
    # Plain copies: in the compile-time VM a `let` of a seq element can
    # alias it, and the frame is updated below.
    let n = stack[^1].n
    let i = stack[^1].i
    if i < n.len:
      stack[^1].i = i + 1
      stack.add (n[i], 0, 0)
      continue
    done = stack[^1].h + 1
    discard stack.pop()
    if stack.len == 0: break
    let k = stack[^1].i - 1           # `n` is this parent's child k
    if n.kind == nnkCall and done > emitHoistHeight:
      let t = genSym(nskLet, "irPart")
      lets.add newIdentDefs(t, newEmptyNode(), n)
      stack[^1].n[k] = t
      done = 1
    stack[^1].h = max(stack[^1].h, done)
  if lets.len == 0: root
  else: newTree(nnkStmtListExpr, lets, root)

proc demoteUnrenderableWitnessTy(ty: IRType): IRType =
  ## RFC-chapulin-hardening CR-2c (Cluster 2 — Crash-totality). `classifyType`
  ## is a SHARED, widely-reused classifier — it also runs on purely-internal
  ## (non-witness) types, e.g. the return type of an in-body helper call like
  ## `bytes(s): seq[byte]`, which legitimately classifies to `itSeq` even
  ## though `byte`-element seqs have no witness reader. Degrading THOSE would
  ## be over-triggering: it would corrupt internal type modeling for values
  ## that are never rendered as a witness at all (confirmed by a regression:
  ## gating `classifyType` itself broke `.len`/indexing on such internal
  ## values). The renderability gate must therefore apply ONLY at the true
  ## choke point — here, where `parseProc*` classifies a TOP-LEVEL SUT
  ## PARAMETER type, the exact value `emitTyAndReader` (`symex.nim`) will
  ## later be asked to build a witness reader for.
  ##
  ## Only a fixed sub-fragment of `seq`/`Table`/`HashSet` element/key/value
  ## shapes has a witness reader. `isRenderableWitnessTy` (`smt/types.nim`)
  ## is the RECURSIVE renderability predicate over the WHOLE witness type-tree
  ## — it mirrors EXACTLY the type-tree `emitTyAndReader` walks (recursing into
  ## tuple/object fields, array elements, variant arms, distinct bases and ref
  ## pointees), reusing the `isRenderableSeqElemTy`/`isRenderableTableTy`/
  ## `isRenderableSetElemTy` leaf checks so predicate and reader never drift.
  ## This closes the nested-aggregate completeness gap: a parameter that NESTS
  ## an unrenderable `seq[Widget]`/`Table[string,string]`/`HashSet[string]`
  ## inside a tuple / object / array / variant / distinct / ref pointee (not
  ## just a bare top-level `seq`/`Table`/`HashSet`) is demoted to the
  ## `itUninterp("__unsupported_witness:" & s)` placeholder INSTEAD of the real
  ## aggregate type — mirroring CR-2b's `__unsupported:` idiom under a distinct
  ## marker — so `allocateSym` (`smt/runtime.nim`) raises the classified
  ## `SymexClassifiedDegradeError` (`feUnsupportedWitnessType`) at PARAMETER-
  ## ALLOCATION time, before the body is walked and before witness codegen is
  ## ever reached, forcing a WHOLE-RUN `sxUnknown` instead of
  ## `emitTyAndReader`'s `error()` aborting compilation. The DEMOTED unit is
  ## always the WHOLE top-level parameter (sound: the run degrades to
  ## `sxUnknown` regardless of the body, and no dummy is ever rendered as a
  ## false `sxSat`).
  if isRenderableWitnessTy(ty): ty
  else: tUninterp("__unsupported_witness:" & $ty)

proc parseProc*(procDef: NimNode, maxInstantiationsPerProc = 0): ParseResult =
  ## RFC-parser-normalization N2: `procDef` is always already resolved by
  ## its callers (`resolveEntryImpl`'s hard-error wrapper, or an internal
  ## `resolveRoutineImpl` result) — a membership-only assertion, so it
  ## routes onto `walkableRoutineKinds`.
  procDef.expectKind walkableRoutineKinds
  let formalParams = procDef[3]
  formalParams.expectKind nnkFormalParams
  let ctx = newParseCtx(maxInstantiationsPerProc)
  # RFC-0005 S8e: claim every declaration's IR name by SYMBOL before any
  # pre-pass or IR build reads a name (`scoped_names`): a shadowing local
  # gets its own env slot. Params claim first, so the witness keeps them.
  resetNameScopes()
  claimRoutine(procDef)
  # Round-6 B1a (ADR-0028 Leg 1): the representation pre-pass runs BEFORE
  # any IR is built — the `iekStrSubstr`-vs-`iekSeqSlice` dispatch choice
  # `parseStmt` below bakes into the IR the instant `parseExpr`'s bracket
  # arm returns, so the deciding fact must exist first.
  ctx.procScoped.stringBackedParams = collectStringBackedByteSeqParams(procDef)
  # Round-6 B4 (ADR-0028 Leg 1, ADR-0027's recorded lift): same pre-pass
  # timing discipline as B1a above — the deciding fact (which int PARAM
  # feeds an accumulating-scan's offset) must exist before `runSymexImpl`'s
  # top-level param-allocation loop chooses BV vs svInt.
  let intOffsetParams = collectIntOffsetParams(procDef)
  let scanOffsetParams = collectScanOffsetParams(procDef)   ## RFC-0005 S8q/S8t
  # Round-6 B7r2 (walker v88): companion pre-pass for the literal-seeded
  # case `collectIntOffsetParams` cannot cover (see its own doc comment)
  # — same timing discipline (must exist before the `nnkVarSection`/
  # `nnkLetSection` statement-parse arm below bakes the literal's proto
  # choice into the IR).
  ctx.procScoped.intOffsetLiteralLocals = collectIntOffsetLiteralLocals(procDef)
  ctx.procScoped.assumedBoundVars = collectAssumedBoundVars(procDef)
  # Round-6 R5 (finding S4, walker v93): same pre-pass timing discipline as
  # B1a/B7r2 above — the deciding fact ("is this pair-loop's counter read
  # after the loop") must exist before `tryRecognizePairLoopIdiom` (reached
  # mid-body-walk) decides whether to apply the closed form at all.
  ctx.procScoped.pairLoopCounterConsumedAfter = collectPairLoopCounterConsumedAfter(procDef)
  var params: seq[IRParam]
  var paramsNimSeq = newTree(nnkBracket)
  for i in 1 ..< formalParams.len:
    let id = formalParams[i]
    id.expectKind nnkIdentDefs
    let tyNode = id[id.len - 2]
    # Phase 14 A7a: detect `var T` at the SUT parameter level so
    # `isVar = true` is consistently set for top-level params, not
    # just for callees (parseCalleeImpl already does this). The
    # witness still extracts the INITIAL value via `initialEnv` —
    # mutations are walker-internal symbolic operations.
    let isVarParam = tyNode.kind == nnkVarTy
    var classified = classifyType(tyNode)
    classified.ty = demoteUnrenderableWitnessTy(classified.ty)   ## CR-2c
    for j in 0 ..< id.len - 2:
      let name = id[j].strVal
      var p = IRParam(name: name, ty: classified.ty,
                      rangeLo: classified.range.lo,
                      rangeHi: classified.range.hi,
                      hasRange: classified.range.hasRange,
                      isVar: isVarParam,
                      isStringBacked: containsSym(ctx.procScoped.stringBackedParams, id[j]),
                      isIntOffset: name in intOffsetParams,
                      isScanOffset: name in scanOffsetParams)
      params.add p
      paramsNimSeq.add emitParam(p)
  # Phase 14 cycle C3: always wrap the proc body in `isBlock` so the
  # walker's frontier-prune (which lives in `walkBlock`) sees the
  # top-level statement stream. Without this, single-statement
  # bodies (e.g. one outer `if`) dispatch straight to `walk(isIf)`
  # and bypass the prune entirely.
  let parsed = parseStmt(procDef[6], ctx)
  let bodyIR = if parsed != nil and parsed.kind == isBlock: parsed
               else: mkBlock(@[parsed])
  # RFC-0005 S8p: the SUT's return type, so a read of `result` before the
  # body writes it takes that type's zero value, as in a callee (S8n).
  # Classified as `parseCalleeImpl` classifies a callee's.
  if formalParams[0].kind != nnkEmpty:
    result.retTy = classifyType(formalParams[0]).ty
    result.retTyNimNode = emitIRType(result.retTy)
  else:
    result.retTyNimNode = newNilLit()
  result.params = params
  result.bodyNimNode = emitStmt(bodyIR)
  result.paramsNimNode = prefix(paramsNimSeq, "@")
  result.procsNimNode = emitProcs(ctx.procs)
  result.body = bodyIR
  result.procs = ctx.procs
  result.userExnHierarchyNimNode = emitStrStrTable(ctx.userExnHierarchy)
  # RFC-0005 S8as: after every routine is parsed, so every global the walk
  # can reach has been named.
  result.globals = collectGlobals(ctx)
  result.globalsNimNode = emitGlobals(result.globals)
  # RFC-0005 S8 (§2.5 point 4): placement check against the emitted IR.
  placeDeclineScopes(ctx.parseErrors, [result.bodyNimNode, result.procsNimNode])
  # RFC-0005 S8t2: after the placement check, which reads the builders as
  # emitted; the bound moves call subtrees but keeps every node.
  result.bodyNimNode = boundEmittedDepth(result.bodyNimNode)
  result.procsNimNode = boundEmittedDepth(result.procsNimNode)
  result.parseErrors = ctx.parseErrors
  result.parseErrorsNimNode = emitErrorSeq(ctx.parseErrors)   ## Phase 15 G1c
  result.annotationViolations = ctx.annotationViolations
  result.annotationViolationsNimNode =
    emitAnnotationViolations(ctx.annotationViolations)          ## RFC-0005 S8

proc parseEntryImpl*(fn: NimNode, apiName: string, maxInst: int): ParseResult =
  ## RFC-parser-normalization N1. Collapses the three-step `getImpl` -> kind
  ## gate -> `parseProc` ritual duplicated across SIX `symex.nim` entry
  ## macros (`symexCacheKeyForFn`, `saveSymexWitness`, `loadSymexWitnesses`,
  ## `saveSymexVerdict`, `loadSymexVerdict`, `symexFindAllWitnesses`).
  ##
  ## The FOURTH step of that ritual — destructuring the result into
  ## `paramsExpr`/`bodyExpr`/`procsExpr` (+ `rebuildTargetNode`) — is shared
  ## by only FIVE of those six (`symexFindAllWitnesses` consumes `parsed`
  ## directly), so it stays per-consumer and is deliberately NOT folded in
  ## here. `symexFind`/`assertCoveredBy` also route through this proc (as of
  ## commit 1adcd33) and consume `.params` at macro time the same way
  ## `symexFindAllWitnesses` does — all nine entry macros now route through
  ## `parseEntryImpl`.
  scanProcFieldAssigns(fn)   ## RFC-0005 S8bn (item 6)
  parseProc(resolveEntryImpl(fn, apiName), maxInst)
