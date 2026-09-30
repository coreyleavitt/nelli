## RFC-0005 (soundness channels) slice S8ab -- S8x's remainder: a
## TYPE-AWARE mechanical guard for the compile-time VM `let`-aliasing
## hazard, over the whole scope S8x's own hand audit covered.
##
## S8x (`tests/tsymex_rfc0005_s8x_vm_alias.nim`) found and fixed the two
## live-at-the-time hazards (`resolveBreak`'s `let t = ctx.procScoped.
## jumpTargets[i]`, `ensureProcRegistered`'s `let savedProcScoped = ctx.
## procScoped`) but its own mechanical pin only source-scans ONE pattern
## in ONE file: no `let` in `dsl_parser.nim` binding a `ctx.procScoped`
## record or element. Its own "different mechanisms, reported and not
## fixed here" note is explicit that this is too narrow: "a line scan
## cannot tell a `NimNode` `let` (safe) from an object `let`. The next
## value-typed save/restore added to the front end is guarded only by
## review and by this note." This slice closes that gap with a
## TYPED-AST walker (Option 1 of the slice's brief) instead of text.
##
## ---- What the walker does -----------------------------------------------
##
## For every top-level `proc`/`func`/`macro`/`template`/`iterator`/
## `converter` in the audited files (found by a column-0 source scan --
## structural, not semantic, so it also catches a nested proc's OWN
## nested defs only indirectly, via recursing into the outer proc's typed
## body, where they appear as `nnkProcDef` children):
##
## 1. `getImpl()` on the resolved symbol (private procs need the
##    compiler to see them: `{.all.}` on each `import` below, not plain
##    `import`, since most of the two historical hazards' hosts --
##    `resolveBreak`, `ensureProcRegistered` -- are unexported) gives the
##    TYPED body.
## 2. Every `nnkLetSection` is walked. A binding is a HAZARD SHAPE if its
##    RHS (after unwrapping hidden conversions the compiler inserts) is
##    `nnkBracketExpr` (a seq/array/Table element), `nnkDotExpr` (a
##    field), or a bare `nnkSym` (a whole other local's location) --
##    exactly the three node kinds RFC-0005's slice brief names. A
##    binding whose ROOT symbol is itself defined earlier in the SAME
##    `let` section is the compiler's OWN tuple-unpack desugaring
##    (`let (a, b) = f()` lowers to `let tmp = f(); let a = tmp[0]; let
##    b = tmp[1]` -- `tmp` is a fresh value, never an outside alias) and
##    is excluded; it is not a real instance of this hazard, and without
##    this exclusion it was the single largest noise source found while
##    building this guard (S8x's own scope, ~330 "safe" lets survives
##    dwarfed by tuple-unpack noise otherwise).
## 3. The bound NAME's `getTypeInst()` decides safety: `NimNode`,
##    `IRExpr`, `IRStmt`, `IRType` and every other `ref` are
##    `ntyRef` -- safe by the VM's own rules (S8x's note: "a ref is
##    shared by design, so aliasing one changes nothing"). A scalar
##    (`ntyInt`, `ntyBool`, ...) is safe too (copied into a register). A
##    `typeKind` of `ntyObject`, `ntyTuple`, `ntySequence`, `ntyString`,
##    `ntySet` or `ntyArray` is the hazard class RFC-0005 S8x's own VM
##    probe pinned as aliasing.
##
## Non-`var` PARAMETERS get a separate, narrower check: a value-typed
## parameter aliases the caller's location too, but Nim's own mutability
## rules already forbid mutating it BY ITS OWN NAME (`'x' cannot be
## assigned to`), so the only real shape is `paramThenCallerWriteThroughRef`
## (S8x's own pin): a SECOND, `ref`-typed parameter's reachable field
## graph contains the same type as a plain value parameter, AND the body
## mutates that ref parameter in place -- meaning a caller that happens to
## pass the same location twice (once directly, once through the ref) can
## make the value parameter observably stale. A structural-only version
## of this check (any non-`var` value parameter, regardless of whether
## anything mutates a same-typed sibling) was tried first and produced
## 265 hits across this scope, overwhelmingly ordinary read-only `string`/
## `seq` parameters -- exactly the "hundreds of false positives" the
## slice brief rules out. Gating on an ACTUAL in-place mutation of a
## same-shaped ref sibling (`bodyMutatesRoot`, reusing S8x's own
## `scan.py` MUT_METH vocabulary) brings it to zero on the real scope
## while still catching the fixture below.
##
## ---- Scope ----------------------------------------------------------
##
## The same 15 files S8x's own audit table covers (its "Method"
## paragraph): the six `smt/` front-end modules, `symex.nim`'s macro
## helpers, and the eight other macro-declaring top-level modules.
## `{.all.}` is required on every one of them: the two historical hazards
## were both UNEXPORTED procs, and a plain `import` cannot see those at
## all, so a guard restricted to exported symbols would have missed both
## of S8x's own findings.
##
## ---- Known gaps (different mechanisms, reported and not fixed here) --
##
## - Backtick operator names (`` `==` ``, `` `[]` ``, ...) ARE picked up
##   (the source scan special-cases a leading backtick), but any name the
##   scan cannot parse at all (an unusual multi-line signature, a name
##   this scan's simple lexer mishandles) silently drops that routine from
##   coverage. The scan is structural text, same caveat as S8x's own.
## - A `[]`-style hazard reached through a PROC call (Table's `[]`, a
##   distinct wrapper's `[]`) types as `nnkCall`, not `nnkBracketExpr`,
##   and is NOT covered -- the brief's three named shapes are exactly
##   `nnkBracketExpr`/`nnkDotExpr`/`nnkSym`, and widening to "any `[]`
##   call" was tried and immediately caught STRING SLICING
##   (`s[0 .. ^2]`, which always copies) as a false positive, because
##   slicing is ALSO lowered through a `[]` call. No confirmed compile-time
##   Table-value instance exists in this scope today.
## - The param check's "same type reachable" test compares `repr` text,
##   not true structural/generic identity, and a ref param's field graph
##   is walked only 3 levels deep.
## - Generic procs never instantiated in this scope's own compilation unit
##   get `getImpl()`'s un-instantiated generic tree; a `let`/param whose
##   type depends on an uninstantiated generic parameter cannot be
##   classified and is silently skipped (not a false negative signal --
##   `getTypeInst` returns a generic placeholder or nil, filtered out by
##   the same `objKinds`/`t.isNil` checks as any other unresolvable type).
##
## No walker bump: this is test-only reflection over already-compiled
## modules; the IR is untouched.

import std/[macros, os, strutils, sequtils, unittest]
import nelli/smt/dsl_parser {.all.}
import nelli/smt/dsl_typebridge {.all.}
import nelli/smt/scoped_names {.all.}
import nelli/smt/exn_hierarchy {.all.}
import nelli/smt/stdlib_models {.all.}
import nelli/smt/types {.all.}
import nelli/symex {.all.}
import nelli/fuzzmacro {.all.}
import nelli/derive {.all.}
import nelli/dsl {.all.}
import nelli/coverage {.all.}
import nelli/mutation {.all.}
import nelli/concolic {.all.}
import nelli/strategy {.all.}
import nelli/parallel {.all.}

const smtDir = currentSourcePath().parentDir() / ".." / "src" / "nelli" / "smt"
const rootDir = currentSourcePath().parentDir() / ".." / "src" / "nelli"
const thisFile = "tsymex_rfc0005_s8ab_letaudit.nim"

# ---- name discovery (structural: column-0 source scan) ----------------------

proc extractTopLevelNames(path: string): seq[string] =
  ## Every top-level `proc`/`func`/`macro`/`template`/`iterator`/
  ## `converter` name in `path`, in source order, deduplicated. Column 0
  ## only, so a NESTED def (like `emitMVBranch` inside
  ## `emitTyAndReaderShared`) is not separately listed here -- it is still
  ## audited, as an `nnkProcDef` child the outer proc's typed-body walk
  ## descends into. A backtick-quoted operator (`` `==`* ``) is handled
  ## too; S8x's own scope table lists exactly one (`types.nim`'s `IRType`
  ## `==`).
  let src = staticRead(path)
  var seen: seq[string]
  for line in src.splitLines():
    if line.len == 0 or line[0] notin {'p', 'f', 'm', 't', 'i', 'c'}: continue
    var rest = ""
    for kw in ["proc ", "func ", "macro ", "template ", "iterator ", "converter "]:
      if line.startsWith(kw):
        rest = line[kw.len .. ^1]
        break
    if rest.len == 0: continue
    var nm = ""
    if rest[0] == '`':
      let close = rest.find('`', 1)
      if close > 1: nm = rest[1 ..< close]
    else:
      var i = 0
      if i < rest.len and rest[i] in {'A' .. 'Z', 'a' .. 'z', '_'}:
        let start = i
        while i < rest.len and rest[i] in {'A' .. 'Z', 'a' .. 'z', '0' .. '9', '_'}: inc i
        nm = rest[start ..< i]
    if nm.len > 0 and nm notin seen:
      seen.add nm
      result.add nm

# ---- the typed-AST walker (compile time) -------------------------------------

var letHits {.compileTime.}: seq[string]
var paramHits {.compileTime.}: seq[string]
var walkErrs {.compileTime.}: seq[string]

const objKinds = {ntyObject, ntyTuple, ntySequence, ntyString, ntySet, ntyArray}
  ## RFC-0005 S8x's VM probe: every non-scalar VALUE location the VM
  ## aliases through a `let`. `ref` (`ntyRef`) is excluded on purpose --
  ## "shared by design", the VM's own safe case.

proc unwrapHidden(n: NimNode): NimNode =
  ## Strips the implicit conversions/derefs the typed tree inserts around
  ## an expression (`nnkHiddenStdConv` and friends) so shape/root checks
  ## see the real expression underneath.
  result = n
  while result.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv,
                         nnkHiddenSubConv, nnkHiddenCallConv, nnkConv,
                         nnkExprColonExpr}:
    if result.len == 0: break
    result = result[^1]

proc rootSym(n: NimNode): NimNode =
  ## The base symbol of a `.field`/`[i]` chain (`ctx.procScoped.
  ## jumpTargets[i]` -> `ctx`).
  var cur = unwrapHidden(n)
  while cur.kind in {nnkBracketExpr, nnkDotExpr}:
    if cur.len == 0: return cur
    cur = unwrapHidden(cur[0])
  cur

proc rhsAliasKind(n: NimNode): NimNode =
  ## nil: not one of the three hazard shapes. Otherwise the (unwrapped)
  ## RHS node to classify by type.
  let r = unwrapHidden(n)
  if r.kind in {nnkBracketExpr, nnkDotExpr, nnkSym}: return r
  nil

proc walkLets(n: NimNode; owner: string; hits: var seq[string]) =
  if n == nil: return
  if n.kind == nnkLetSection:
    # Names bound in THIS section: a hit whose root is one of them is the
    # compiler's own tuple-unpack temp, not an outside alias (see header).
    var localNames: seq[string]
    for iddef in n:
      if iddef.kind notin {nnkIdentDefs, nnkVarTuple}: continue
      for k in 0 ..< iddef.len - 2:
        if iddef[k].kind == nnkSym: localNames.add macros.strVal(iddef[k])
    for iddef in n:
      if iddef.kind notin {nnkIdentDefs, nnkVarTuple}: continue
      let rhs = rhsAliasKind(iddef[^1])
      if rhs.isNil: continue
      let root = rootSym(rhs)
      if root.kind == nnkSym and macros.strVal(root) in localNames: continue
      for k in 0 ..< iddef.len - 2:
        let nameNode = iddef[k]
        if nameNode.kind != nnkSym: continue
        let t = nameNode.getTypeInst()
        if t.isNil: continue
        if t.typeKind notin objKinds: continue
        hits.add owner & ": let " & macros.strVal(nameNode) & " : " & t.repr &
          " (" & $t.typeKind & ") <- " & rhs.repr
  for c in n:
    walkLets(c, owner, hits)

const mutMethods = ["add", "setLen", "del", "delete", "insert", "incl",
  "excl", "pop", "clear", "sort", "reverse", "shrink", "fill", "inc", "dec",
  "mgetOrPut", "containsOrIncl", "missingOrExcl", "swap", "apply", "keepIf",
  "keepItIf", "applyIt", "mitems", "mpairs", "addQuoted", "removePrefix",
  "removeSuffix"]
  ## S8x's `scan.py` MUT_METH vocabulary, reused at the typed level: the
  ## receiver-mutating call surface that can make a bound location's later
  ## read stale.

proc bodyMutatesRoot(n: NimNode; target: NimNode): bool =
  ## True if the body writes in place to `target` or anything reachable
  ## through it (a field/element assignment, or a call to a mutating
  ## method on `target` or a sub-path of it).
  if n == nil: return false
  case n.kind
  of nnkAsgn:
    let lhs = unwrapHidden(n[0])
    if lhs.kind in {nnkBracketExpr, nnkDotExpr} and rootSym(lhs) == target:
      return true
  of nnkCall, nnkCommand:
    if n.len > 0:
      let callee = n[0]
      if callee.kind == nnkDotExpr and callee.len == 2 and
         macros.strVal(callee[1]) in mutMethods and rootSym(callee[0]) == target:
        return true
      if callee.kind == nnkSym and macros.strVal(callee) in mutMethods and
         n.len > 1 and rootSym(n[1]) == target:
        return true
  else: discard
  for c in n:
    if bodyMutatesRoot(c, target): return true
  false

proc collectFieldTypeReprs(objTypeSym: NimNode; depth: int; into: var seq[string]) =
  ## Field types reachable from a ref/object type symbol, depth-bounded
  ## (3): the shape of `paramThenCallerWriteThroughRef(h: Holder; xs: seq
  ## [int])`, where `xs` aliases `h.c.xs` because the CALLER passed the
  ## same location twice.
  if depth <= 0 or objTypeSym.kind != nnkSym: return
  var cur: NimNode
  try: cur = objTypeSym.getTypeImpl()
  except CatchableError: return
  if cur.isNil: return
  if cur.kind in {nnkRefTy, nnkPtrTy} and cur.len > 0 and cur[0].kind == nnkSym:
    let inner = cur[0]
    try: cur = inner.getTypeImpl()
    except CatchableError: return
  if cur.kind != nnkObjectTy or cur.len < 3: return
  let recList = cur[2]
  if recList.kind != nnkRecList: return
  for fld in recList:
    if fld.kind != nnkIdentDefs: continue
    let fieldTypeNode = fld[1]
    into.add fieldTypeNode.repr
    if fieldTypeNode.kind == nnkSym:
      collectFieldTypeReprs(fieldTypeNode, depth - 1, into)

proc walkParams(impl: NimNode; owner: string; hits: var seq[string]) =
  if impl.len <= 6: return
  let formals = impl[3]
  if formals.kind != nnkFormalParams: return
  let body = impl[6]
  var candidates: seq[tuple[nm: string, t: NimNode]]
  var siblingFieldReprs: seq[string]
  for i in 1 ..< formals.len:
    let iddef = formals[i]
    if iddef.kind != nnkIdentDefs: continue
    if iddef[1].kind == nnkVarTy: continue  # `var T`: copies, safe
    let sym = iddef[0]
    if sym.kind != nnkSym: continue
    let t = sym.getTypeInst()
    if t.isNil: continue
    if t.typeKind == ntyRef:
      # Only a ref param this body actually mutates in place can make a
      # sibling value param stale -- an unmutated ref param can never
      # invalidate anything, whatever its field types are.
      if bodyMutatesRoot(body, sym):
        collectFieldTypeReprs(t, 3, siblingFieldReprs)
    elif t.typeKind in objKinds:
      candidates.add (macros.strVal(sym), t)
  if siblingFieldReprs.len == 0: return
  for (nm, t) in candidates:
    if t.repr in siblingFieldReprs:
      hits.add owner & ": param " & nm & " : " & t.repr &
        " (" & $t.typeKind & ") -- a sibling ref param, mutated in this " &
        "body, reaches the same field type"

macro auditOne(procSym: typed; fileTag: static string): untyped =
  ## `procSym` is a `typed` macro parameter: passed a bare (possibly
  ## overloaded) identifier, the compiler resolves it to an
  ## `nnkClosedSymChoice`/`nnkOpenSymChoice` of every visible symbol with
  ## that name -- from ANY imported module, not just `fileTag`'s -- rather
  ## than raising "ambiguous identifier". `getImpl()`'s own
  ## `lineInfoObj.filename` then filters each candidate down to the ones
  ## that actually come from `fileTag`, so cross-module name collisions
  ## (a common short name reused elsewhere) cost nothing but a few
  ## rejected candidates.
  result = newStmtList()
  var syms: seq[NimNode]
  case procSym.kind
  of nnkClosedSymChoice, nnkOpenSymChoice:
    for s in procSym: syms.add s
  of nnkSym:
    syms.add procSym
  else: discard
  for s in syms:
    if s.symKind notin {nskProc, nskFunc, nskMethod, nskIterator,
                         nskConverter, nskTemplate, nskMacro}:
      continue
    var impl: NimNode
    try:
      impl = s.getImpl()
    except CatchableError as e:
      walkErrs.add fileTag & ": " & macros.strVal(s) & " getImpl raised: " & e.msg
      continue
    if impl.isNil or impl.kind == nnkNilLit: continue
    if not impl.lineInfoObj.filename.endsWith(fileTag): continue
    walkLets(impl, fileTag & ":" & macros.strVal(s), letHits)
    walkParams(impl, fileTag & ":" & macros.strVal(s), paramHits)

macro genAudits(names: static seq[string]; fileTag: static string): untyped =
  ## Emits one `auditOne(<bare name>, fileTag)` call per discovered name.
  ## Each call is its own macro instantiation; wrapping in a trivial
  ## `when true:` keeps every one of them a distinct statement rather than
  ## requiring `auditOne` to be variadic (it needs a separate `typed`
  ## argument per name for the compiler to resolve each independently).
  result = newStmtList()
  for nm in names:
    let call = newCall(bindSym"auditOne", ident(nm), newLit(fileTag))
    result.add nnkWhenStmt.newTree(nnkElifBranch.newTree(bindSym"true", newStmtList(call)))

template auditFile(dir, fname: string) =
  const path = dir / fname
  const names = extractTopLevelNames(path)
  genAudits(names, fname)

auditFile(smtDir, "dsl_parser.nim")
auditFile(smtDir, "dsl_typebridge.nim")
auditFile(smtDir, "scoped_names.nim")
auditFile(smtDir, "exn_hierarchy.nim")
auditFile(smtDir, "stdlib_models.nim")
auditFile(smtDir, "types.nim")
auditFile(rootDir, "symex.nim")
auditFile(rootDir, "fuzzmacro.nim")
auditFile(rootDir, "derive.nim")
auditFile(rootDir, "dsl.nim")
auditFile(rootDir, "coverage.nim")
auditFile(rootDir, "mutation.nim")
auditFile(rootDir, "concolic.nim")
auditFile(rootDir, "strategy.nim")
auditFile(rootDir, "parallel.nim")

const realScopeLetHits = block:
  var dedup: seq[string]
  for h in letHits:
    if h notin dedup: dedup.add h
  dedup

const realScopeParamHits = block:
  var dedup: seq[string]
  for h in paramHits:
    if h notin dedup: dedup.add h
  dedup

const realScopeErrs = walkErrs

# ---- allowlist: every let hit the real scope produces today -----------------
#
# Both are the SAME finding S8x's own hand audit already recorded (RFC
# §2.5 "As landed" table): `IRType`'s `==` (`types.nim`) and
# `emitMVBranch`, nested in `emitTyAndReaderShared` (`symex.nim`), each
# read a `VariantAxis`/`VariantArm` element and do not write it while the
# binding is live. No param hit is allowlisted: the real scope produces
# none today (see the walker's header for why the structural-only version
# of the param check was rejected).
const allowlist = [
  "types.nim:==: let bx : VariantAxis (ntyObject) <- b.mvAxes[i]",
  "types.nim:==: let barm : VariantArm (ntyObject) <- bx.arms[k]",
  "symex.nim:emitTyAndReaderShared: let ax : VariantAxis (ntyObject) <- ty.mvAxes[axisIdx]",
  "symex.nim:emitTyAndReaderShared: let elseArm : VariantArm (ntyObject) <- ax.arms[elseArmIx]",
]

# ---- RED fixture: S8x's pre-fix shapes, replicated on the real types --------
#
# `preFixResolveBreakShape`/`preFixEnsureProcRegisteredShape` are S8x's
# OWN pre-fix code from `dsl_parser.nim` at 5f4c2bb (`resolveBreak`,
# `ensureProcRegistered`), copied verbatim onto the real `ParseCtx`/
# `ProcScopedCollectors`/`JumpTarget` types this file already imports.
# They are never called; they exist only so the walker above can be
# pointed at THIS file's own name and prove it still flags the exact
# historical shape.

proc preFixResolveBreakShape(ctx: ParseCtx; label: NimNode): int =
  for i in countdown(ctx.procScoped.jumpTargets.high, 0):
    let t = ctx.procScoped.jumpTargets[i]      # RFC-0005 5f4c2bb hazard
    if not t.isLoop: return i
  -1

proc preFixEnsureProcRegisteredShape(ctx: ParseCtx) =
  let savedProcScoped = ctx.procScoped          # RFC-0005 5f4c2bb hazard
  ctx.procScoped = ProcScopedCollectors()
  discard savedProcScoped

type
  FxInner = object
    xs: seq[int]
  FxHolder = ref object
    c: FxInner

proc fxParamAliasShape(h: FxHolder; xs: seq[int]): int =
  ## The param check's own positive: `xs` may be `h.c.xs`, passed twice by
  ## the caller; `h` is mutated in place here, same shape as S8x's
  ## `paramThenCallerWriteThroughRef` pin.
  h.c.xs.add 3
  xs.len

const fixtureNames = @["preFixResolveBreakShape", "preFixEnsureProcRegisteredShape",
                       "fxParamAliasShape"]
genAudits(fixtureNames, thisFile)

const fixtureLetHits = block:
  var dedup: seq[string]
  for h in letHits:
    if h.startsWith(thisFile) and h notin realScopeLetHits and h notin dedup: dedup.add h
  dedup

const fixtureParamHits = block:
  var dedup: seq[string]
  for h in paramHits:
    if h.startsWith(thisFile) and h notin realScopeParamHits and h notin dedup: dedup.add h
  dedup

# ---- tests --------------------------------------------------------------

suite "S8ab: type-aware guard for the compile-time VM let-aliasing hazard":

  test "RED: the walker flags S8x's own two pre-fix shapes on the real types":
    # Taken from S8x's base (5f4c2bb): `resolveBreak`'s element let and
    # `ensureProcRegistered`'s whole-record let, both on the real
    # `ParseCtx`/`ProcScopedCollectors`/`JumpTarget` types.
    check fixtureLetHits.len == 2
    check fixtureLetHits.anyIt(it.contains("preFixResolveBreakShape") and it.contains("JumpTarget"))
    check fixtureLetHits.anyIt(it.contains("preFixEnsureProcRegisteredShape") and
                                it.contains("ProcScopedCollectors"))

  test "RED: the walker flags a non-var param aliased through a mutated ref sibling":
    check fixtureParamHits.len == 1
    check fixtureParamHits[0].contains("fxParamAliasShape")
    check fixtureParamHits[0].contains("param xs")

  test "GREEN: no getImpl/audit-machinery error across the 15-file scope":
    check realScopeErrs.len == 0
    if realScopeErrs.len > 0: echo realScopeErrs.join("\n")

  test "GREEN: every let hit in the real scope is on the explicit allowlist":
    var unexpected: seq[string]
    for h in realScopeLetHits:
      if h notin allowlist: unexpected.add h
    check unexpected.len == 0
    if unexpected.len > 0: echo "UNALLOWLISTED:\n" & unexpected.join("\n")
    # Every allowlist entry must still be live -- an entry the scope no
    # longer produces means the allowlist has drifted stale.
    var stale: seq[string]
    for a in allowlist:
      if a notin realScopeLetHits: stale.add a
    check stale.len == 0
    if stale.len > 0: echo "STALE ALLOWLIST ENTRY:\n" & stale.join("\n")

  test "GREEN: no param hit in the real scope (none allowlisted)":
    check realScopeParamHits.len == 0
    if realScopeParamHits.len > 0: echo realScopeParamHits.join("\n")
