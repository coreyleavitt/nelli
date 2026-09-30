## RFC-0005 (soundness channels) slices S8ab + S8af -- S8x's remainder: a
## TYPE-AWARE mechanical guard for the compile-time VM `let`-aliasing
## hazard, over the whole scope S8x's own hand audit covered.
##
## S8af closes four of S8ab's own "different mechanisms, reported and not
## fixed here" gaps (search this file for "S8af" to find each change):
## 1. Table/`[]`-via-`nnkCall` aliasing, told apart from string slicing by
##    the resolved callee's OWN return-type shape (`var T` vs `lent T` vs a
##    plain value), never by call syntax -- `calleeReturnsVar`.
## 2. Real type identity (`sameType`) in the param check, replacing the
##    `repr`-text comparison that a type ALIAS could evade -- `sameType`
##    call sites in `walkParams`, fixtures collected via `collectFieldTypes`.
## 3. Generic procs: a REAL instantiation (forced by passing an actual call
##    expression, not a bare name, through a `typed` macro parameter) is
##    now auditable instead of silently skipped -- `auditGenericInstantiation`.
## 4. CI: the guard now also runs as a named contract test on
##    `fuzzer-mingw`/`fuzzer-msvc` (it already ran on `symex-mingw` via
##    nelli.nimble's derived `tsymex_*` corpus) -- see
##    `.github/workflows/fuzzer-mingw.yaml` / `fuzzer-msvc.yaml`.
##
## S8af also adds `smt/scan.nim` to the audited scope (a real gap: it walks
## the SUT's IR "at macro time", per its own header, directly from
## `symexFindAllWitnesses`'s un-quoted macro body -- `symex.nim:2826/2828`
## -- with no quote-do wrapper between the macro and the call, so it is
## genuinely compile-time-VM-executed and was simply missing from S8x's
## original 15-file list). It contains zero `let`s today (all locals are
## `var`), so this adds coverage, not a new hit.
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
## S8x's original 15 files (its "Method" paragraph: the six `smt/`
## front-end modules, `symex.nim`'s macro helpers, and the eight other
## macro-declaring top-level modules) PLUS `smt/scan.nim` (S8af: see the
## file header's item above -- genuinely compile-time-VM-executed, was
## simply missing). `{.all.}` is required on every one of them: the two
## historical hazards were both UNEXPORTED procs, and a plain `import`
## cannot see those at all, so a guard restricted to exported symbols
## would have missed both of S8x's own findings.
##
## S8af also confirmed, file by file, that NOTHING ELSE reachable from
## `symex.nim`'s imports belongs in this scope. `runtime.nim`/
## `runtime_strings.nim` (and everything `runtime.nim` itself pulls in --
## `abstraction.nim`, `regex_parser.nim`, `concolictaxonomy.nim`,
## `../choice`) execute only at TEST RUNTIME: every call site is either
## inside a `quote do:` block (backtick-interpolated identifiers --
## `renderAsChoices(`witId`)` at `symex.nim:2520`,
## `processIsolationSpawnWorker(`idLit`, `propSym`)` at
## `fuzzmacro.nim:514`) or its own doc says so directly
## (`saveSymexWitnessImpl`: "Runtime body of `saveSymexWitness`",
## `symex.nim:245`). `canonicalize.nim` (`symexCacheKey`, `canonicalize`)
## is the same: its callers operate on `db: ExampleDatabase`, a value that
## does not exist until the compiled test binary runs, so the cache-key
## computation cannot happen at macro-expansion time either. The
## `engine/`, `optbox.nim`, `db.nim` family is the property-testing
## ENGINE (pipeline phases, the example database, strategy generation) --
## reachable only from `runtime.nim`'s / the PBT driver's own import
## graph, never from the parser. `smt/dsl.nim` (confusable with the
## already-scoped top-level `dsl.nim`) is a pure re-export facade -- zero
## `proc`/`func`/`macro`/`template` declarations of its own, nothing to
## audit. This matches S8x's own conclusion for `runtime.nim`, now
## re-confirmed against every module one hop further out: it "compiles to
## native code, where `let` copies" -- there is no VM-aliasing hazard to
## find there, by construction, not by omission.
##
## The already-scoped `strategy.nim`/`parallel.nim`/`fuzzmacro.nim`/
## `coverage.nim` generic combinators (`oneOf`, `map`, `isLinearisable`,
## `processIsolationSpawnWorker`, `logCmp`, and `symex.nim`'s own
## `renderInto`/`renderAsChoices`/`forAllWithSymexSeeds`/
## `allRaiseFindings`/`sortedKeysOf`/`sortedElemsOf`) are audited (the
## guard walks every top-level routine in a scoped file, not just the
## macro-adjacent ones) but are ALSO runtime-only by the same test: each
## is called only from inside a `quote do:` block or from property-test
## execution, never from a macro's own un-quoted body. They are not
## exempted from the walk (over-inclusion here is free and safe), just
## from the "force a real instantiation" requirement below, since a
## generic instantiation that never runs in the VM cannot hide a VM
## hazard regardless of whether this guard can see it.
##
## ---- Known gaps (different mechanisms, reported and not fixed here) --
##
## - Backtick operator names (`` `==` ``, `` `[]` ``, ...) ARE picked up
##   (the source scan special-cases a leading backtick), but any name the
##   scan cannot parse at all (an unusual multi-line signature, a name
##   this scan's simple lexer mishandles) silently drops that routine from
##   coverage. The scan is structural text, same caveat as S8x's own.
## - The param check's ref-param field graph is walked only 3 levels deep
##   (`collectFieldTypes`'s own `depth` bound) -- unchanged by S8af, which
##   fixed the COMPARISON (`sameType`, was `repr` text) but not this bound.
## - A generic proc that is NEVER instantiated ANYWHERE this test binary
##   reaches (not even via a forced fixture call, S8af's own mechanism)
##   still cannot be classified: `getImpl()` on the bare, un-instantiated
##   generic symbol gives back a tree whose bound names are `nnkIdent`,
##   not `nnkSym` (probed, `probe_bare_generic2.nim`: the SAME guard code
##   that already requires `nameNode.kind == nnkSym` before calling
##   `getTypeInst()` is what silently drops these -- not, as an earlier
##   draft of this note speculated, `getTypeInst` returning a generic
##   placeholder). S8af closes this for every generic proc that IS
##   instantiated somewhere reachable (which, per the scope note above, is
##   every compile-time-VM-reachable one found in this scope today --
##   `dsl_parser.traceOneCallBoundary[T]`, forced via
##   `auditGenericInstantiation`) by forcing the instantiation itself
##   rather than trying to classify the generic tree; a FUTURE generic
##   proc added to compile-time-reachable code and never called anywhere
##   (including by this file's own fixtures) is still only caught by
##   review, same as S8x's own residual gap for plain `let`s.
##
## No walker bump: this is test-only reflection over already-compiled
## modules; the IR is untouched.

import std/[macros, os, strutils, sequtils, tables, unittest]
import nelli/smt/dsl_parser {.all.}
import nelli/smt/dsl_typebridge {.all.}
import nelli/smt/scoped_names {.all.}
import nelli/smt/exn_hierarchy {.all.}
import nelli/smt/stdlib_models {.all.}
import nelli/smt/types {.all.}
import nelli/smt/scan {.all.}  ## RFC-0005 S8af: added to scope, see the file header.
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

const routineSymKinds = {nskProc, nskFunc, nskMethod, nskIterator,
                          nskConverter, nskTemplate, nskMacro}

proc calleeReturnsVar(callNode: NimNode): bool =
  ## RFC-0005 S8af (closes S8ab's "`[]`-via-`nnkCall`" gap). True iff
  ## `callNode` (an already-`unwrapHidden`-ed `nnkCall`) resolves to a
  ## routine whose DECLARED return type is `var T` -- the one signature
  ## shape this Nim VM proves aliases through a proc-call-mediated `[]`:
  ## `tables.[]​(t: var Table[A, B], key: A): var B` (probed,
  ## `probe_vm_table2.nim`: `t["k"].add(99)` after `let v = t["k"]` shows
  ## through `v` in the VM, native copies). A `lent T` return (the
  ## non-`var`-table overload, `[]​(t: Table[A, B], key: A): lent B`) and a
  ## plain value return (string/seq/array SLICING,
  ## `[]​(s: …; x: HSlice[…]): string`/`seq[T]`) both COPY in this VM --
  ## same probe file, `tableLentOverload`. `lent`'s own surface syntax is
  ## unresolved `nnkCommand` (`probe_lent2.nim`), indistinguishable from a
  ## plain call by shape, so `var` (the compiler's own `nnkVarTy` on the
  ## resolved signature) is the only shape-safe signal; widening to "any
  ## proc call" was rejected the same way S8ab rejected "any `[]` call" --
  ## every ordinary `let x = someProc(...)` returning a seq/string/object
  ## BY VALUE would otherwise be flagged.
  if callNode.kind != nnkCall or callNode.len == 0: return false
  let callee = callNode[0]
  if callee.kind != nnkSym or callee.symKind notin routineSymKinds: return false
  var impl: NimNode
  try: impl = callee.getImpl()
  except CatchableError: return false
  if impl.isNil or impl.kind == nnkNilLit or impl.len <= 3: return false
  let formals = impl[3]
  if formals.kind != nnkFormalParams or formals.len == 0: return false
  formals[0].kind == nnkVarTy

proc rootSym(n: NimNode): NimNode =
  ## The base symbol of a `.field`/`[i]`/aliasing-call chain (`ctx.
  ## procScoped.jumpTargets[i]` -> `ctx`; RFC-0005 S8af: `t["k"]` where
  ## `[]` resolves to a `var`-returning overload -> `t`, the receiver
  ## argument, same as `.field`/`[i]`'s own first child).
  result = unwrapHidden(n)
  while true:
    case result.kind
    of nnkBracketExpr, nnkDotExpr:
      if result.len == 0: return
      result = unwrapHidden(result[0])
    of nnkCall:
      if calleeReturnsVar(result) and result.len > 1:
        result = unwrapHidden(result[1])
      else:
        return
    else:
      return

proc rhsAliasKind(n: NimNode): NimNode =
  ## nil: not one of the hazard shapes. Otherwise the (unwrapped) RHS node
  ## to classify by type. RFC-0005 S8af: `nnkCall` joins the original three
  ## (`nnkBracketExpr`/`nnkDotExpr`/`nnkSym`) ONLY when `calleeReturnsVar`
  ## -- see its own doc for why that gate, not "any call", is the right
  ## line.
  let r = unwrapHidden(n)
  if r.kind in {nnkBracketExpr, nnkDotExpr, nnkSym}: return r
  if r.kind == nnkCall and calleeReturnsVar(r): return r
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

proc collectFieldTypes(objTypeSym: NimNode; depth: int; into: var seq[NimNode]) =
  ## Field TYPES (not text) reachable from a ref/object type symbol,
  ## depth-bounded (3, unchanged by S8af -- see the file header's "Known
  ## gaps"): the shape of `paramThenCallerWriteThroughRef(h: Holder; xs:
  ## seq[int])`, where `xs` aliases `h.c.xs` because the CALLER passed the
  ## same location twice. RFC-0005 S8af: collects each field's RESOLVED
  ## type (`getTypeInst()` on the field's own symbol) for comparison via
  ## `sameType` in `walkParams`, not the raw declaration node's `repr` --
  ## a type ALIAS (`type StrIntTable = Table[string, int]`; `xs:
  ## StrIntTable` vs a sibling param `xs: Table[string, int]`) reprs
  ## differently ("StrIntTable" vs "Table[string, int]") but IS the same
  ## type (`sameType`'s own doc: "true... when comparing alias with
  ## original type") -- probed, `probe_alias_mismatch.nim`: the OLD
  ## repr-text compare said `false` on exactly this shape, a real false
  ## negative the fixture below pins.
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
    let fieldNameSym = fld[0]
    if fieldNameSym.kind != nnkSym: continue
    var fieldType: NimNode
    try: fieldType = fieldNameSym.getTypeInst()
    except CatchableError: continue
    if fieldType.isNil: continue
    into.add fieldType
    if fieldType.kind == nnkSym:
      collectFieldTypes(fieldType, depth - 1, into)

proc walkParams(impl: NimNode; owner: string; hits: var seq[string]) =
  if impl.len <= 6: return
  let formals = impl[3]
  if formals.kind != nnkFormalParams: return
  let body = impl[6]
  var candidates: seq[tuple[nm: string, t: NimNode]]
  var siblingFieldTypes: seq[NimNode]
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
        collectFieldTypes(t, 3, siblingFieldTypes)
    elif t.typeKind in objKinds:
      candidates.add (macros.strVal(sym), t)
  if siblingFieldTypes.len == 0: return
  for (nm, t) in candidates:
    # RFC-0005 S8af: `sameType`, not `t.repr in siblingFieldReprs` -- see
    # `collectFieldTypes`'s own doc for the alias false negative this
    # replaces.
    var matched = false
    for ft in siblingFieldTypes:
      if sameType(t, ft): matched = true; break
    if matched:
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
    if s.symKind notin routineSymKinds:
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

macro auditGenericInstantiation(callExpr: typed; fileTag: static string): untyped =
  ## RFC-0005 S8af: closes S8ab's "generic procs ... silently skipped" gap.
  ## Unlike `auditOne` (which resolves a BARE name and so always gets the
  ## GENERIC, un-instantiated symbol -- `getImpl()` on THAT gives back a
  ## tree whose bound names are `nnkIdent`, not `nnkSym`; probed,
  ## `probe_bare_generic2.nim`), `callExpr` here is an actual CALL
  ## EXPRESSION. Passing a call (not a name) as a `typed` macro argument
  ## forces the compiler to produce the fully-substituted INSTANTIATED
  ## symbol as the call's own callee -- `getImpl()` on THAT returns the
  ## typed body with every generic parameter resolved to the concrete type
  ## the call used (probed, `probe_generic_inst.nim`:
  ## `probeCall(genericHelper(@[1, 2, 3]))` sees `let y`'s
  ## `getTypeInst().typeKind == ntySequence`, not a generic placeholder).
  ## The caller supplies a REAL call (real argument types, closures
  ## included) so this only ever audits an instantiation that could
  ## actually occur, never a synthetic one.
  result = newEmptyNode()
  if callExpr.kind notin {nnkCall, nnkCommand} or callExpr.len == 0: return
  let callee = callExpr[0]
  if callee.kind != nnkSym or callee.symKind notin routineSymKinds: return
  var impl: NimNode
  try:
    impl = callee.getImpl()
  except CatchableError as e:
    walkErrs.add fileTag & ": " & macros.strVal(callee) &
      " (forced instantiation) getImpl raised: " & e.msg
    return
  if impl.isNil or impl.kind == nnkNilLit: return
  let owner = fileTag & ":" & macros.strVal(callee) & "[instantiated]"
  walkLets(impl, owner, letHits)
  walkParams(impl, owner, paramHits)

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
# RFC-0005 S8af: added to scope -- see the file header's item above.
auditFile(smtDir, "scan.nim")
auditFile(rootDir, "symex.nim")
auditFile(rootDir, "fuzzmacro.nim")
auditFile(rootDir, "derive.nim")
auditFile(rootDir, "dsl.nim")
auditFile(rootDir, "coverage.nim")
auditFile(rootDir, "mutation.nim")
auditFile(rootDir, "concolic.nim")
auditFile(rootDir, "strategy.nim")
auditFile(rootDir, "parallel.nim")

# ---- RFC-0005 S8af: forced generic instantiation, real production scope -----
#
# `traceOneCallBoundary[T]` (`dsl_parser.nim`) is the one compile-time-VM-
# reachable generic proc this scope's own audit found (see the file
# header's scope note for why every OTHER generic proc found here is
# runtime-only and therefore not forced). Its own doc names its two real
# instantiations: `seq[NimNode]` (`collectStringBackedByteSeqParamsImpl`'s
# own `getCalleeMarked`/`isMarked` pair) and `HashSet[string]`
# (`collectIntOffsetParamsImpl`'s). `seq[NimNode]` is forced here with
# minimal closures matching the real signature -- never called, same as
# the RED fixtures below, present only to be typed-checked (and thereby
# instantiated).

proc s8afFxGetCalleeMarked(calleeImpl: NimNode): seq[NimNode] = @[]
proc s8afFxIsMarked(marked: seq[NimNode], formalSym: NimNode): bool = false
proc s8afFxOnMatch(argNode: NimNode) = discard

auditGenericInstantiation(
  traceOneCallBoundary[seq[NimNode]](
    newEmptyNode(), s8afFxGetCalleeMarked, s8afFxIsMarked, s8afFxOnMatch),
  "dsl_parser.nim")

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

# ---- RFC-0005 S8af RED fixtures ----------------------------------------

proc fxTableBracketAliasShape(): int =
  ## S8af gap 1 positive: Table's mutable `[]` overload
  ## (`[]​(t: var Table[A, B], key: A): var B`) returns a real alias in
  ## this VM -- typed as `nnkCall`, not `nnkBracketExpr`, so S8ab's own
  ## RHS-shape check missed it entirely. `calleeReturnsVar` classifies it
  ## by the resolved callee's `var` return, not by seeing a `[]` at all.
  var t = initTable[string, seq[int]]()
  t["k"] = @[1, 2, 3]
  let v = t["k"]                             # RFC-0005 S8af hazard
  t["k"].add 99
  v.len

proc fxStringSliceNotFlagged(s: string): string =
  ## S8af gap 1 control: string slicing lowers through the SAME `[]`-call
  ## syntax as `fxTableBracketAliasShape`'s hazard, but its resolved
  ## callee (`[]​(s: string; x: HSlice[…]): string`) returns a plain
  ## value, not `var T` -- must NOT be flagged. This is the exact false
  ## positive S8ab's own note rejected "any `[]` call" for.
  let v = s[0 .. ^2]
  v

proc fxTableLentNotFlagged(t: Table[string, seq[int]]): int =
  ## S8af gap 1 control: the read-only `[]` overload
  ## (`[]​(t: Table[A, B], key: A): lent B`) COPIES in this VM (probed,
  ## `probe_vm_table2.nim`'s `tableLentOverload`) -- must NOT be flagged
  ## even though it is also an `nnkCall`.
  let v = t["k"]
  v.len

type
  FxIntSeqAlias = seq[int]
  FxInnerAlias = object
    xs: FxIntSeqAlias
  FxHolderAlias = ref object
    c: FxInnerAlias

proc fxParamAliasViaTypeAlias(h: FxHolderAlias; xs: seq[int]): int =
  ## S8af gap 2 positive: `h.c.xs` is declared through a TYPE ALIAS
  ## (`FxIntSeqAlias = seq[int]`), otherwise identical to
  ## `fxParamAliasShape` above (same mutation, `.add`, so `bodyMutatesRoot`
  ## sees it the same way -- the only variable is the field's declared
  ## type). The OLD repr-text comparison ("FxIntSeqAlias" != "seq[int]")
  ## MISSED this real `paramThenCallerWriteThroughRef` hazard -- `xs` may
  ## be `h.c.xs`, passed twice by the caller. `sameType` sees through the
  ## alias and catches it (probed, `probe_alias_mismatch.nim`, same shape
  ## with `Table[string, int]`).
  h.c.xs.add 3
  xs.len

proc fxGenericAliasShape[T](container: seq[T]): T =
  ## S8af gap 3: a generic proc's OWN `let`, hazard-shaped only once `T`
  ## is resolved to a non-scalar. `container[0]` is `nnkBracketExpr`, one
  ## of the original three shapes -- this fixture isolates gap 3 (generic
  ## instantiation coverage) from gap 1 (the new `nnkCall` shape).
  let v = container[0]        # RFC-0005 S8af hazard, once T is non-scalar
  v

const fixtureNames = @["preFixResolveBreakShape", "preFixEnsureProcRegisteredShape",
                       "fxParamAliasShape", "fxTableBracketAliasShape",
                       "fxStringSliceNotFlagged", "fxTableLentNotFlagged",
                       "fxParamAliasViaTypeAlias", "fxGenericAliasShape"]
genAudits(fixtureNames, thisFile)

# `fxGenericAliasShape` is walked TWICE: once above, bare, via `genAudits`
# (proving the OLD/bare-name path sees nothing -- its body's bound names
# are `nnkIdent`, not `nnkSym`, for an un-instantiated generic), and once
# here, FORCED to a concrete `T = seq[int]` via `auditGenericInstantiation`
# (proving the NEW path catches the hazard once real). Both results are
# distinguished by owner-tag suffix in the tests below.
auditGenericInstantiation(fxGenericAliasShape[seq[int]](@[@[1, 2, 3]]), thisFile)

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
    check fixtureLetHits.anyIt(it.contains("preFixResolveBreakShape") and it.contains("JumpTarget"))
    check fixtureLetHits.anyIt(it.contains("preFixEnsureProcRegisteredShape") and
                                it.contains("ProcScopedCollectors"))

  test "RED: the walker flags a non-var param aliased through a mutated ref sibling":
    check fixtureParamHits.anyIt(it.contains("fxParamAliasShape") and it.contains("param xs"))

  test "S8af RED: Table's var-returning `[]` (nnkCall) is flagged, string slicing and the lent overload are not":
    check fixtureLetHits.anyIt(it.contains("fxTableBracketAliasShape") and
                                it.contains("let v") and it.contains("seq[int]"))
    check not fixtureLetHits.anyIt(it.contains("fxStringSliceNotFlagged"))
    check not fixtureLetHits.anyIt(it.contains("fxTableLentNotFlagged"))

  test "S8af RED: a param aliased only through a type ALIAS is flagged (sameType, not repr text)":
    check fixtureParamHits.anyIt(it.contains("fxParamAliasViaTypeAlias") and it.contains("param xs"))

  test "S8af RED: a generic proc's hazard is invisible to the bare/un-instantiated walk":
    # The bare-walk owner tag has no "[instantiated]" suffix -- distinct
    # from the forced-instantiation hit the GREEN test below expects.
    check not fixtureLetHits.anyIt(it.contains(thisFile & ":fxGenericAliasShape:"))

  test "S8af GREEN: the SAME generic proc's hazard is caught once a real instantiation is forced":
    check fixtureLetHits.anyIt(it.contains("fxGenericAliasShape[instantiated]") and
                                it.contains("let v") and it.contains("seq[int]"))

  test "S8af GREEN: the one compile-time-reachable generic proc in the real scope" &
       " (traceOneCallBoundary[seq[NimNode]]) instantiates and audits cleanly":
    check realScopeErrs.len == 0
    check not realScopeLetHits.anyIt(it.contains("traceOneCallBoundary[instantiated]"))
    check not realScopeParamHits.anyIt(it.contains("traceOneCallBoundary[instantiated]"))

  test "GREEN: no getImpl/audit-machinery error across the 16-file scope":
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
