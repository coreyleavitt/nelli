## RFC-0005 (soundness channels) slices S8ab + S8af + S8ah -- S8x's
## remainder: a TYPE-AWARE mechanical guard for the compile-time VM
## `let`-aliasing hazard, over the whole scope S8x's own hand audit
## covered.
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
## S8ah (RFC-0005 S8ah, search this file for "S8ah" to find each change)
## closes S8af's own four remaining gaps:
## 1. **Macro reachability + generic-instantiation coverage.** S8af traced,
##    BY HAND, which ONE of the scope's 37 generic-bracketed routines is
##    ever called directly (unquoted) from a macro's own compile-time-VM
##    code, versus only emitted inside `quote do:`. S8ah makes that trace
##    MECHANICAL (`vmGuardWalkForGenericCalls`, in
##    `nelli/smt/vm_alias_guard.nim`): walk every macro's typed
##    `getImpl()` tree for a LIVE call whose resolved callee is one of the
##    37 -- a call inside `quote do:` lowers to `getAst`/tree-construction
##    code and never shows up as a live call to the target (probed,
##    `probe_quotedo_reach.nim`), so no special-casing of quoted regions is
##    needed. Every generic the walk finds VM-reachable must have a forced
##    `vmGuardAuditInstantiation` audit (S8af's own forcing mechanism) or
##    the guard fails closed -- see the completeness tests below and
##    `vm_alias_guard.nim`'s own self-audit.
## 2. **Field-graph depth.** `collectFieldTypes`'s old 3-level bound is
##    replaced with a full walk guarded by a `sameType`-keyed VISITED LIST
##    (not a depth counter) -- the bound's only real job was stopping an
##    infinite loop on a self-referential type, which a visited set does
##    at any depth.
## 3. **Uninstantiated generics.** Once reachability (item 1) is
##    mechanical, "never instantiated" classifies itself: every VM-
##    reachable generic gets forced; every one the mechanical walk finds
##    NOT VM-reachable is proven unreachable BY THAT SAME WALK, not by a
##    manual claim.
## 4. **Build-time check.** The exact same mechanism (moved into
##    `nelli/smt/vm_alias_guard.nim`, a reusable library this test file
##    now imports instead of keeping its own copy) is wired into
##    `symex.nim`'s and `concolic.nim`'s own trailing `when
##    defined(nelliVmAliasAudit)` blocks -- a genuine build-time gate
##    (`doAssert`, not `check`), opt-in so an ordinary `import nelli/symex`
##    compile pays nothing, with CI turning the define on in every leg
##    (`.github/workflows/{fuzzer-mingw,fuzzer-msvc,symex-mingw}.yaml`).
##
## S8ak (search this file for "S8ak" to find each change) closes S8ah's own
## two remaining gaps:
## 1. **Zero-required-argument macros.** `vmGuardAuditNames` used to
##    generate `vmGuardAuditRoutine(ident(nm), fileTag)` and let the
##    compiler re-resolve `ident(nm)` as a fresh `typed` ARGUMENT
##    EXPRESSION -- Nim auto-invokes a macro with no required parameters
##    referenced bare in that position (probed: its own RESULT, e.g. an
##    `nnkIntLit`, arrives in place of its symbol), so such a macro's body
##    was never walked at all, a silent false negative. Now resolved via
##    `bindSym(nm, brForceOpen)` (`nelli/smt/vm_alias_guard.nim`'s own doc
##    has the full probed before/after). No real macro in the current
##    16-file scope has zero required parameters (S8ah's own note already
##    confirmed this), so this is a future-proofing fix, not a current
##    real-scope hazard.
## 2. **`extractTopLevelNames`/`extractTopLevelMacroNames`.** Replaced the
##    column-0 source-TEXT scan with `parseStmt(staticRead(path))`, reading
##    each top-level definition node's own name -- handles a backtick
##    operator and a routine whose keyword and name sit on different
##    physical lines the same way it handles an ordinary signature, since a
##    real parser has no line boundaries to be confused by. Re-derived the
##    real-scope counts mechanically against the new scan: still 22 macros,
##    still 37 generics, still exactly 1 VM-reachable -- no change.
##
## S8al (search this file for "S8al" to find each change) closes S8ak's own
## two remaining gaps:
## 1. **The force-and-audit half of the guard, exercised against a fixture
##    generic.** In the real 16-file scope, the "a VM-reachable generic with
##    no forced-instantiation audit fails the completeness check closed"
##    comparison has only ever had ONE row to evaluate
##    (`traceOneCallBoundary`, always forced) -- its FAILING branch had
##    never actually run. Two new fixture generics
##    (`s8alFxForcedHazardGeneric`/`s8alFxUnforcedHazardGeneric`), each
##    reachable from its own zero-arg fixture macro, prove both outcomes:
##    the forced one's hazard is reported, and the never-forced one is
##    correctly reported unforced by the SAME comparison -- confirmed by
##    deliberately skipping the forced generic's `vmGuardAuditInstantiation`
##    call (podman, reverted after confirming): both of its own tests go
##    RED (the hazard disappears from `fixtureLetHits`, and the
##    completeness comparison's `unforced.len` goes from 0 to 1).
## 2. **`vmGuardAuditMacroReachWithSpecs`, resolved by symbol.** This
##    test-only reachability hook took the macro SYMBOL directly as a
##    `typed` argument -- the exact auto-invoke trap S8ak's item 1 already
##    fixed for `vmGuardAuditNames` (a genuinely zero-required-argument
##    macro referenced bare in that position is auto-invoked by Nim, never
##    resolved to its own symbol). RED (observed against the pre-fix
##    signature, podman, reverted after confirming): a genuinely zero-arg
##    macro passed this way was silently auto-invoked and never walked.
##    Fixed with the same `bindSym`-via-nested-macro technique
##    (`vmGuardAuditOneSymReachOnly`, `nelli/smt/vm_alias_guard.nim`) --
##    which also let `s8ahFxDirectGenericCall`/`s8ahFxQuotedGenericCall`
##    drop the dummy required parameter they carried purely to dodge the
##    trap; both are now genuinely zero-arg and still correctly flagged.
##
## S8x (`tests/tsymex_rfc0005_s8x_vm_alias.nim`) found and fixed the two
## live-at-the-time hazards (`resolveBreak`'s `let t = ctx.procScoped.
## jumpTargets[i]`, `ensureProcRegistered`'s `let savedProcScoped = ctx.
## procScoped`) but its own mechanical pin only source-scans ONE pattern
## in ONE file: no `let` in `dsl_parser.nim` binding a `ctx.procScoped`
## record or element. Its own "different mechanisms, reported and not
## fixed here" note is explicit that this is too narrow. This slice closes
## that gap with a TYPED-AST walker (Option 1 of the slice's brief)
## instead of text.
##
## ---- What the walker does (now living in `nelli/smt/vm_alias_guard.nim`,
## see its own header for the mechanism) -------------------------------
##
## For every top-level `proc`/`func`/`macro`/`template`/`iterator`/
## `converter` in the audited files (found by a column-0 source scan --
## structural, not semantic):
##
## 1. `getImpl()` on the resolved symbol (private procs need the compiler
##    to see them: `{.all.}` on each `import` below) gives the TYPED body.
## 2. Every `nnkLetSection` is walked for the three hazard shapes
##    (`nnkBracketExpr`/`nnkDotExpr`/bare `nnkSym`), excluding the
##    compiler's own tuple-unpack desugaring.
## 3. The bound NAME's `getTypeInst()` decides safety: a `ref` or a scalar
##    is safe; `ntyObject`/`ntyTuple`/`ntySequence`/`ntyString`/`ntySet`/
##    `ntyArray` is the hazard class.
##
## Non-`var` PARAMETERS get a separate, narrower check gated on an ACTUAL
## in-place mutation of a same-shaped `ref` sibling
## (`paramThenCallerWriteThroughRef`'s own shape) -- a structural-only
## version (any non-`var` value parameter) produced 265 false-positive
## hits and was rejected.
##
## ---- Scope ----------------------------------------------------------
##
## S8x's original 15 files PLUS `smt/scan.nim` (S8af) -- the six `smt/`
## front-end modules, `symex.nim`'s macro helpers, and the eight other
## macro-declaring top-level modules (`fuzzmacro`, `derive`, `dsl`,
## `coverage`, `mutation`, `concolic`, `strategy`, `parallel`). `{.all.}`
## is required on every one: the two historical hazards were both
## UNEXPORTED procs.
##
## `runtime.nim`/`runtime_strings.nim` (and everything they pull in) and
## `smt/dsl.nim` (a pure re-export facade) are OUT of scope: they execute
## only at TEST RUNTIME, never at macro-expansion time -- see S8af's own
## note for the full per-file confirmation.
##
## ---- Known gaps (different mechanisms, reported and not fixed here) --
##
## - Backtick operator names ARE picked up, but a name this scan's simple
##   lexer mishandles (an unusual multi-line signature) silently drops
##   that routine from coverage.
## - A generic proc that is NEVER instantiated ANYWHERE this test binary
##   reaches (not even via a forced fixture call) still cannot be
##   classified -- S8ah closes this for every VM-REACHABLE generic found
##   by the mechanical walk (forced via `vmGuardAuditInstantiation`); a
##   generic that is genuinely unreachable from the VM needs no forcing
##   (it cannot hide a VM hazard, since it never runs in the VM), which the
##   same walk also proves, mechanically, rather than by manual trace.
##
## No walker bump: this is test-only reflection over already-compiled
## modules; the IR is untouched.

import std/[macros, os, strutils, sequtils, tables, unittest]
import nelli/smt/vm_alias_guard
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

# ---- RFC-0005 S8ah: the walker itself, the 37-generic reachability specs,
# the compile-time accumulators and the audit macros now all live in
# `nelli/smt/vm_alias_guard.nim` (imported above), shared with the SAME
# mechanism's build-time use in `symex.nim`/`concolic.nim`. This file keeps
# only: the per-scope-file audit wiring, its own RED/GREEN fixtures, and
# the allowlist/completeness assertions.

template auditFile(dir, fname: string) =
  const path = dir / fname
  const names = extractTopLevelNames(path)
  vmGuardAuditNames(names, fname)

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
# runtime-only and therefore not forced -- S8ah: now proven mechanically,
# not just traced by hand, by `realScopeReachHits`/the completeness test
# below). Its own doc names its two real instantiations: `seq[NimNode]`
# (`collectStringBackedByteSeqParamsImpl`'s own `getCalleeMarked`/`isMarked`
# pair) and `HashSet[string]` (`collectIntOffsetParamsImpl`'s). `seq[NimNode]`
# is forced here with minimal closures matching the real signature -- never
# called, same as the RED fixtures below, present only to be typed-checked
# (and thereby instantiated).

proc s8afFxGetCalleeMarked(calleeImpl: NimNode): seq[NimNode] = @[]
proc s8afFxIsMarked(marked: seq[NimNode], formalSym: NimNode): bool = false
proc s8afFxOnMatch(argNode: NimNode) = discard

vmGuardAuditInstantiation(
  traceOneCallBoundary[seq[NimNode]](
    newEmptyNode(), s8afFxGetCalleeMarked, s8afFxIsMarked, s8afFxOnMatch),
  "dsl_parser.nim")

const realScopeLetHits = block:
  var dedup: seq[string]
  for h in vmGuardLetHits:
    if h notin dedup: dedup.add h
  dedup

const realScopeParamHits = block:
  var dedup: seq[string]
  for h in vmGuardParamHits:
    if h notin dedup: dedup.add h
  dedup

const realScopeReachHits = block:
  var dedup: seq[string]
  for h in vmGuardReachHits:
    if h notin dedup: dedup.add h
  dedup

const realScopeErrs = vmGuardWalkErrs

# RFC-0005 S8ah item 1 correction: the S8ah fence title (and S8af's own
# residual note) both say "17 macros". Counted mechanically here
# (`extractTopLevelMacroNames`, the same column-0 scan `auditFile` already
# uses for every routine kind) rather than trusting that figure: the real
# 16-file scope has 22 UNIQUE macro names (across 7 of the 16 files;
# `dsl_parser.nim`, `dsl_typebridge.nim`, `scoped_names.nim`,
# `exn_hierarchy.nim`, `stdlib_models.nim`, `types.nim` and `scan.nim`
# declare none). "17" does not match either the unique-name count (22) or
# any other natural reading (raw `macro` defs, which is also 22 here --
# no file in scope overloads a macro name the way `coverage.nim` overloads
# `logCmp` as a proc). Per the "RFC status lines lag git" lesson, the
# figure is corrected in the As-landed note rather than propagated.
const realScopeMacroNames = block:
  var names: seq[string]
  for fname in ["dsl_parser.nim", "dsl_typebridge.nim", "scoped_names.nim",
                "exn_hierarchy.nim", "stdlib_models.nim", "types.nim", "scan.nim"]:
    for n in extractTopLevelMacroNames(smtDir / fname):
      if n notin names: names.add n
  for fname in ["symex.nim", "fuzzmacro.nim", "derive.nim", "dsl.nim",
                "coverage.nim", "mutation.nim", "concolic.nim", "strategy.nim",
                "parallel.nim"]:
    for n in extractTopLevelMacroNames(rootDir / fname):
      if n notin names: names.add n
  names

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

# RFC-0005 S8ak: a reachable/forced-generic key's `file:name` identity,
# stripping the trailing `@<line>`. S8ad shifted `traceOneCallBoundary`
# from `dsl_parser.nim:7269` to `:7270` by editing ABOVE it; the hardcoded
# "@7269" this const used to carry went stale the instant that landed, and
# re-typing "@7270" here would only move the same trap one edit further
# out. Comparing identity (name+file) instead of the full key, below,
# means no edit anywhere in `dsl_parser.nim` can ever desync this list
# from reality again -- the production fix (`vm_alias_guard.nim`'s own
# doc, item 6) makes the same change for the same reason.
proc genericKeyPrefix(k: string): string =
  let at = k.rfind('@')
  if at < 0: k else: k[0 ..< at]

# RFC-0005 S8ah: every generic the mechanical reachability walk finds
# VM-reachable ANYWHERE in the real 16-file scope must appear here, with a
# corresponding `vmGuardAuditInstantiation` call somewhere in this compile
# (this file's own forced call above, OR -- since `vmGuardForcedGenerics`
# is a GLOBAL compile-time list -- one made by `vm_alias_guard.nim`'s own
# self-audit, which this file also pulls in by importing that module).
const realScopeForcedGenerics = [
  "dsl_parser.nim:traceOneCallBoundary",
]

# `vmGuardForcedGenerics` is `{.compileTime.}` (VM-only storage); snapshot
# it into a `const` here so the runtime `check`s below can read it.
const globallyForcedGenerics = vmGuardForcedGenerics

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
  ## (`[]​(t: Table[A, B], key: A): lent B`) COPIES in this VM -- must NOT
  ## be flagged even though it is also an `nnkCall`.
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
  ## `fxParamAliasShape` above. The OLD repr-text comparison MISSED this
  ## real `paramThenCallerWriteThroughRef` hazard. `sameType` sees through
  ## the alias and catches it.
  h.c.xs.add 3
  xs.len

proc fxGenericAliasShape[T](container: seq[T]): T =
  ## S8af gap 3: a generic proc's OWN `let`, hazard-shaped only once `T`
  ## is resolved to a non-scalar. `container[0]` is `nnkBracketExpr`, one
  ## of the original three shapes -- this fixture isolates gap 3 (generic
  ## instantiation coverage) from gap 1 (the new `nnkCall` shape).
  let v = container[0]        # RFC-0005 S8af hazard, once T is non-scalar
  v

# ---- RFC-0005 S8ah RED fixtures: field-graph depth ---------------------
#
# The OLD `collectFieldTypes(objTypeSym, depth = 3, ...)` misses a hazard
# buried more than 3 `.field` hops deep. Probed against the exact code
# below (`probe_fielddepth_red.nim`, not part of the shipped guard): the
# old bound's own `siblingFieldTypes` stays EMPTY for this shape
# (`siblingFieldTypes.len=0 matched(xs)=false`) -- a real false negative
# the unbounded, visited-set-guarded walk in `vm_alias_guard.nim` now
# fixes.

type
  FxDeep5 = ref object
    xs: seq[int]
  FxDeep4 = ref object
    nxt: FxDeep5
  FxDeep3 = ref object
    nxt: FxDeep4
  FxDeep2 = ref object
    nxt: FxDeep3
  FxHolderDeep = ref object
    nxt: FxDeep2

proc fxParamAliasDeepShape(h: FxHolderDeep; xs: seq[int]): int =
  ## S8ah positive: the shared field type (`seq[int]`) is reachable only
  ## 5 levels down (`h.nxt.nxt.nxt.nxt.xs`), past the OLD depth-3 bound.
  h.nxt.nxt.nxt.nxt.xs.add 3
  xs.len

type
  FxCyclicInner = ref object
    self: FxCyclicInner   # self-referential: a naive unbounded walk with
                           # no visited set recurses on this forever.
    xs: seq[int]
  FxCyclicHolder = ref object
    link: FxCyclicInner

proc fxParamAliasCyclicShape(h: FxCyclicHolder; xs: seq[int]): int =
  ## S8ah: a hazard reachable THROUGH a self-referential type
  ## (`FxCyclicInner.self: FxCyclicInner`). Proves the visited-set both
  ## catches the hazard (at `h.link.xs`, depth 2) AND terminates: without
  ## a visited set (a naive "just remove the depth bound" change), walking
  ## `FxCyclicInner`'s fields re-enters `FxCyclicInner` through `self`
  ## forever. This fixture compiling at all is part of the proof.
  h.link.xs.add 3
  xs.len

# ---- RFC-0005 S8ah RED/GREEN fixtures: macro reachability of a generic -----
#
# `s8ahFxDirectGenericCall` calls a generic DIRECTLY (unquoted) at
# compile-time-VM-execution time; `s8ahFxQuotedGenericCall` only emits the
# SAME call inside `quote do:` (so the generated code, which runs at
# property-test RUNTIME, calls it -- this must NOT be flagged as
# VM-reachable). Both reuse `fxGenericAliasShape` (above) as the generic
# under test, forced via `vmGuardAuditInstantiation` once flagged.
#
# RFC-0005 S8al: both are genuinely zero-required-argument macros -- no
# dummy parameter. Before S8al, `vmGuardAuditMacroReachWithSpecs` took the
# macro SYMBOL directly as a `typed` argument, which Nim auto-invokes for a
# zero-arg macro referenced bare in that position (probed separately:
# yields `nnkIntLit`, the RESULT of calling it, never `nnkSym`), so each
# fixture needed a required dummy param purely to dodge that. S8al moved
# this hook onto the same `bindSym`-by-name technique `vmGuardAuditNames`
# already uses (S8ak) -- pure name resolution, never an expression
# evaluation, so a zero-arg macro is never auto-invoked -- and the dummy
# param is no longer needed; see `vmGuardAuditMacroReachWithSpecs`'s own
# doc.

macro s8ahFxDirectGenericCall(): untyped =
  let v = fxGenericAliasShape(@[1, 2, 3])
  newLit(v)

macro s8ahFxQuotedGenericCall(): untyped =
  quote do:
    discard fxGenericAliasShape(@[1, 2, 3])

# ---- RFC-0005 S8ak RED/GREEN fixture: a GENUINELY zero-required-argument
# macro -- no dummy param, unlike the pair just above, which specifically
# NEEDED one to dodge this very bug -- directly calling a REAL registered
# generic (`just`, `strategy.nim:130`).
#
# Before S8ak's fix, `vmGuardAuditNames` resolved each discovered name via
# `newCall(bindSym"vmGuardAuditRoutine", ident(nm), newLit(fileTag))`: the
# generated `vmGuardAuditRoutine(ident(nm), fileTag)` call is re-semchecked
# by the compiler, and Nim auto-invokes a zero-required-argument macro
# referenced bare in that `typed`-argument expression position (same
# mechanism as the dummy-param note above) -- `vmGuardAuditRoutine` then
# receives this macro's own RESULT (an `nnkIntLit`), never its symbol, and
# silently records nothing. `bindSym` (S8ak) resolves the name without
# evaluating it, so the fix must flag this reachable.
macro s8akFxZeroArgDirectGenericCall(): untyped =
  discard just(5)
  newLit(0)

const fixtureNames = @["preFixResolveBreakShape", "preFixEnsureProcRegisteredShape",
                       "fxParamAliasShape", "fxTableBracketAliasShape",
                       "fxStringSliceNotFlagged", "fxTableLentNotFlagged",
                       "fxParamAliasViaTypeAlias", "fxGenericAliasShape",
                       "fxParamAliasDeepShape", "fxParamAliasCyclicShape",
                       "s8akFxZeroArgDirectGenericCall"]
vmGuardAuditNames(fixtureNames, thisFile)

# RFC-0005 S8ah: the reachability-mechanism fixtures use their OWN small
# spec list (naming this file's own `fxGenericAliasShape`, not one of the
# real 37) via `vmGuardAuditMacroReachWithSpecs` -- see that macro's own
# doc for why: the production pipeline (`vmGuardAuditNames` above) only
# ever searches for the REAL 37 registered generics, so it would never
# flag a call to a test-only fixture generic.
const fixtureGenericSpecs: seq[GenericRoutineSpec] = @[("fxGenericAliasShape", thisFile, 0)]
vmGuardAuditMacroReachWithSpecs("s8ahFxDirectGenericCall", thisFile, fixtureGenericSpecs)
vmGuardAuditMacroReachWithSpecs("s8ahFxQuotedGenericCall", thisFile, fixtureGenericSpecs)

# `fxGenericAliasShape` is walked TWICE: once above, bare, via
# `vmGuardAuditNames` (proving the OLD/bare-name path sees nothing -- its
# body's bound names are `nnkIdent`, not `nnkSym`, for an un-instantiated
# generic), and once here, FORCED to a concrete `T = seq[int]` via
# `vmGuardAuditInstantiation` (proving the NEW path catches the hazard
# once real). Both results are distinguished by owner-tag suffix in the
# tests below.
vmGuardAuditInstantiation(fxGenericAliasShape[seq[int]](@[@[1, 2, 3]]), thisFile)

# RFC-0005 S8ak: snapshot AFTER the forcing call just above, so this
# includes `fxGenericAliasShape`'s own forced key alongside whatever
# `vm_alias_guard.nim`'s own import-time self-audit already forced
# (`globallyForcedGenerics`, snapshotted earlier, captures only the
# latter -- this file's OWN forcing above runs later in module-init
# order, so it is NOT yet in that earlier snapshot).
const fixtureForcedGenerics = vmGuardForcedGenerics

# ---- RFC-0005 S8al: the force-and-audit half of the guard, exercised
# end-to-end with a FIXTURE generic -- `fxGenericAliasShape` above is
# forced too, but its own reachability is proven only through the
# fixture-SPECS-only mechanism test (`vmGuardAuditMacroReachWithSpecs`
# directly), never through the SAME "found reachable -> must be forced or
# the completeness check fails closed" comparison the real 16-file scope's
# own test ("GREEN: every generic the real 16-file scope finds
# VM-reachable has a forced-instantiation audit", below) and
# `vm_alias_guard.nim`'s own self-audit `doAssert unforced.len == 0` both
# run in production. In the real scope, that comparison has only ever had
# ONE row to check (`traceOneCallBoundary`, always forced) -- it has never
# been exercised against a row that is REACHABLE-BUT-UNFORCED, so a
# regression that broke the comparison itself (e.g. computing `unforced`
# from the wrong list, or comparing the wrong key) could not have been
# caught by the real scope alone. Two near-identical generics, each
# reachable from its own zero-arg fixture macro (S8al: no dummy param
# needed now -- see `vmGuardAuditMacroReachWithSpecs`'s own doc): one gets
# a forced-instantiation audit, the other deliberately does not.

proc s8alFxForcedHazardGeneric[T](container: seq[T]): T =
  ## Forced below via `vmGuardAuditInstantiation` -- its let-aliasing
  ## hazard (once `T` is non-scalar) must be reported, same shape as
  ## `fxGenericAliasShape`'s own hazard.
  let v = container[0]        # RFC-0005 S8al hazard, once T is non-scalar
  v

proc s8alFxUnforcedHazardGeneric[T](container: seq[T]): T =
  ## Deliberately never forced: no `vmGuardAuditInstantiation` call for
  ## this generic exists anywhere in this file. Proves the completeness
  ## comparison fails CLOSED -- flags a reachable-but-unforced generic,
  ## rather than silently treating "never checked" as "fine".
  let v = container[0]        # RFC-0005 S8al hazard, once T is non-scalar
  v

macro s8alFxDirectForcedGenericCall(): untyped =
  let v = s8alFxForcedHazardGeneric(@[1, 2, 3])
  newLit(v)

macro s8alFxDirectUnforcedGenericCall(): untyped =
  let v = s8alFxUnforcedHazardGeneric(@[1, 2, 3])
  newLit(v)

const s8alFixtureSpecs: seq[GenericRoutineSpec] = @[
  ("s8alFxForcedHazardGeneric", thisFile, 0),
  ("s8alFxUnforcedHazardGeneric", thisFile, 0),
]
vmGuardAuditMacroReachWithSpecs("s8alFxDirectForcedGenericCall", thisFile, s8alFixtureSpecs)
vmGuardAuditMacroReachWithSpecs("s8alFxDirectUnforcedGenericCall", thisFile, s8alFixtureSpecs)

# Force ONLY `s8alFxForcedHazardGeneric`'s instantiation -- the sibling
# generic above is left unforced on purpose (see its own doc). Confirmed
# (podman, deleted after confirming): skipping this call -- the force path
# breaking the way a future regression plausibly could -- turns both the
# "hazard is reported" and "completeness comparison passes" tests below
# RED (`unforced.len was 1`, and `fixtureLetHits` loses the
# `[instantiated]` hit), proving they actually exercise the force-and-audit
# path rather than passing vacuously.
vmGuardAuditInstantiation(
  s8alFxForcedHazardGeneric[seq[int]](@[@[1, 2, 3]]), thisFile)

# Snapshot AFTER the forcing call just above -- same reasoning as
# `fixtureForcedGenerics`'s own doc above.
const s8alFixtureForcedGenerics = vmGuardForcedGenerics

const fixtureLetHits = block:
  var dedup: seq[string]
  for h in vmGuardLetHits:
    if h.startsWith(thisFile) and h notin realScopeLetHits and h notin dedup: dedup.add h
  dedup

const fixtureParamHits = block:
  var dedup: seq[string]
  for h in vmGuardParamHits:
    if h.startsWith(thisFile) and h notin realScopeParamHits and h notin dedup: dedup.add h
  dedup

const fixtureReachHits = block:
  var dedup: seq[string]
  for h in vmGuardReachHits:
    if h.startsWith(thisFile) and h notin realScopeReachHits and h notin dedup: dedup.add h
  dedup

# ---- RFC-0005 S8ak: extractTopLevelNames/extractTopLevelMacroNames, now
# parsed from the module AST rather than scanned from source text --------
#
# `tests/s8ak_scan_fixture.nim` is a small, never-imported fixture source
# (syntactically valid, not necessarily semantically valid -- it is only
# ever `parseStmt`-ed, never compiled) carrying three shapes: a routine
# whose keyword and name sit on different physical lines (RED under the
# OLD column-0 scan: its first line, `"proc"`, does not satisfy
# `line.startsWith("proc ")`, so the name is never even searched for), an
# ordinary single-line backtick operator (already correct under the old
# scan -- pinned here as a non-regression), and a signature whose
# parameter list spans several lines (also already correct under the old
# scan, since only the first line matters there -- pinned because the
# slice's own brief names this shape explicitly).
const scanFixturePath = currentSourcePath().parentDir() / "s8ak_scan_fixture.nim"
const scanFixtureNames = extractTopLevelNames(scanFixturePath)
const scanFixtureMacroNames = extractTopLevelMacroNames(scanFixturePath)

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

suite "S8ah: field-graph depth (unbounded, visited-set-guarded)":

  test "RED (observed against the OLD depth-3 code, see the file header): " &
       "a hazard 5 field-hops deep is now caught":
    check fixtureParamHits.anyIt(it.contains("fxParamAliasDeepShape") and it.contains("param xs"))

  test "GREEN: a hazard reachable through a self-referential type is caught, and the walk terminates":
    # Compiling this file at all (see `FxCyclicInner.self: FxCyclicInner`
    # above) is part of the termination proof -- a visited-set-less
    # unbounded walk would not return.
    check fixtureParamHits.anyIt(it.contains("fxParamAliasCyclicShape") and it.contains("param xs"))

suite "S8ah: macro-by-macro reachability of the 37 generics":

  test "RED (mechanism): a macro's direct, unquoted call into a generic is flagged reachable":
    check fixtureReachHits.anyIt(it.contains("s8ahFxDirectGenericCall") and
                                  it.contains("-> " & thisFile & ":fxGenericAliasShape"))

  test "GREEN (mechanism): the SAME generic, called only inside quote do:, is NOT flagged reachable":
    check not fixtureReachHits.anyIt(it.contains("s8ahFxQuotedGenericCall"))

  test "GREEN: every generic the real 16-file scope finds VM-reachable has a forced-instantiation audit":
    # RFC-0005 S8ak: compared by `genericKeyPrefix` (name+file), never the
    # full `file:name@line` key -- S8ad's `dsl_parser.nim` edit (7269 ->
    # 7270) proved the full-key comparison breaks on ANY edit that shifts a
    # registered generic's declaration, independent of whether the
    # generic's own reachability or forced-ness actually changed.
    var reachableGenerics: seq[string]
    for h in realScopeReachHits:
      let genericKey = h.split(" -> ")[^1]
      if genericKey notin reachableGenerics: reachableGenerics.add genericKey
    let globallyForcedPrefixes = globallyForcedGenerics.mapIt(genericKeyPrefix(it))
    var unforced: seq[string]
    for g in reachableGenerics:
      if genericKeyPrefix(g) notin realScopeForcedGenerics and
         genericKeyPrefix(g) notin globallyForcedPrefixes: unforced.add g
    check unforced.len == 0
    if unforced.len > 0: echo "UNFORCED VM-REACHABLE GENERIC:\n" & unforced.join("\n")
    # And the converse: an entry on the forced list that the real scope no
    # longer finds reachable is stale (the same staleness check the
    # allowlist above already gets).
    let reachablePrefixes = reachableGenerics.mapIt(genericKeyPrefix(it))
    var stale: seq[string]
    for g in realScopeForcedGenerics:
      if g notin reachablePrefixes: stale.add g
    check stale.len == 0
    if stale.len > 0: echo "STALE FORCED-GENERIC ENTRY:\n" & stale.join("\n")

  test "GREEN: the real scope has 22 unique macro names, not the fence's stale 17":
    # See `realScopeMacroNames`'s own doc comment for the reconciliation.
    check realScopeMacroNames.len == 22

  test "GREEN: exactly 1 of the 37 registered generics is VM-reachable from any macro in scope" &
       " (the other 36 are proven unreachable by the SAME mechanical walk, not left unclassified)":
    var reachableGenerics: seq[string]
    for h in realScopeReachHits:
      let genericKey = h.split(" -> ")[^1]
      if genericKey notin reachableGenerics: reachableGenerics.add genericKey
    # RFC-0005 S8ak: compared by identity (name+file), not the full key --
    # see `genericKeyPrefix`'s own doc. The line is still reported in
    # `reachableGenerics` itself (useful diagnostic detail); it is just
    # never load-bearing for THIS assertion.
    check reachableGenerics.mapIt(genericKeyPrefix(it)) == @["dsl_parser.nim:traceOneCallBoundary"]

suite "S8al: the force-and-audit half of the guard, exercised against a fixture generic " &
      "(not just traceOneCallBoundary)":

  test "GREEN: the forced generic's own let-aliasing hazard is reported":
    check fixtureLetHits.anyIt(it.contains("s8alFxForcedHazardGeneric[instantiated]") and
                                it.contains("let v") and it.contains("seq[int]"))

  test "GREEN (mechanism): a VM-reachable fixture generic WITH a forced-instantiation audit " &
       "passes the SAME completeness comparison the real scope's own test uses":
    var reachable: seq[string]
    for h in fixtureReachHits:
      if h.contains("s8alFxDirectForcedGenericCall"): reachable.add h.split(" -> ")[^1]
    check reachable.len == 1
    let forcedPrefixes = s8alFixtureForcedGenerics.mapIt(genericKeyPrefix(it))
    var unforced: seq[string]
    for g in reachable:
      if genericKeyPrefix(g) notin forcedPrefixes: unforced.add g
    check unforced.len == 0

  test "RED (mechanism): the SAME completeness comparison fails CLOSED -- a VM-reachable " &
       "generic with no forced-instantiation audit is reported unforced, not silently accepted":
    # `s8alFxUnforcedHazardGeneric` is reachable (its own fixture macro
    # calls it directly) but deliberately never forced anywhere in this
    # file -- see its own doc above. Before this slice, the "force and
    # audit" mechanism's completeness comparison had only ever been run
    # against `traceOneCallBoundary`, which is ALWAYS forced -- this is the
    # first time the comparison itself is exercised against a row that
    # should come out unforced, proving a regression in the comparison
    # (e.g. comparing the wrong key, or reading the wrong list) would show
    # up here even though the real 16-file scope's own single row could
    # never catch it.
    var reachable: seq[string]
    for h in fixtureReachHits:
      if h.contains("s8alFxDirectUnforcedGenericCall"): reachable.add h.split(" -> ")[^1]
    check reachable.len == 1
    let forcedPrefixes = s8alFixtureForcedGenerics.mapIt(genericKeyPrefix(it))
    var unforced: seq[string]
    for g in reachable:
      if genericKeyPrefix(g) notin forcedPrefixes: unforced.add g
    check unforced.len == 1
    if unforced.len == 1:
      echo "CORRECTLY UNFORCED (expected, proves fail-closed): ", unforced[0]

suite "S8ak: a zero-required-argument macro is resolved by symbol, not auto-invoked":

  test "a genuinely zero-arg macro's direct call into a registered generic" &
       " (just, strategy.nim) is flagged reachable":
    # Pre-fix: `vmGuardAuditNames` generated `vmGuardAuditRoutine(ident(nm),
    # fileTag)` and let the compiler re-resolve `ident(nm)` as a fresh
    # `typed` argument -- Nim auto-invokes a zero-required-arg macro
    # referenced bare there, so `s8akFxZeroArgDirectGenericCall` was
    # silently executed (producing `discard just(5); newLit(0)`'s `0`, an
    # `nnkIntLit`) instead of ever having its body walked, and this check
    # failed (`fixtureReachHits` held no entry for it at all).
    # RFC-0005 S8ak: matched on "-> strategy.nim:just@", not the exact
    # line -- see `genericKeyPrefix`'s own doc for why a hardcoded line in
    # a check like this is exactly the trap that broke `traceOneCallBoundary`.
    check fixtureReachHits.anyIt(it.contains("s8akFxZeroArgDirectGenericCall") and
                                  it.contains("-> strategy.nim:just@"))

  test "GREEN: no getImpl/audit-machinery error from resolving a zero-arg macro's name":
    check realScopeErrs.len == 0

suite "S8ak: extractTopLevelNames/extractTopLevelMacroNames enumerate from a real parse" &
      " of the module (parseStmt), not a column-0 text scan":

  test "a routine whose keyword and name sit on different physical lines is still found":
    # Pre-fix: the old scan required `line.startsWith("proc ")` on ONE
    # line; a line containing only `"proc"` (the name is on the next line)
    # fails that check outright, so `s8akSplitKeywordOp` never appeared in
    # `extractTopLevelNames`'s result at all.
    check "s8akSplitKeywordOp" in scanFixtureNames

  test "GREEN: an ordinary single-line backtick operator name is still found (no regression)":
    check "s8akOrdinaryBacktickOp" in scanFixtureNames

  test "GREEN: a signature whose parameter list spans multiple lines is still found":
    check "s8akMultiLineParams" in scanFixtureNames

  test "extractTopLevelMacroNames finds a macro whose keyword and name sit" &
       " on different physical lines":
    check "s8akSplitKeywordMacro" in scanFixtureMacroNames

  test "GREEN: extractTopLevelNames also finds the split-keyword macro" &
       " (it audits every routine kind, not only procs)":
    check "s8akSplitKeywordMacro" in scanFixtureNames

suite "S8ak: a reachable generic's hit key tracks the live declaration, never the " &
      "registry's hand-typed line":

  test "RED/GREEN (mechanism): a wrong/stale line in the generic's OWN spec entry must " &
       "not desync the reachable-generic key from the forced-instantiation key":
    # `fixtureGenericSpecs` (above) registers `fxGenericAliasShape` with
    # `line: 0` -- deliberately wrong, since the real declaration is nowhere
    # near line 0. This is exactly the shape of S8ad's real regression: an
    # edit elsewhere in the file left the registry's OWN recorded line
    # stale relative to where the generic actually lives.
    #
    # Before this fix, `vmGuardWalkForGenericCallsAux` built the reachable
    # hit's key from `spec.line` (here, the wrong `0`), while
    # `vmGuardAuditInstantiation`'s forced key (the `vmGuardAuditInstantiation`
    # call just above `fixtureForcedGenerics`'s own snapshot) always derived
    # its line LIVE from `getImpl()` (`fxGenericAliasShape`'s real
    # declaration line) -- so `"...fxGenericAliasShape@0"` never matched
    # `"...fxGenericAliasShape@<real line>"`, and a generic that IS already
    # forced in this very file would still show up "unforced" by the exact
    # same completeness check `realScopeReachHits`/`realScopeForcedGenerics`
    # run on the real scope. After the fix, the reachable-generic key is
    # derived from the MATCHED CALLEE's own live `getImpl()` too (see
    # `vmGuardWalkForGenericCallsAux`'s own doc), so `spec.line` being wrong
    # -- by one, by a thousand, in either direction -- can never matter.
    var reach: seq[string]
    for h in fixtureReachHits:
      if h.contains("s8ahFxDirectGenericCall"): reach.add h.split(" -> ")[^1]
    check reach.len == 1
    check reach[0] in fixtureForcedGenerics
    if reach.len == 1 and reach[0] notin fixtureForcedGenerics:
      echo "REACHABLE-BUT-UNFORCED (line-keying desync): ", reach[0],
           "\nFORCED KEYS: ", fixtureForcedGenerics.join(", ")
