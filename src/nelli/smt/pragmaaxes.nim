## RFC-0016 K3c (section 8.1) -- the pragma axis.
##
## One `AxisTable` over the ADM-1 machinery, keyed `<place>/<name>` on the
## `pragma:` scope, three lists in four places:
##
## * `local/<name>`: a pragma on a local `var` / `let`. The list W1-b wrote as
##   `localPragmaAllowlist` (`noinit`, `global`, `inject`, `gensym`, `used`);
##   every other name declines `feLocalPragma` (`cursor` shares memory the
##   copy model does not, PRC-39; `align`, `volatile`, `codegenDecl` change
##   the generated code).
## * `routine/<name>` and `param/<name>`: a pragma on a routine or on one of
##   its formals, read where a callee is registered (`ensureProcRegistered`).
## * `type/<name>`: a pragma on a type declaration, read wherever a value of
##   the type enters the walk (a local, a formal, a result) and through its
##   components. `union` overlays fields, `packed` and `size` / `align` fix
##   a layout the object model does not have, `byref` / `bycopy` fix how a
##   value is passed (and so whether a callee's write shows in the caller):
##   `union`, `packed`, `byref` and `bycopy` decline until modelled.
## * `field/<name>`: a pragma on one field of an object (W3-z P4), read where
##   the type is walked (`typePragmaHit`). `bitsize` and `align` change what a
##   store keeps, so they decline; a name with no row declines too (a field
##   pragma is not read by macros the way a type's is).
##
## `noalias` (C `restrict`) is declined too: it asserts the formals do not
## overlap, which is a precondition on the caller (undefined behaviour when
## false), so it belongs to the definedness axis's operand classes (K10b).
##
## Absent is a decline at the local, routine and parameter places: a name with
## no row answers `feUnadmitted` (at the local place, `feLocalPragma`, the kind
## W1-b shipped). At the type place the walker acts on the four declined rows
## only: types carry pragmas for macros and templates freely (`RootObj` has
## `compilerproc`), and none changes a value but those four. Nim has no enum of
## pragmas, so the lists are hand-written; `tsymex_0016_k3c_pragmaaxis` scans
## the toolchain's `lib/` and fails on a pragma it declares that has no row.
## Names are style-insensitive (`noSideEffect` is `nosideeffect`), as in Nim.
import std/[macros, options, strutils]
import ./admission
import ./errorkind

type
  PragmaPlace* = enum
    ppLocal, ppRoutine, ppParam, ppType, ppField
  PragmaSite* = enum
    psLocalDecl       ## `var` / `let` section of a routine body
    psRoutineDecl     ## a callee's pragma list and its formals' (registration)
    psTypeDecl        ## a type reaching a local, a formal or a result
    psFieldDecl       ## a field of an object reached through its type
  PragmaModel* = enum
    pmInert           ## no effect on any value the walk computes
    pmRead            ## the walker reads it at a site of its own
  PragmaKey = tuple[key: string, row: Row[PragmaSite, PragmaModel]]

func placeKey*(p: PragmaPlace): string =
  case p
  of ppLocal: "local"
  of ppRoutine: "routine"
  of ppParam: "param"
  of ppType: "type"
  of ppField: "field"

func siteOf(p: PragmaPlace): PragmaSite =
  case p
  of ppLocal: psLocalDecl
  of ppRoutine, ppParam: psRoutineDecl
  of ppType: psTypeDecl
  of ppField: psFieldDecl

func inert(p: PragmaPlace; names: openArray[string]; why: string):
    seq[PragmaKey] =
  for n in names:
    result.add (placeKey(p) & "/" & n,
                modelled[PragmaSite, PragmaModel](pmInert, {siteOf(p)}, why))

func read(p: PragmaPlace; names: openArray[string]; why: string):
    seq[PragmaKey] =
  for n in names:
    result.add (placeKey(p) & "/" & n,
                modelled[PragmaSite, PragmaModel](pmRead, {siteOf(p)}, why))

func declined(p: PragmaPlace; names: openArray[string]; kind: SymexErrorKind;
              why: string): seq[PragmaKey] =
  for n in names:
    result.add (placeKey(p) & "/" & n,
                refused[PragmaSite, PragmaModel](some(kind), why))

func neverField(names: openArray[string]; why: string): seq[PragmaKey] =
  ## A field pragma the toolchain refuses: a `never` cell (`nrPlatform`).
  for n in names:
    result.add (placeKey(ppField) & "/" & n,
                refused[PragmaSite, PragmaModel](some(feUnsupportedOp), why,
                                                 iNever, nrPlatform))

func pragmaRows(): seq[PragmaKey] =
  # --- the local list (W1-b) ------------------------------------------------
  result.add read(ppLocal, ["noinit"],
    "modelled: an unwritten read taints (`noinitPlain`)")
  result.add read(ppLocal, ["global"],
    "modelled: a module-level variable (`isModuleGlobal`)")
  result.add inert(ppLocal, ["inject", "gensym"],
    "template hygiene only: renames the symbol at expansion, no run-time " &
    "effect (`std/re`'s `=~`)")
  result.add inert(ppLocal, ["used"],
    "suppresses the unused-variable hint; no code is changed")
  result.add declined(ppLocal, ["cursor"], feLocalPragma,
    "a non-owning alias of its source's storage; the copy model reads a " &
    "stale value after a write through the source (PRC-39 models it)")
  result.add declined(ppLocal,
    ["align", "codegenDecl", "volatile", "register", "compileTime",
     "threadvar", "guard", "exportc", "importc", "extern", "nodecl",
     "header", "dynlib", "deprecated", "bitsize", "size", "byaddr",
     "redefine"],
    feLocalPragma,
    "changes the generated code or the storage of the local, which the " &
    "model does not represent")
  # --- the routine list -------------------------------------------------------
  result.add inert(ppRoutine,
    ["inline", "noinline", "noSideEffect", "sideEffect", "gcsafe", "benign",
     "raises", "tags", "forbids", "locks", "effectsOf", "discardable",
     "deprecated", "used", "nimcall", "cdecl", "stdcall", "fastcall",
     "safecall", "syscall", "noconv", "closure", "procvar", "compilerproc",
     "compilerRtl", "rtl", "rtlFunc", "inl", "core", "stackTrace",
     "lineTrace", "enforceNoRaises", "systemRaisesDefect", "nonReloadable",
     "noWeirdTarget", "noNimJs", "nimhcr", "hcrInline", "multisync", "since",
     "requires", "ensures", "base", "operator", "profiler", "debugger",
     "dirty", "callsite", "async", "parseRaises", "parseFormatRaises",
     "auditDelete", "executeOnReload", "quirky", "evalonce", "myShallow",
     "epollPacked", "outParamsAt", "importIconv", "lcrypto", "boehmGC",
     "gcMark", "nosinks", "errorNoReturn", "fatal", "nimbaseH", "sendable"],
    "no effect on the value a call computes, or a name only a macro, a " &
    "template or the code generator reads")
  result.add read(ppRoutine,
    ["checks", "assertions", "floatChecks", "nanChecks", "infChecks",
     "fieldChecks", "overflowChecks", "rangeChecks", "boundChecks",
     "objChecks", "nilChecks"],
    "a check option: `check_options` reads it for the routine's region")
  result.add inert(ppRoutine,
    ["optimization", "warnings", "hints", "exportcpp", "importObjC",
     "exportJs", "tlsEmulation"],
    "a compiler diagnostic or code-generation switch with no effect on a value")
  result.add read(ppRoutine,
    ["magic", "borrow", "importc", "importcpp", "importjs", "dynlib"],
    "decided where the callee is resolved: a magic (`implMagic`), a borrow " &
    "(`hasBorrowPragma`), a foreign body routed to the opaque-call arm " &
    "(`isBodilessForeign`)")
  result.add read(ppRoutine, ["noreturn"],
    "a call to it ends the path (`isNoReturnRoutine`)")
  result.add read(ppRoutine, ["thread"],
    "a thread's entry (`routeBodyOf`); a direct call runs its body as written")
  result.add read(ppRoutine, ["noinit"],
    "`result` starts unwritten, as a `{.noinit.}` local does: a read before " &
    "a write is indeterminate (`noinitResultPrologue`); a managed result " &
    "declines")
  result.add inert(ppRoutine, ["exportc", "extern", "header", "nodecl"],
    "names the routine's C symbol, adds an `#include` or leaves out its " &
    "prototype: the Nim body runs as written (a foreign body is decided by " &
    "`importc`)")
  result.add inert(ppRoutine, ["error", "compileTime"],
    "a call to it in run-time code does not compile, so no walked program " &
    "reaches it")
  result.add declined(ppRoutine, ["nodestroy"], feUnsupportedOp,
    "no destructor or hook is injected in the body: an assignment is a " &
    "bitwise copy and nothing is destroyed, which the copy model (hooks " &
    "run) does not represent")
  result.add declined(ppRoutine,
    ["codegenDecl", "constructor", "asmNoStackFrame", "emit", "varargs"],
    feUnsupportedOp,
    "changes the routine's generated C/C++ (its declaration, a C++ " &
    "constructor, a frameless assembler body, emitted code, C varargs), " &
    "which the walk does not read")
  result.add declined(ppRoutine, ["importCompilerProc"], feUnsupportedOp,
    "a body supplied by the compiler's runtime, not by the declaration: an " &
    "empty body walked would answer the zero default")
  # --- the parameter list -------------------------------------------------------
  result.add inert(ppParam, ["inject", "used"],
    "template hygiene or a hint; no run-time effect")
  result.add declined(ppParam, ["byref", "bycopy"], feUnsupportedOp,
    "fixes how the formal is passed: a callee's write through a `byref` " &
    "formal shows in the caller, and the call model passes by copy")
  result.add declined(ppParam, ["noalias"], feUnsupportedOp,
    "C `restrict`: an assertion that the formals do not overlap, undefined " &
    "when false; an `OperandClass` of the definedness axis (K10b)")
  # --- the type list -----------------------------------------------------------
  result.add inert(ppType,
    ["pure", "final", "inheritable", "acyclic", "shallow", "requiresInit",
     "sendable", "deprecated", "incompleteStruct", "completeStruct", "gcsafe",
     "noSideEffect", "raises", "tags", "forbids", "locks", "effectsOf",
     "nimcall", "cdecl", "stdcall", "fastcall", "safecall", "syscall",
     "noconv", "closure", "nosinks", "benign", "inline", "myShallow"],
    "no effect on the values of the type: ownership, inheritance or " &
    "effect annotations")
  result.add read(ppType,
    ["importc", "importcpp", "importjs", "exportc", "header", "nodecl",
     "size", "align", "borrow", "dynlib", "extern", "nimbaseH"],
    "names a foreign type or fixes the size of a scalar; read where the " &
    "type is classified (`classifyType`, `getSize`), not here")
  result.add declined(ppType, ["union", "packed", "byref", "bycopy"],
    feUnsupportedOp,
    "changes the layout or the passing of the type, which the object model " &
    "(independent fields, passed by copy) does not represent")

  # --- the field list (W3-z P4) ---------------------------------------------------
  result.add inert(ppField, ["deprecated", "requiresInit", "used"],
    "a diagnostic or an initialisation rule: no effect on the field's value")
  result.add inert(ppField, ["cursor"],
    "a non-owning field: the value read is the same while its owner lives")
  result.add inert(ppField, ["exportc"],
    "names the field's C member: the value stored and read is the same " &
    "(`system.Exception.msg` carries it, so every exception object does; " &
    "`tsymex_0016_w1a_exn_typeid`, `tsymex_0016_p4_fieldpragma`)")
  result.add declined(ppField,
    ["bitsize", "align", "importc", "extern", "guard"],
    feUnsupportedOp,
    "fixes the width, alignment or storage of the field (`bitsize: 3` wraps " &
    "a store to 3 bits), which the object model (one full-width slot per " &
    "field) does not represent")
  result.add neverField(
    ["size", "volatile", "codegenDecl", "header", "nodecl", "dynlib",
     "atomic"],
    "Nim rejects it on a field (`not compiles`, `tsymex_0016_p4_fieldpragma`), " &
    "so no program carries it; the row stays a decline if a toolchain accepts it")

func buildTable(): AxisTable[PragmaSite, PragmaModel] =
  var rows: seq[PragmaKey]
  var seen: seq[string]
  for r in pragmaRows():
    let n = nimIdentNormalize(r.key)
    doAssert n notin seen, "pragma row twice (style-insensitive): " & r.key
    seen.add n
    rows.add r
  axisTable[PragmaSite, PragmaModel](axPragma, rows)

const pragmaAxis* = buildTable()

func canonicalKey(place: PragmaPlace; name: string): string =
  ## The row key spelled as the table spells it, or the name as written.
  let want = nimIdentNormalize(placeKey(place) & "/" & name)
  for k in pragmaAxis.keys:
    if nimIdentNormalize(k) == want:
      return k
  placeKey(place) & "/" & name

func admitPragma*(place: PragmaPlace; name: string; site: PragmaSite):
    Admit[PragmaModel] =
  ## Whether the pragma `name` is admitted in `place`, read at `site`.
  pragmaAxis.admit(canonicalKey(place, name), site,
                   absent = some(if place == ppLocal: feLocalPragma
                                 else: feUnadmitted))

func admittedNames*(place: PragmaPlace): seq[string] =
  ## The names `place` admits, in table order (for a decline's message).
  let head = placeKey(place) & "/"
  for k in pragmaAxis.keys:
    if k.startsWith(head) and
       pragmaAxis.admit(k, siteOf(place)).admitted:
      result.add k[head.len .. ^1]

const unnamedPragma* = "?"
  ## What `pragmaName` answers for a pragma entry of a shape it cannot name.
  ## It has no row, so every list but the type list declines it (absent is a
  ## decline); the type list ignores a name with no row, so its readers test
  ## for this name and decline (RFC-0016 K2F-2).

proc pragmaName*(p: NimNode): string =
  ## The name of one pragma entry (`cursor`, `align: 8` -> `align`,
  ## `align(8)` -> `align`, `raises: [IOError]` -> `raises`, `m.cursor` ->
  ## `cursor`), `unnamedPragma` ("?") for a shape with no name: never a name
  ## that could match a row.
  case p.kind
  of nnkIdent, nnkSym: p.strVal
  of nnkExprColonExpr, nnkCall, nnkCommand, nnkCallStrLit, nnkBracketExpr,
     nnkOpenSymChoice, nnkClosedSymChoice:
    if p.len > 0: pragmaName(p[0]) else: unnamedPragma
  of nnkDotExpr:
    if p.len == 2: pragmaName(p[1]) else: unnamedPragma
  else: unnamedPragma
