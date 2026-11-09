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
##
## `noalias` (C `restrict`) is declined too: it asserts the formals do not
## overlap, which is a precondition on the caller (undefined behaviour when
## false), so it belongs to the definedness axis's operand classes (K10b).
##
## Absent is a decline: a name with no row answers `feUnadmitted` (at the
## local place, `feLocalPragma`, the kind W1-b shipped). Nim has no enum of
## pragmas, so the lists are hand-written; `tsymex_0016_k3c_pragmaaxis` scans
## the toolchain's `lib/` and fails on a pragma it declares that has no row.
## Names are style-insensitive (`noSideEffect` is `nosideeffect`), as in Nim.
import std/[macros, options, strutils]
import ./admission
import ./errorkind

type
  PragmaPlace* = enum
    ppLocal, ppRoutine, ppParam, ppType
  PragmaSite* = enum
    psLocalDecl       ## `var` / `let` section of a routine body
    psRoutineDecl     ## a callee's pragma list and its formals' (registration)
    psTypeDecl        ## a type reaching a local, a formal or a result
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

func siteOf(p: PragmaPlace): PragmaSite =
  case p
  of ppLocal: psLocalDecl
  of ppRoutine, ppParam: psRoutineDecl
  of ppType: psTypeDecl

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
    ["magic", "borrow", "importCompilerProc", "importc", "importcpp", "importjs", "exportc",
     "header", "dynlib", "nodecl", "extern", "error", "thread", "noinit",
     "constructor", "varargs", "noreturn", "compileTime", "asmNoStackFrame",
     "nodestroy", "codegenDecl", "emit"],
    "decided where the callee is resolved: a magic, a foreign body, an " &
    "opaque call, a thread entry")
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

proc pragmaName*(p: NimNode): string =
  ## The name of one pragma entry (`cursor`, `align: 8` -> `align`,
  ## `raises: [IOError]` -> `raises`), "?" for a shape with no name.
  case p.kind
  of nnkIdent, nnkSym: p.strVal
  of nnkExprColonExpr, nnkCall, nnkCommand, nnkOpenSymChoice,
     nnkClosedSymChoice:
    if p.len > 0: pragmaName(p[0]) else: "?"
  else: "?"
