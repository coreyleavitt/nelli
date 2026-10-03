## RFC-0005 S8e -- scope-keyed names for the DSL parser.
##
## The IR names every variable by a STRING, and the walker's env, the
## closure capture lists, the `var`-param write-back map and every
## name-keyed pre-pass collector key on that string. The parser used to take
## the string straight from the symbol's printed name (`strVal`). Two
## distinct Nim symbols with one spelling -- an inner `var k` that shadows an
## outer `k` in a nested block, a loop body, an `if` arm, a for-variable, a
## closure body, an inlined iterator body -- therefore got ONE env slot, and
## a write through either name was seen through both. That is a silent
## substitution (§2.2's class): a false `sxSat` or `sxUnsat` with an empty
## `errors`.
##
## The fix keys a name by its SYMBOL. Before a routine is parsed, its
## declarations are CLAIMED in source order within one naming scope (the env
## the walker gives that routine: the entry proc or a callee, with its
## lambdas and inlined iterator bodies, which share or copy from that env).
## The first symbol to claim a spelling keeps it -- so an entry proc's
## params, which claim first, keep their names in the witness -- and every
## later, DIFFERENT symbol with the same spelling is given a fresh name
## (`k__scN`; Nim identifiers cannot contain `__`, so it can collide with no
## user name, and `__sym_`-style parser temporaries do not use the suffix).
##
## Every conversion from a symbol to an IR name goes through `strVal`
## below, which this module exports in place of `std/macros.strVal`
## (`dsl_parser` imports `std/macros except strVal`). So the rename holds at
## every site by construction, with no per-site audit to go stale: the
## declaration, every read and write, the closure capture scan, the
## pre-pass collectors and the iterator param substitution all see one
## name per symbol. A symbol that is not renamed (every non-local symbol,
## and every local whose spelling is unique in its scope) reads exactly as
## before.
##
## State is compile-time and scoped like `ProcScopedCollectors`: a callee's
## parse runs in its own naming scope (`enterNameScope`/`leaveNameScope`),
## which inherits the caller's renames (a nested proc may name a caller
## local) and discards its own on exit.

import std/macros
import std/tables
import std/sets
from ./types import globalEnvPrefix

type
  NameScope* = object
    ## One naming scope's state, saved and restored around a nested scope.
    renames: Table[string, seq[tuple[sym: NimNode, name: string]]]
      ## spelling -> the symbols of that spelling that were renamed, with
      ## their scoped names. Consulted by `strVal`; empty for any routine
      ## with no shadowing, so the lookup costs one `len` check.
    claimed: Table[string, seq[NimNode]]
      ## spelling -> symbols already claimed in this scope (makes a claim
      ## idempotent: a lambda claimed with its enclosing routine, then again
      ## when `parseRoutineToLambda` reaches it, keeps its first name).
    taken: HashSet[string]
      ## every IR name in use in this scope

var nameScope {.compileTime.}: NameScope
var nameCounter {.compileTime.}: int
var byRefCounter {.compileTime.}: int
var moduleGlobalSyms {.compileTime.}: Table[string, NimNode]
  ## RFC-0005 S8bw. The symbol of every module-level global `strVal` named,
  ## by its `__gl:` name, so the emitter can give a read its declared type
  ## (`globalSymOf`).

const byRefMarkColumn = -32123
  ## RFC-0005 S8ba. The column a by-reference base carries (`markByRef`):
  ## no source position has a negative column.

const claimableSymKinds = {nskVar, nskLet, nskForVar, nskParam, nskTemp}
  ## The runtime value bindings an env slot holds. A local `const` is folded
  ## by the compiler at every use, and `result` is never declared by an
  ## `IdentDefs` (each routine's `result` is its own frame's slot).

proc isModuleGlobal*(n: NimNode): bool =
  ## RFC-0005 S8an. True when `n` is the symbol of a module-level `var` or
  ## `let` (its owner is the module itself).
  if n.kind != nnkSym or symKind(n) notin {nskVar, nskLet}: return false
  let o = owner(n)
  o.kind == nnkSym and symKind(o) == nskModule

proc byRefName*(n: NimNode): string =
  ## RFC-0005 S8ba. The IR name of a by-reference base (`markByRef`), or ""
  ## when `n` is not one. RFC-0005 S8bd: a mark is a symbol, or a node with
  ## no children (`markByRef` of an element or a call result).
  if n.kind != nnkSym and n.len != 0: return ""
  let li = n.lineInfoObj
  if li.column != byRefMarkColumn or li.line <= 0: return ""
  "__byref_" & $li.line

proc markByRef*(base: NimNode): NimNode =
  ## RFC-0005 S8ba. A copy of the symbol `base` (it keeps its symbol and
  ## type) that names a fresh by-reference parameter: `strVal` reads it as
  ## `__byref_<N>`, so a callee specialised to a heap lvalue (`p.x` for its
  ## `var` formal) reads and writes that cell through the ref the caller
  ## evaluated at the call. nil when the counter is spent (the line field
  ## holds the number).
  ## RFC-0005 S8bd: a base that is not a symbol (`a[i]`, `getBox()`) is
  ## marked as a copy of its own node without its children: it keeps the
  ## node's type, and names nothing of the caller's.
  if byRefCounter >= 65000: return nil
  inc byRefCounter
  result = copyNimNode(base)
  result.setLineInfo(base.lineInfoObj.filename, byRefCounter, byRefMarkColumn)

proc strVal*(n: NimNode): string =
  ## `std/macros.strVal`, except that a symbol renamed by a claim reads as
  ## its scoped name (RFC-0005 S8e), and a module-level variable reads as
  ## `__gl:<module>.<name>` (RFC-0005 S8an). A by-reference base reads as
  ## its parameter's name (RFC-0005 S8ba, `markByRef`).
  let br = byRefName(n)
  if br.len > 0: return br
  result = macros.strVal(n)
  if isModuleGlobal(n):
    result = globalEnvPrefix & macros.strVal(owner(n)) & "." & result
    moduleGlobalSyms[result] = n
    return
  if n.kind == nnkSym and nameScope.renames.len > 0:
    let cands = nameScope.renames.getOrDefault(result)
    for c in cands:
      if c.sym == n:
        return c.name

proc globalSymOf*(name: string): NimNode =
  ## RFC-0005 S8bw. The symbol of the module-level global `name` (an
  ## `__gl:` name `strVal` produced), or nil.
  moduleGlobalSyms.getOrDefault(name, nil)

proc resetNameScopes*() =
  ## Start a top-level parse: no renames, no claims, counter at zero (so a
  ## re-parse of the same proc yields the same names, and the same cache
  ## key).
  nameScope = NameScope()
  nameCounter = 0
  byRefCounter = 0

proc enterNameScope*(): NameScope =
  ## Open a nested naming scope (a callee's own env). Keeps the enclosing
  ## renames visible; clears claims and taken names. Returns the state to
  ## hand back to `leaveNameScope`.
  result = nameScope
  nameScope.claimed = initTable[string, seq[NimNode]]()
  nameScope.taken = initHashSet[string]()

proc leaveNameScope*(saved: NameScope) =
  nameScope = saved

proc reserveScopedNames*(names: seq[string]) =
  ## RFC-0005 S8an. Mark `names` as in use in the current scope before its
  ## routine is claimed: a routine declared inside another shares its env
  ## with the enclosing variables it captures (`ProcSig.captures`), so a
  ## local or parameter of its own with the same spelling must get a fresh
  ## name.
  for nm in names: nameScope.taken.incl nm

proc claimDecl(n: NimNode) =
  var s = n
  if s.kind == nnkPragmaExpr and s.len > 0: s = s[0]
  if s.kind == nnkPostfix and s.len > 1: s = s[1]
  if s.kind == nnkVarTuple:
    for i in 0 ..< s.len - 2: claimDecl(s[i])
    return
  if s.kind != nnkSym or symKind(s) notin claimableSymKinds: return
  let raw = macros.strVal(s)
  for c in nameScope.claimed.getOrDefault(raw):
    if c == s: return
  nameScope.claimed.mgetOrPut(raw, @[]).add s
  if raw notin nameScope.taken:
    nameScope.taken.incl raw
    return
  inc nameCounter
  let fresh = raw & "__sc" & $nameCounter
  nameScope.renames.mgetOrPut(raw, @[]).add (sym: s, name: fresh)
  nameScope.taken.incl fresh

proc claimRoutine*(routine: NimNode)

proc claimScopedNames*(n: NimNode) =
  ## Claim, in source (pre-)order, every declaration in `n` that shares the
  ## current scope's env: `let`/`var` names (incl. tuple unpacking),
  ## for-variables, and the params and bodies of nested lambdas. A nested
  ## NAMED routine is its own scope (claimed when it is parsed), and a type
  ## section declares no env slot.
  if n == nil: return
  case n.kind
  of nnkTypeSection, nnkTemplateDef, nnkMacroDef, nnkProcDef, nnkFuncDef,
     nnkIteratorDef, nnkConverterDef, nnkMethodDef:
    discard
  of nnkIdentDefs, nnkVarTuple, nnkConstDef:
    for i in 0 ..< n.len - 2: claimDecl(n[i])
    claimScopedNames(n[n.len - 1])
  of nnkForStmt:
    for i in 0 ..< n.len - 2: claimDecl(n[i])
    claimScopedNames(n[n.len - 2])
    claimScopedNames(n[n.len - 1])
  of nnkLambda, nnkDo:
    claimRoutine(n)
  else:
    for c in n: claimScopedNames(c)

proc claimRoutine*(routine: NimNode) =
  ## Claim a routine's formal params (first, so they keep their spelling)
  ## and then its body, into the CURRENT naming scope.
  if routine == nil or routine.len < 7: return
  let formal = routine[3]
  if formal.kind == nnkFormalParams:
    for i in 1 ..< formal.len:
      let id = formal[i]
      if id.kind == nnkIdentDefs:
        for j in 0 ..< id.len - 2: claimDecl(id[j])
  claimScopedNames(body(routine))

proc scopedRepr*(n: NimNode): string =
  ## A structural key for an expression that spells each symbol by its
  ## scoped name: `n.repr` would print an inner shadowing `k` and the outer
  ## `k` alike, so a key built on it conflates them (RFC-0005 S8e -- the
  ## `caseNarrow` scrutinee key).
  if n == nil: return "nil"
  if n.kind == nnkSym: return "sym:" & strVal(n)
  # Compiler-inserted wrappers `repr` prints through: keep the key's
  # equality where the old `repr` key had it.
  if n.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv,
                nnkHiddenSubConv, nnkHiddenCallConv} and n.len > 0:
    return scopedRepr(n[n.len - 1])
  if n.kind == nnkCheckedFieldExpr and n.len > 0:
    return scopedRepr(n[0])
  if n.len == 0: return $n.kind & ":" & n.repr
  result = $n.kind & "("
  for i, c in n:
    if i > 0: result.add ","
    result.add scopedRepr(c)
  result.add ")"
