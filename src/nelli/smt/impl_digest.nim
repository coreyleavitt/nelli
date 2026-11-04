## RFC-0005 code review, round 1 (R1-09). The part of the verdict cache key the
## parsed program does not carry: the source of the routines the SUT calls.
##
## A cached `rsConfirmed`, `witnessUnsafe` or `:raised` sentinel is a fact about
## the real `fn`, which a replay ran, and so about every routine `fn` reaches
## natively. The IR holds only what the walker inlined: a `{.symexOpaque.}` or
## `{.symexTransparent.}` callee, a declined call and a bodiless foreign routine
## appear in it as a name. Edit such a body and the program's key did not move,
## so the cache served the old run's trusted result.
##
## `implDigest(fn)` is a digest of every user routine `fn` names, transitively
## through the routines they name: each one's symbol kind, name, typed
## definition (parameters, pragmas and body, as a structural serialisation that
## leaves out line info and gensym numbering), and the check options it was
## compiled under (`check_options.routineChecks`), which the typed AST does not
## show. `fn`'s own body is the IR and is not hashed again, so two SUTs with the
## same body keep one key whatever their names (`tsymex_phase15_C1_*`).
##
## Not followed, by design:
## - a routine declared in the compiler's `lib/` tree. The walker models what it
##   inlines from there, and the key's `nim=` segment moves with the toolchain;
## - nelli's own runtime (the markers), which `symexWalkerVersion` keys.
##
## Not visible, and so not keyed (`docs/migration/0.9.0.md` names the same
## limits for the walk):
## - a bodiless foreign routine's external body. Its name, signature and
##   pragmas (`importc`, `dynlib`, the header) are keyed; the C, C++ or
##   library code behind it is not;
## - the overrides of a method `fn` calls, which no macro can list: those the
##   walk dispatches over are in the IR, their own callees are not followed;
## - the target of a call through a proc value.
import std/[macros, hashes, os, strutils, tables]
import ./dsl_typebridge   ## `isUserRoutine`
import ./check_options    ## `routineChecks`

const ownRuntimeDir = currentSourcePath.parentDir.parentDir.replace('\\', '/') & "/"
  ## `src/nelli/`: nelli's own routines, keyed by the walker version.

proc isOwnRuntime(sym: NimNode): bool =
  sym.getImpl.lineInfoObj.filename.replace('\\', '/').startsWith(ownRuntimeDir)

proc serialise(n: NimNode; s: var string; refs: var seq[NimNode]) =
  ## Kind, literal and symbol name, in tree order. A user routine named here is
  ## collected for the walk.
  s.add $ord(n.kind)
  case n.kind
  of nnkCharLit .. nnkUInt64Lit: s.add ':' & $n.intVal
  of nnkFloatLit .. nnkFloat64Lit: s.add ':' & $n.floatVal
  of nnkStrLit .. nnkTripleStrLit:
    s.add ':' & $n.strVal.len & ':' & n.strVal
  of nnkIdent: s.add ':' & n.strVal
  of nnkSym:
    s.add ':' & n.strVal & '/' & $n.symKind
    if isUserRoutine(n): refs.add n
  of nnkCommentStmt, nnkEmpty, nnkNilLit, nnkNone, nnkType: discard
  else:
    s.add '('
    for c in n: serialise(c, s, refs)
    s.add ')'

proc implDigest*(fn: NimNode): string =
  ## Empty when `fn` names no user routine outside nelli and the stdlib, so such
  ## a program keys as it did before R1-09.
  if fn.kind != nnkSym: return ""
  let root = fn.getImpl
  if root.kind notin RoutineNodes or root.len < 7: return ""
  var work: seq[NimNode]
  var canon: string
  block:
    var s: string
    serialise(root[6], s, work)   # only for what it names
  var seen: seq[NimNode] = @[fn]
  var i = 0
  while i < work.len:
    let r = work[i]
    inc i
    var dup = false
    for x in seen:
      if x == r:
        dup = true
        break
    if dup: continue
    seen.add r
    if isOwnRuntime(r): continue
    let impl = r.getImpl
    if impl.kind notin RoutineNodes: continue
    let c = routineChecks(impl)
    canon.add "R" & $r.symKind & ":" & r.strVal & "|ck=" & $c.checks &
      (if c.why.len > 0: "|ck?" else: "") & "|"
    # The whole definition: name, parameters, pragmas, body. A foreign
    # routine's body slot is empty; its pragmas name what it binds to.
    serialise(impl, canon, work)
    canon.add '\n'
  if canon.len == 0: return ""
  # `std/sha1` does not run at compile time; two independent 64-bit hashes and
  # the length stand in for it.
  $canon.len & "-" & toHex(hash(canon)) & toHex(hash("nelli/R1-09\0" & canon))
