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
import std/[macros, os, strutils]
import ./dsl_typebridge   ## `isUserRoutine`
import ./check_options    ## `routineChecks`
import ./sha256           ## `sha256Hex`, VM-safe (review R3, E10)

const ownRuntimeDir = currentSourcePath.parentDir.parentDir.replace('\\', '/') & "/"
  ## `src/nelli/`: nelli's own routines, keyed by the walker version. Absolute
  ## and slash-terminated, so a user file elsewhere whose path merely contains
  ## `src/nelli` (another checkout, `src/nelli-extras/`) is not matched.

func pathUnder*(file, dir: string): bool =
  ## Whether `file` lies inside the slash-terminated `dir`. Compared
  ## case-insensitively on Windows, whose paths are.
  let f = file.replace('\\', '/')
  when defined(windows): f.toLowerAscii.startsWith(dir.toLowerAscii)
  else: f.startsWith(dir)

proc isOwnRuntime(sym: NimNode): bool =
  pathUnder(sym.getImpl.lineInfoObj.filename, ownRuntimeDir)

proc serialise(n: NimNode; s: var string; refs: var seq[NimNode]) =
  ## An injective, self-delimiting encoding in tree order: every node is
  ## `k<kind>.`, then a leaf's value as `<len>:<bytes>` or a composite's
  ## `<child count>(` children `)`. No value or sibling can run into the next
  ## node's digits. A user routine named here is collected for the walk.
  proc leaf(s: var string; v: string) =
    s.add $v.len & ':' & v
  s.add 'k' & $ord(n.kind) & '.'
  case n.kind
  of nnkCharLit .. nnkUInt64Lit: leaf(s, $n.intVal)
  of nnkFloatLit .. nnkFloat64Lit: leaf(s, $n.floatVal)
  of nnkStrLit .. nnkTripleStrLit: leaf(s, n.strVal)
  of nnkIdent: leaf(s, n.strVal)
  of nnkSym:
    leaf(s, n.strVal & '/' & $n.symKind)
    if isUserRoutine(n): refs.add n
  of nnkCommentStmt, nnkEmpty, nnkNilLit, nnkNone, nnkType: discard
  else:
    s.add $n.len & '('
    for c in n: serialise(c, s, refs)
    s.add ')'

proc serialiseNode*(n: NimNode): string =
  ## `serialise` without the routine walk, for the injectivity tests.
  var refs: seq[NimNode]
  serialise(n, result, refs)

proc implDigest*(fn: NimNode): string =
  ## Empty when `fn` names no user routine outside nelli and the stdlib, so such
  ## a program keys as it did before R1-09.
  if fn.kind != nnkSym: return ""
  let root = fn.getImpl
  if root.kind notin RoutineNodes or root.len < 7: return ""
  var work: seq[NimNode]
  # Review R3 (SC2): the domain tag starts the text the hash reads, so the
  # canon is never copied to be prefixed.
  const tag = "nelli/R2-SM2\0"
  var canon = tag
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
    canon.add "R" & $r.symKind & ":" & $r.strVal.len & ":" & r.strVal &
      "|ck=" & $c.checks & (if c.why.len > 0: "|ck?" else: "") & "|"
    # The whole definition: name, parameters, pragmas, body. A foreign
    # routine's body slot is empty; its pragmas name what it binds to.
    serialise(impl, canon, work)
    canon.add '\n'
  if canon.len == tag.len: return ""
  # SHA-256 over the tag and the whole serialisation (`sha256.nim`).
  "sha256-" & sha256Hex(canon)
