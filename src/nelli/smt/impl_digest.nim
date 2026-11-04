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

# SHA-256 (FIPS 180-4) in plain Nim. `std/sha1` imports C (`c_memcpy`) and
# cannot run in the compile-time VM, which is where the digest is computed, so
# the hash is written out here. Checked against the standard vectors in
# `tests/tsymex_rfc0005_r2_impldigest.nim`.
const sha256K = [
  0x428a2f98'u32, 0x71374491'u32, 0xb5c0fbcf'u32, 0xe9b5dba5'u32,
  0x3956c25b'u32, 0x59f111f1'u32, 0x923f82a4'u32, 0xab1c5ed5'u32,
  0xd807aa98'u32, 0x12835b01'u32, 0x243185be'u32, 0x550c7dc3'u32,
  0x72be5d74'u32, 0x80deb1fe'u32, 0x9bdc06a7'u32, 0xc19bf174'u32,
  0xe49b69c1'u32, 0xefbe4786'u32, 0x0fc19dc6'u32, 0x240ca1cc'u32,
  0x2de92c6f'u32, 0x4a7484aa'u32, 0x5cb0a9dc'u32, 0x76f988da'u32,
  0x983e5152'u32, 0xa831c66d'u32, 0xb00327c8'u32, 0xbf597fc7'u32,
  0xc6e00bf3'u32, 0xd5a79147'u32, 0x06ca6351'u32, 0x14292967'u32,
  0x27b70a85'u32, 0x2e1b2138'u32, 0x4d2c6dfc'u32, 0x53380d13'u32,
  0x650a7354'u32, 0x766a0abb'u32, 0x81c2c92e'u32, 0x92722c85'u32,
  0xa2bfe8a1'u32, 0xa81a664b'u32, 0xc24b8b70'u32, 0xc76c51a3'u32,
  0xd192e819'u32, 0xd6990624'u32, 0xf40e3585'u32, 0x106aa070'u32,
  0x19a4c116'u32, 0x1e376c08'u32, 0x2748774c'u32, 0x34b0bcb5'u32,
  0x391c0cb3'u32, 0x4ed8aa4a'u32, 0x5b9cca4f'u32, 0x682e6ff3'u32,
  0x748f82ee'u32, 0x78a5636f'u32, 0x84c87814'u32, 0x8cc70208'u32,
  0x90befffa'u32, 0xa4506ceb'u32, 0xbef9a3f7'u32, 0xc67178f2'u32]

func rotr(x: uint32; n: int): uint32 {.inline.} =
  (x shr n.uint32) or (x shl (32 - n).uint32)

func sha256Hex*(msg: string): string =
  ## Lower-case hex SHA-256 of `msg`; runs at compile time.
  var h = [0x6a09e667'u32, 0xbb67ae85'u32, 0x3c6ef372'u32, 0xa54ff53a'u32,
           0x510e527f'u32, 0x9b05688c'u32, 0x1f83d9ab'u32, 0x5be0cd19'u32]
  var m = msg
  let bitLen = uint64(msg.len) * 8'u64
  m.add '\x80'
  while m.len mod 64 != 56: m.add '\0'
  for i in countdown(7, 0): m.add char((bitLen shr uint64(i * 8)) and 0xff'u64)
  var w: array[64, uint32]
  var off = 0
  while off < m.len:
    for i in 0 ..< 16:
      w[i] = (uint32(ord(m[off + 4*i])) shl 24) or
             (uint32(ord(m[off + 4*i + 1])) shl 16) or
             (uint32(ord(m[off + 4*i + 2])) shl 8) or
             uint32(ord(m[off + 4*i + 3]))
    for i in 16 ..< 64:
      let s0 = rotr(w[i-15], 7) xor rotr(w[i-15], 18) xor (w[i-15] shr 3'u32)
      let s1 = rotr(w[i-2], 17) xor rotr(w[i-2], 19) xor (w[i-2] shr 10'u32)
      w[i] = w[i-16] + s0 + w[i-7] + s1
    var a = h[0]; var b = h[1]; var c = h[2]; var d = h[3]
    var e = h[4]; var f = h[5]; var g = h[6]; var hh = h[7]
    for i in 0 ..< 64:
      let s1 = rotr(e, 6) xor rotr(e, 11) xor rotr(e, 25)
      let ch = (e and f) xor ((not e) and g)
      let t1 = hh + s1 + ch + sha256K[i] + w[i]
      let s0 = rotr(a, 2) xor rotr(a, 13) xor rotr(a, 22)
      let maj = (a and b) xor (a and c) xor (b and c)
      let t2 = s0 + maj
      hh = g; g = f; f = e; e = d + t1
      d = c; c = b; b = a; a = t1 + t2
    h[0] += a; h[1] += b; h[2] += c; h[3] += d
    h[4] += e; h[5] += f; h[6] += g; h[7] += hh
    off += 64
  const hex = "0123456789abcdef"
  for x in h:
    for i in countdown(7, 0): result.add hex[int((x shr uint32(i * 4)) and 0xf'u32)]

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
    canon.add "R" & $r.symKind & ":" & $r.strVal.len & ":" & r.strVal &
      "|ck=" & $c.checks & (if c.why.len > 0: "|ck?" else: "") & "|"
    # The whole definition: name, parameters, pragmas, body. A foreign
    # routine's body slot is empty; its pragmas name what it binds to.
    serialise(impl, canon, work)
    canon.add '\n'
  if canon.len == 0: return ""
  # SHA-256 over the whole serialisation (see `sha256Hex`).
  "sha256-" & sha256Hex("nelli/R2-SM2\0" & canon)
