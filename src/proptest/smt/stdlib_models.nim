## Stdlib model registry — Phase 5+ home for symex models of stdlib
## procs (`[]`/`[]=`/`contains`/`hasKey`/`len`/`add`/`incl`/`excl`...).
##
## Phase 5 populates the registry with the read-side accessors that
## the parser intercepts by name (`len`, `[]`, `contains`, `hasKey`).
## Each entry is identified by its Nim proc name and the **kind of
## receiver** it targets — the same name (`len`) maps to different
## semantics for `seq[T]` vs (later) `string`, etc.
##
## The registry is consulted both:
##   * By the parser (to recognise the call before it falls into
##     `getImpl`-based resolution, which would error on generic
##     receivers).
##   * By tests like `tsymex_phase5_models` (to verify the catalog
##     reflects what the parser actually handles).

import ./types

type
  StdlibModelKind* = enum
    smkUnregistered
    smkSeqLen         ## `len(s: seq[T])` → seq length
    smkSeqIndex       ## `[](s: seq[T], i)` → element at i
    smkTableIndex     ## `[](t: Table[K, V], k)` → value at k
    smkTableContains  ## `contains(t, k)` / `hasKey(t, k)`
    smkSetContains    ## `contains(s: HashSet[T], x)` / `x in s`
    smkOpaqueEffectful ## #137: known-effectful proc; symex skips the
                       ## body, returns a fresh symbol, and marks the
                       ## surviving path uncertain.
    # ---- Phase 15 Cluster S (S1 stubs). One model kind per Z3-String op the
    # parser will route an `itString`-receiver call to. S1 registers them all in
    # the `of itString:` dispatch but they remain inert routing targets until the
    # owning cycle (noted) fleshes out the real parse → `iekStr*` lowering.
    smkStrLen          ## `s.len`            (S3)
    smkStrIndex        ## `s[i]` read        (S3)
    smkStrAt           ## `s.at(i)`          (S3)
    smkStrSubstr       ## `s[a..b]`          (S3)
    smkStrFind         ## `s.find(sub)`      (S4)
    smkStrContains     ## `sub in s`         (S4)
    smkStrStartsWith   ## `s.startsWith(p)`  (S4)
    smkStrEndsWith     ## `s.endsWith(q)`    (S4)
    smkStrReplace      ## `s.replace(o,n)`   (S5)
    smkStrReplaceAll   ## `s.replace(o,n)` all-occ (S5)
    smkStrSplit        ## `s.split(sep)`     (S5)
    smkStrJoin         ## `xs.join(sep)`     (S5)
    smkStrMatch        ## `s.match(re)`      (S6)
    smkStrBytes        ## `bytes(s)`         (S7a)

  StdlibModel* = object
    kind*: StdlibModelKind

const phase5Entries: array[5, tuple[name: string, kind: StdlibModelKind]] = [
  ("len_seq",         smkSeqLen),
  ("indexed_seq",     smkSeqIndex),
  ("indexed_table",   smkTableIndex),
  ("contains_table",  smkTableContains),
  ("contains_set",    smkSetContains),
]

proc getStdlibModel*(callee: string): StdlibModel =
  ## Look up by *qualified key* (`<callee>_<receiverKind>`). For
  ## bare-name queries (the parser's path), see `getStdlibModelFor`.
  for e in phase5Entries:
    if e.name == callee:
      return StdlibModel(kind: e.kind)
  StdlibModel(kind: smkUnregistered)

const mathFpModeledOps* = [
  ## Phase 15 F6: std/math (and system) float ops/predicates with a
  ## Z3-FP-native model. Routed to `iekMathCall`; lowered in runtime.nim.
  "abs", "sqrt", "min", "max",
  "floor", "ceil", "round", "trunc",
  "signbit", "isNaN", "isInf", "isFinite", "isNormal",
]

const mathFpDeferredOps* = [
  ## Phase 15 F6: float ops recognised by name but NOT yet modeled. These
  ## still route to `iekMathCall`; the runtime emits a classified
  ## `feUnsupportedOp` (sevError) rather than a silent UNSAT (Invariant 3).
  "classify", "copySign", "nextafter",
]

const OpaqueEffectfulProcs* = [
  "echo", "print", "write", "writeLine", "writeFile", "readFile",
  "stdout", "stderr", "readLine", "readAll", "openFileStream",
  "sleep", "send", "recv", "open", "close",
]

proc getStdlibModelFor*(callee: string, recvKind: IRTypeKind): StdlibModel =
  ## Resolve `callee` against a receiver kind, mirroring what the
  ## parser does inline: `len(s) on seq → seqLen`, etc.
  for opa in OpaqueEffectfulProcs:
    if callee == opa:
      return StdlibModel(kind: smkOpaqueEffectful)
  # Phase 15 Cluster S (S1). `itString`-receiver calls are recognised here so
  # the parser routes them to the `iekStr*` family instead of falling into
  # `getImpl`-based user-proc resolution (which crashes on built-ins like `len`).
  # In S1 every string op resolves to its `smkStr*` kind but the parser routes it
  # to a STUBBED `iekStr*` (classified `seUnsupportedStringOp`); S2–S11 flesh out
  # the real lowering one op per cycle. Unrecognised string calls → smkUnregistered.
  if recvKind == itString:
    case callee
    of "len":                  return StdlibModel(kind: smkStrLen)
    of "[]":                   return StdlibModel(kind: smkStrIndex)
    of "at":                   return StdlibModel(kind: smkStrAt)
    of "substr":               return StdlibModel(kind: smkStrSubstr)
    of "find":                 return StdlibModel(kind: smkStrFind)
    of "contains":             return StdlibModel(kind: smkStrContains)
    of "startsWith":           return StdlibModel(kind: smkStrStartsWith)
    of "endsWith":             return StdlibModel(kind: smkStrEndsWith)
    of "replace":              return StdlibModel(kind: smkStrReplace)
    of "replaceAll":           return StdlibModel(kind: smkStrReplaceAll)
    of "split":                return StdlibModel(kind: smkStrSplit)
    of "join":                 return StdlibModel(kind: smkStrJoin)
    of "match":                return StdlibModel(kind: smkStrMatch)
    of "bytes":                return StdlibModel(kind: smkStrBytes)
    else:                      return StdlibModel(kind: smkUnregistered)
  case callee
  of "len":
    if recvKind == itSeq: StdlibModel(kind: smkSeqLen)
    else: StdlibModel(kind: smkUnregistered)
  of "[]":
    case recvKind
    of itSeq:   StdlibModel(kind: smkSeqIndex)
    of itTable: StdlibModel(kind: smkTableIndex)
    else: StdlibModel(kind: smkUnregistered)
  of "contains", "hasKey":
    case recvKind
    of itTable: StdlibModel(kind: smkTableContains)
    of itSet:   StdlibModel(kind: smkSetContains)
    else: StdlibModel(kind: smkUnregistered)
  else:
    StdlibModel(kind: smkUnregistered)
