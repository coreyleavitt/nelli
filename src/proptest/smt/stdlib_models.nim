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

proc getStdlibModelFor*(callee: string, recvKind: IRTypeKind): StdlibModel =
  ## Resolve `callee` against a receiver kind, mirroring what the
  ## parser does inline: `len(s) on seq → seqLen`, etc.
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
