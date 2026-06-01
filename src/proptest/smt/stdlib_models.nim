## Stdlib model registry — Phase 5+ home for symex models of stdlib
## procs (`[]`/`[]=`/`contains`/`len`/`add`/`del`/...).
##
## A "model" here is a hand-written specification of a stdlib proc's
## behavior at the Z3 level: rather than walking the proc's
## implementation (which leaves the supported fragment quickly), the
## walker consults this registry and emits the symbolic effect
## directly.
##
## The registry's shape will be:
##
## ```nim
## type StdlibModel = proc(call: IRStmt, env: Env): seq[Path]
##
## var registry*: Table[string, StdlibModel]
##
## proc registerStdlibModel*(name: string, m: StdlibModel)
## ```
##
## Phase 3 ships this file empty — the framework lands when Phase 5
## (dynamic seq / Table / HashSet) needs the first models.
##
## Until then, calls to stdlib procs fall through to the standard
## `getImpl`-and-walk path, which works for any proc whose
## implementation is reachable.

import ./types

type
  StdlibModelKind* = enum
    smkUnregistered

  StdlibModel* = object
    kind*: StdlibModelKind

proc getStdlibModel*(callee: string): StdlibModel =
  ## Phase 3 stub: always returns `smkUnregistered`. Phase 5+ adds
  ## the registry table and per-callee entries.
  StdlibModel(kind: smkUnregistered)
