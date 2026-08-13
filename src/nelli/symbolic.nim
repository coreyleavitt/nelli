## Symbolic-reference stateful rules (#109).
##
## Builds on `promise_store.nim` (the typed cell-of-V) and `stateful.nim`
## (the `Rule[S]` type + `stateful` runner) to give us qsm-parity rule
## constructors:
##
## - `producingRule[S, A, V]` — fires `action: proc(s, a): V`, fulfills
##   the returned V in the current promise store under `(name, occ)`.
## - `consumingRule[S, A, V0]` — resolves one `SymRef[V0]` before fire;
##   disabled (not enumerated by the stateful runner) when its consumed
##   ref isn't yet fulfilled.
## - `consumingRule[S, A, V0, V1]` — 2-arity. Higher arities deferred to
##   a macro follow-up (#122).
##
## Dependency-respecting shrinking is automatic: the stateful runner
## encodes the plan in the choice IR; the shrinker deletes spans and
## replays; an orphan consumer (one whose producer was dropped) hits
## the runtime enablement predicate and is skipped. No shrinker work.
##
## **Coexists with `Bundle[S, V]`**. Bundle expresses "any V from a
## pool, indifferent to identity"; SymRef expresses "the V from rule X
## occurrence k, identity-preserving." Different idioms; real tests
## freely mix both.

import ./strategy, ./datasource, ./stateful, ./promise_store
export promise_store

proc producingRule*[S, A, V](
    name: string,
    args: Strategy[A],
    action: proc(s: var S, a: A): V,
    precondition: proc(s: S): bool = nil): Rule[S] =
  ## A rule that draws an `A` from `args`, fires `action(s, a)`, and
  ## stores the returned `V` in the current promise store under
  ## `(name, nextOccurrence(name))`. Subsequent `consumingRule`s
  ## referencing `symRef[V](name, k)` see this V at occurrence k.
  Rule[S](
    name: name,
    precondition: precondition,
    runStep: proc(s: var S, src: var DataSource) =
      let a = args.run(src)
      let store = storeNow()
      let occ = if store != nil: store.nextOccurrence(name) else: 0
      let produced = action(s, a)
      if store != nil:
        store.fulfill[:V]((ruleName: name, occurrence: occ), produced)
        store.bumpOccurrence(name))

proc consumingRule*[S, A, V0](
    name: string,
    args: Strategy[A],
    consumes: SymRef[V0],
    action: proc(s: var S, a: A, ref0: V0),
    precondition: proc(s: S): bool = nil): Rule[S] =
  ## A rule that resolves one symbolic ref from the current store
  ## before firing. Enablement: the rule is filtered out by the
  ## stateful runner iff the consumed ref isn't yet fulfilled (or
  ## the user precondition fails).
  let consumedId = consumes.id
  Rule[S](
    name: name,
    precondition: proc(s: S): bool =
      let store = storeNow()
      if store == nil or not store.has(consumedId): return false
      if precondition.isNil: return true
      precondition(s),
    runStep: proc(s: var S, src: var DataSource) =
      let a = args.run(src)
      let store = storeNow()
      let v0 = store.read[:V0](consumedId)
      action(s, a, v0))

proc consumingRule*[S, A, V0, V1](
    name: string,
    args: Strategy[A],
    consumes: (SymRef[V0], SymRef[V1]),
    action: proc(s: var S, a: A, ref0: V0, ref1: V1),
    precondition: proc(s: S): bool = nil): Rule[S] =
  ## 2-arity consume. 3+ arities deferred to #122 (macro / varargs).
  let id0 = consumes[0].id
  let id1 = consumes[1].id
  Rule[S](
    name: name,
    precondition: proc(s: S): bool =
      let store = storeNow()
      if store == nil: return false
      if not store.has(id0) or not store.has(id1): return false
      if precondition.isNil: return true
      precondition(s),
    runStep: proc(s: var S, src: var DataSource) =
      let a = args.run(src)
      let store = storeNow()
      let v0 = store.read[:V0](id0)
      let v1 = store.read[:V1](id1)
      action(s, a, v0, v1))
