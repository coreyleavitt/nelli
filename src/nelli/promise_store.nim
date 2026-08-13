## Typed promise store for symbolic-ref stateful testing (#109).
##
## Lifted into its own leaf so both `stateful.nim` (the runner, which
## allocates a fresh store per example) and `symbolic.nim` (the rule
## builders, which read/write it) can depend on it without creating a
## cycle. Neither imports the other.

import std/tables

type
  PromiseId* = tuple[ruleName: string, occurrence: int]

  PromiseBase* = ref object of RootObj
    ## Type-erased base. Each cell in the store is a subclass.

  Promise*[V] = ref object of PromiseBase
    ## A fulfilled symbolic value of type `V`. Retrieval is safe via
    ## Nim's `of` operator (ref RTTI) — a mistyped read raises before
    ## the downcast.
    value*: V

  SymRef*[V] = object
    ## Plan-time reference to a value some other rule produced. `V` is
    ## phantom — preserved for type-checking the action body; the
    ## runtime ref is keyed by `id` only.
    id*: PromiseId

  PromiseStore* = ref object
    cells: Table[PromiseId, PromiseBase]
    occurrences: Table[string, int]

proc newPromiseStore*(): PromiseStore =
  PromiseStore(cells: initTable[PromiseId, PromiseBase](),
               occurrences: initTable[string, int]())

proc symRef*[V](ruleName: string, occurrence = 0): SymRef[V] =
  SymRef[V](id: (ruleName: ruleName, occurrence: occurrence))

proc has*(store: PromiseStore, id: PromiseId): bool =
  store.cells.hasKey(id)

proc fulfill*[V](store: PromiseStore, id: PromiseId, value: V) =
  store.cells[id] = Promise[V](value: value)

proc read*[V](store: PromiseStore, id: PromiseId): V =
  if not store.cells.hasKey(id):
    raise newException(ValueError,
      "promise " & $id & " has no fulfilled value")
  let p = store.cells[id]
  if not (p of Promise[V]):
    raise newException(ValueError,
      "promise " & $id & " is not of the requested type")
  Promise[V](p).value

proc nextOccurrence*(store: PromiseStore, ruleName: string): int =
  if store.occurrences.hasKey(ruleName): store.occurrences[ruleName] else: 0

proc bumpOccurrence*(store: PromiseStore, ruleName: string) =
  store.occurrences[ruleName] = nextOccurrence(store, ruleName) + 1

# Threadvar handle. The stateful runner installs a fresh store at the
# start of each generated example, clears it on exit. Rule action
# closures access the current store via `storeNow()`.

var currentPromiseStore* {.threadvar.}: PromiseStore

proc installPromiseStore*(store: PromiseStore) =
  currentPromiseStore = store

proc storeNow*(): PromiseStore =
  currentPromiseStore
