## Phase 15 — Cluster E, cycle E4: static exception-type hierarchy.
##
## `exnTypeTable` is a compile-time constant mapping each standard Nim
## exception type name to its FULL ancestor chain (nearest parent first,
## up to the `Exception` root). Storing the full chain makes `isSubtypeOf`
## a membership test rather than a repeated parent-lookup walk.
##
## The ancestry encoded here is Nim's REAL system hierarchy
## (`lib/system.nim` + `lib/system/exceptions.nim`, verified against
## Nim 2.2.10):
##
##   Exception                       (root, of RootObj)
##   ├─ Defect                       (of Exception)
##   │   ├─ IndexDefect
##   │   ├─ FieldDefect
##   │   ├─ AssertionDefect
##   │   ├─ RangeDefect
##   │   ├─ OutOfMemDefect           (REAL name; OutOfMemoryDefect is an alias)
##   │   └─ StackOverflowDefect
##   └─ CatchableError               (of Exception)
##       ├─ ValueError
##       │   └─ KeyError             (KeyError is-a ValueError, NOT directly CatchableError)
##       ├─ IOError
##       └─ OSError
##
## `isSubtypeOf(raised, handlerType, exnTable, userExnHierarchy)` answers
## "does an `except handlerType:` clause catch a raised `raised`?": true iff
## `handlerType == raised` or `handlerType` is an ancestor of `raised`.
## A bare `except:` (empty typeIds) is handled by the caller, not here.
##
## `isDefect(...)` answers "is this type a Defect (subtype)?" — true for any
## known Defect subtype, and (dkOther fallback) for an unknown type whose
## chain in `userExnHierarchy` traces to `Defect`. The dynamic capture that
## fills `userExnHierarchy` from a SUT's `getImpl` is E4a; until then it is
## empty and only standard types resolve.

import std/tables

const exnTypeTable*: Table[string, seq[string]] = {
  # root
  "Exception":            @[],
  # Exception's two direct children
  "Defect":               @["Exception"],
  "CatchableError":       @["Exception"],
  # CatchableError subtypes
  "ValueError":           @["CatchableError", "Exception"],
  "IOError":              @["CatchableError", "Exception"],
  "OSError":              @["CatchableError", "Exception"],
  # KeyError is-a ValueError (the real Nim ancestry)
  "KeyError":             @["ValueError", "CatchableError", "Exception"],
  # Defect subtypes
  "IndexDefect":          @["Defect", "Exception"],
  "FieldDefect":          @["Defect", "Exception"],
  "AssertionDefect":      @["Defect", "Exception"],
  "RangeDefect":          @["Defect", "Exception"],
  "OutOfMemDefect":       @["Defect", "Exception"],
  # `OutOfMemoryDefect` is the RFC/checklist spelling; the real Nim type is
  # `OutOfMemDefect`. Keep both names resolving to the same chain so a SUT
  # written against either spelling classifies correctly.
  "OutOfMemoryDefect":    @["Defect", "Exception"],
  "StackOverflowDefect":  @["Defect", "Exception"],
}.toTable

proc ancestorsOf(raised: string,
                 exnTable: Table[string, seq[string]],
                 userExnHierarchy: Table[string, string]): seq[string] =
  ## The full ancestor chain of `raised` (nearest parent first, toward
  ## `Exception`). Resolution order: the static `exnTable` first (full chain
  ## stored directly); otherwise walk `userExnHierarchy` (child -> direct
  ## parent, E4a-populated) one link at a time, splicing in the static chain
  ## of the first standard ancestor we reach. Returns `@[]` for a type that
  ## is in neither table (an unknown type — the caller treats it
  ## conservatively).
  if raised in exnTable:
    return exnTable[raised]
  # Unknown to the static table: chase the user (child->parent) links.
  var cur = raised
  var guard = 0
  while cur in userExnHierarchy and guard < 64:
    let parent = userExnHierarchy[cur]
    result.add parent
    if parent in exnTable:
      # Splice the static ancestors of this standard parent and stop.
      result.add exnTable[parent]
      return
    cur = parent
    inc guard

proc isSubtypeOf*(raised, handlerType: string,
                  exnTable: Table[string, seq[string]],
                  userExnHierarchy: Table[string, string]): bool =
  ## Phase 15 E4. True iff an `except handlerType:` clause catches a raised
  ## `raised` — i.e. `handlerType == raised`, or `handlerType` is an ancestor
  ## of `raised`. A bare `except:` (empty handler typeIds) is the caller's
  ## responsibility (catch-all); this proc is only consulted for a NAMED
  ## handler type. Pure lookup — no Z3.
  if handlerType == raised:
    return true
  handlerType in ancestorsOf(raised, exnTable, userExnHierarchy)

proc isKnownExnType*(typeId: string,
                     exnTable: Table[string, seq[string]],
                     userExnHierarchy: Table[string, string]): bool =
  ## True iff `typeId` is resolvable through either table. An unknown type
  ## (false here) matches only a bare `except:` and is reported as a
  ## `sevWarning` (Invariant 3 — no silent false-negative).
  typeId in exnTable or typeId in userExnHierarchy

proc isDefect*(exnTable: Table[string, seq[string]],
               typeId: string,
               userExnHierarchy: Table[string, string] =
                 initTable[string, string]()): bool =
  ## Phase 15 E4. True iff `typeId` is `Defect` itself or a Defect subtype.
  ## Known standard types resolve via the static chain; an unknown user type
  ## resolves via the dkOther fallback — its `userExnHierarchy` chain tracing
  ## to `Defect` (the dynamic capture filling `userExnHierarchy` is E4a).
  if typeId == "Defect":
    return true
  "Defect" in ancestorsOf(typeId, exnTable, userExnHierarchy)
