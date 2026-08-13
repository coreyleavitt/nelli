## Phase 15 — Cluster E, cycle E4a: dynamic user-exception hierarchy.
##
## E4 shipped the static `ExnTypeTable` (Nim's stdlib exn hierarchy) plus the
## `isSubtypeOf` membership logic that already consults `userExnHierarchy` as a
## fallback — but `userExnHierarchy` was EMPTY (no parser pass filled it). So a
## SUT that defines `type MyError = object of ValueError`, raises `MyError`, and
## catches `except ValueError:` would SILENTLY propagate (`sxRaised{MyError}`)
## because the walker had no link from `MyError` to its stdlib base.
##
## E4a closes that gap: a parser pass walks `getImpl` on every USER exception
## type symbol the SUT mentions — both the type in `raise newException(<T>, …)`
## AND the type in each `except <T>:` handler — recording each `child → parent`
## inheritance link into `userExnHierarchy` up to a known stdlib base. The
## walker's `isSubtypeOf` then bridges `MyError → ValueError` and on into
## `ValueError`'s static ancestor chain.
##
## NB: the raised-type capture is the reconciliation beyond the RFC's
## `nnkExceptBranch`-only wording — test 1 below raises `MyError` but catches
## `ValueError`, so `MyError`'s chain (which only appears at the RAISE site) is
## required to match.
import std/unittest
import nelli/symex
import nelli/smt/dsl

# Exception types are defined at module scope so the parser's `getImpl` on the
# raised/handler type symbols sees a concrete `nnkTypeDef` at macro expansion.

# --- 1. user subtype matched by base handler --------------------------------
type MyError = object of ValueError

proc caughtByBase(x: int): int =
  try:
    if x < 0: raise newException(MyError, "custom")
    result = x
  except ValueError:
    symexTarget("caught_by_base")
    result = -1

# --- 2. unrelated user type not matched -------------------------------------
type SomeError = object of IOError

proc unrelatedNoMatch(x: int): int =
  try:
    if x < 0: raise newException(SomeError, "boom")
    result = x
  except ValueError:
    result = -1

suite "symex Phase 15 E4a — dynamic user-exception hierarchy":
  test "E4a: user-defined exception subtype matched by base handler":
    # MyError is-a ValueError; `except ValueError:` must catch the raised
    # MyError. Without E4a this silently lands as sxRaised{MyError}.
    let r = symexFind(caughtByBase, tLabel("caught_by_base"))
    check r.status == sxSat
    check r.witness[0] < 0

  test "E4a: unrelated user type not matched by unrelated handler":
    # SomeError is-a IOError; `except ValueError:` does NOT catch it; it
    # propagates to the SUT boundary as sxRaised{SomeError}.
    let r = symexFind(unrelatedNoMatch, tRaisedExn("SomeError"))
    check r.status == sxRaised
    check r.raisedTypeId == "SomeError"
