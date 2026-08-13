## Phase 14 cycle A5 — composite arm-field zero-init under
## static-tag discriminator reassignment (ADR-0003 D5).
##
## Phase 11 cycle 6 only zero-init'd PRIMITIVES on reassignment
## (runtime.nim:defaultPrim raised for anything else). A5 replaces
## that with `allocateSym`-driven construction, reusing the same
## per-type SymVal builder the parameter-bind path uses. Arm
## fields of composite type (tuples, seqs, arrays) survive a
## static-tag reassignment with sensible default values.
##
## Scope: A5 inherits `allocateSym`'s scope — `Table[K≠string]`
## and `HashSet[T≠int64]` arm fields still raise (documented
## sub-deferral per RFC §A5).
##
## RED test: SUT reassigns the disc to an arm whose payload is a
## composite (here, a tuple). Pre-A5 the walker crashes with
## "arm field type ... not supported (primitives only)". Post-A5
## the walker reaches the target.
import std/unittest
import nelli/symex
import nelli/smt/types

type
  K = enum kA, kB
  V = object
    case kind: K
    of kA: a: int
    of kB: b: tuple[x: int, y: int]

proc reassignToComposite(v: var V) =
  # Pre-A5: this static-tag reassignment crashes because `b` is
  # tuple, not a primitive. Post-A5: zero-init succeeds; we reach
  # the target unconditionally.
  v.kind = kB
  symexTarget("reassigned")

suite "symex Phase 14 cycle A5 — composite arm-field zero-init":
  test "static reassignment to composite-payload arm doesn't crash":
    let r = symexFind(reassignToComposite, tLabel("reassigned"))
    check r.status == sxSat
