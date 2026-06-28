## Phase 14 cycle A2 — `else:` arms in variants (ADR-0003 D2).
##
## Pre-A2 the parser errored on `nnkElse` branches inside an
## `nnkRecCase` (dsl_typebridge.nim:199-201). A2 makes the
## typebridge collect the else branch as a `VariantArm` with
## `isElse=true, tagOrdinal=-1` (sentinel), wires the walker to
## emit `AND(disc != other.tagOrdinal)` for the else-arm membership
## constraint, and extends the witness emitter to render the else
## branch.
##
## The body's reach test pins the discriminator to a tag covered
## by `else:`. If the walker rejects else or constrains it wrong,
## either the witness misses the target (sxUnsat) or pins the
## wrong tag.
import std/unittest
import proptest/symex
import proptest/smt/types

type
  K = enum kA, kB, kC
  V = object
    case kind: K
    of kA: a: int
    else: x: int  ## covers kB AND kC

proc hitInElse(v: V) =
  # Reach is gated on `v.kind == kB` AND `v.x == 99`. kB is part
  # of the else arm (only kA is on its own arm). The walker must
  # treat the else arm as "disc != kA.ord", inside which v.x lives.
  # Phase 16 D1c: restored flat-and form.
  if v.kind == kB and v.x == 99:
    symexTarget("else-hit")

suite "symex Phase 14 cycle A2 — else: arms in variants":
  test "variant with `else:` arm parses + walker reaches target in else":
    let r = symexFind(hitInElse, tLabel("else-hit"))
    check r.status == sxSat
    check r.witness[0].kind == kB
    check r.witness[0].x == 99
