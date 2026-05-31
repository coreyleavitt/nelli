import std/unittest
import proptest

# Regression for the nopal-filed friction (REQUIRESINIT_DSL_FRICTION.md):
# the `given` DSL and the `tuples` combinator recover a strategy's element
# type via `typeof(valueType(s))`. The phantom `valueType` used to have a
# `default(T)` body, which is invalid for `{.requiresInit.}` types — so a
# perfectly valid strategy (one that never default-constructs its element)
# could not be bound through the DSL purely because of how `T` was recovered.
# On modern Nim that surfaces as `UnsafeDefault`/`UnsafeSetLen` warnings
# (hard errors under strict-def settings); this file is compiled with those
# warnings escalated to errors, so any default-construction of a requiresInit
# type inside proptest's own expansion fails the build.
#
# Two representative shapes are bound through every macro site that touches
# `valueType`:
#   * `Snap`  — a non-variant object with all-required fields (cf. nopal's
#               TrackerSnapshot), the classic "requiresInit" shape.
#   * `Ev`    — a requiresInit object *variant* (cf. nopal's StateEvent).

type
  Snap {.requiresInit.} = object
    state: int
    count: int

  Ev {.requiresInit.} = object
    case kind: bool
    of true:  a: int
    of false: discard

proc snaps(): Strategy[Snap] =
  ## Never default-constructs `Snap` — always builds fully-initialized values.
  map(tuples(integers(0, 4), integers(0, 9)),
      proc(t: (int, int)): Snap = Snap(state: t[0], count: t[1]))

proc evs(): Strategy[Ev] =
  oneOf(@[
    just(Ev(kind: true, a: 0)),
    just(Ev(kind: false)),
  ])

suite "DSL: requiresInit element types":
  property "single given binds a requiresInit object variant":
    given e in evs()
    ensure e.kind or not e.kind

  property "single given binds a requiresInit required-fields object":
    given s in snaps()
    ensure s.state >= 0 and s.count >= 0

  property "multi-binding given mixes requiresInit and ordinary types":
    # Exercises the DSL's N>=2 tuple path: each element type is recovered via
    # `typeof(valueType(s_i))` and the engine carries a `(Ev, Snap, int)` tuple
    # — itself requiresInit-tainted — through generation and shrinking.
    given e in evs(), s in snaps(), k in integers(0, 3)
    ensure (e.kind or not e.kind) and s.state >= 0 and k <= 3

  property "examples pins a requiresInit regression seed":
    # The pinned seed flows through the DSL's `seq[typeof(valueType(strat))]`
    # and the engine's explicit-examples seq — both built without
    # default-constructing the requiresInit element.
    examples Ev(kind: true, a: 42)
    given e in evs()
    ensure (not e.kind) or e.a >= 0

  property "tuples() combinator accepts requiresInit components":
    # `tuples` (strategy.nim) recovers each component type via
    # `typeof(valueType(s_i))` — the second `valueType` call site.
    given pair in tuples(evs(), snaps())
    ensure (pair[0].kind or not pair[0].kind) and pair[1].count >= 0
