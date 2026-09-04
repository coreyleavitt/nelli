## Algebraic-laws property library.
##
## Pre-baked named properties for the common typeclasses (`eq`, `ord`,
## `semigroup`, `monoid`). Each "laws" proc returns a `seq[NamedProperty]`
## — one entry per *named law* so a failure points exactly at which
## algebraic property is broken, not "the monoid laws failed."
##
## Idiomatic use inside `std/unittest`:
##
## ```nim
## suite "MySeq[int] is a monoid":
##   for law in monoidLaws(arbitrary(MySeq[int]), `&`, @[]):
##     test law.name:
##       check law.check()
## ```
##
## Why type-erase via `proc(): bool`: the laws can span multiple types
## (e.g. functor `F[A]` vs `F[B]`), so a typed `LawSuite[T]` would
## force the caller into matching gymnastics. Erasure keeps the
## ergonomic surface uniform.

import std/[options]
import ./strategy, ./engine, ./datasource

type
  NamedProperty* = object
    ## One algebraic law, packaged for batch execution. `check` runs an
    ## internal `forAll` and returns true iff the law holds at the
    ## chosen budget. `diagnostic` returns a `repro()`-format string
    ## of the failing example for triage when `check` returned false.
    name*: string
    check*: proc(): bool {.closure.}
    diagnostic*: proc(): string {.closure.}

const lawSettings = Settings(
    maxExamples: 100, maxRejections: 1000,
    seed: 0x1234567890abcdef'u64, flakyRetries: 0,
    maxShrinks: 200, useSA: false, targetedSAIters: 0,
    printEvents: false, autoLabels: false)
    ## RFC-0010 A1b pin. This is the library doing the defect to itself: an
    ## in-`src` hand-copy of `defaultSettings()`' values that silently omitted
    ## `autoLabels`, so law runs got `false` where the copy's author plainly
    ## meant "the defaults, with these four turned off". Writing the zero
    ## explicitly keeps today's behaviour across A2's flip; A3 decides whether
    ## the law suite actually wants the label sink on.

proc namedProperty[T](name: string, s: Strategy[T],
                      pred: proc(x: T): bool): NamedProperty =
  ## Internal: wrap a `T → bool` predicate as a `NamedProperty`. The
  ## same `s` and `pred` are reused by both `check` and `diagnostic`,
  ## so a failed `check` followed by `diagnostic` re-runs (deterministic
  ## in the seed) — the user sees the same counterexample either way.
  NamedProperty(
    name: name,
    check: proc(): bool =
      let r = forAll(s, proc(x: T) = (ensure pred(x)), lawSettings)
      r.outcome == otPassed,
    diagnostic: proc(): string =
      let r = forAll(s, proc(x: T) = (ensure pred(x)), lawSettings)
      repro(r))

proc pair[T](s: Strategy[T]): Strategy[(T, T)] =
  newStrategy(proc(src: var DataSource): (T, T) =
    let a = s.run(src); let b = s.run(src); (a, b))

proc triple[T](s: Strategy[T]): Strategy[(T, T, T)] =
  newStrategy(proc(src: var DataSource): (T, T, T) =
    let a = s.run(src); let b = s.run(src); let c = s.run(src); (a, b, c))

proc eqLaws*[T](s: Strategy[T]): seq[NamedProperty] =
  ## Reflexivity, symmetry, transitivity for `T`'s default `==`.
  ## Reflexivity:  ∀x. x == x.
  ## Symmetry:     ∀x, x'. (x == x') iff (x' == x).
  ## Transitivity: ∀x, y, z. (x == y ∧ y == z) ⇒ (x == z).
  ##               Vacuously true for distinct draws — independent
  ##               draws rarely satisfy the antecedent, but the
  ##               law statement is still well-defined and the test
  ##               is sound (a counterexample requires false in the
  ##               consequent given true in the antecedent, which can
  ##               never trigger spuriously).
  result.add namedProperty("reflexivity", s,
    proc(x: T): bool = x == x)
  result.add namedProperty("symmetry", pair(s),
    proc(xy: (T, T)): bool = (xy[0] == xy[1]) == (xy[1] == xy[0]))
  result.add namedProperty("transitivity", triple(s),
    proc(xyz: (T, T, T)): bool =
      not (xyz[0] == xyz[1] and xyz[1] == xyz[2]) or xyz[0] == xyz[2])

proc semigroupLaws*[T](s: Strategy[T],
                       op: proc(a, b: T): T): seq[NamedProperty] =
  ## Associativity: ∀x, y, z. op(op(x, y), z) == op(x, op(y, z)).
  result.add namedProperty("associativity", triple(s),
    proc(xyz: (T, T, T)): bool =
      op(op(xyz[0], xyz[1]), xyz[2]) == op(xyz[0], op(xyz[1], xyz[2])))

proc ordLaws*[T](s: Strategy[T]): seq[NamedProperty] =
  ## eq laws plus the three ord-specific laws for `<=`:
  ##   Antisymmetry:      ∀x, y. (x <= y ∧ y <= x) ⇒ x == y.
  ##   Totality:          ∀x, y. x <= y ∨ y <= x.
  ##   Transitivity of <=: ∀x, y, z. (x <= y ∧ y <= z) ⇒ x <= z.
  result.add eqLaws(s)
  result.add namedProperty("antisymmetry", pair(s),
    proc(xy: (T, T)): bool =
      not (xy[0] <= xy[1] and xy[1] <= xy[0]) or xy[0] == xy[1])
  result.add namedProperty("totality", pair(s),
    proc(xy: (T, T)): bool = xy[0] <= xy[1] or xy[1] <= xy[0])
  result.add namedProperty("transitivity of <=", triple(s),
    proc(xyz: (T, T, T)): bool =
      not (xyz[0] <= xyz[1] and xyz[1] <= xyz[2]) or xyz[0] <= xyz[2])

proc monoidLaws*[T](s: Strategy[T], op: proc(a, b: T): T,
                    id: T): seq[NamedProperty] =
  ## Semigroup associativity, plus:
  ##   Left identity:  ∀x. op(id, x) == x.
  ##   Right identity: ∀x. op(x, id) == x.
  result.add semigroupLaws(s, op)
  result.add namedProperty("left identity", s,
    proc(x: T): bool = op(id, x) == x)
  result.add namedProperty("right identity", s,
    proc(x: T): bool = op(x, id) == x)
