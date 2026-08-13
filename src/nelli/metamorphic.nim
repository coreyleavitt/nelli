## Metamorphic-testing combinators.
##
## When a function has no obvious oracle (you can't compute the
## expected output without re-implementing the system under test),
## *relations between outputs under input transformations* are often
## easy to state — and easy to test.
##
## Classic examples:
##   sort:        sort(reverse(xs)) == sort(xs)
##   search:      count(haystack, needle) == count(haystack ++ haystack, needle) / 2
##   compiler:    compile(rename(ast)) ≅ compile(ast)
##   optimizer:   f(perturb(x)) ≈ f(x)  within ε
##
## `metamorphic(s, prop, transform, relation)` checks
## `relation(prop(x), prop(transform(x)))` for each generated `x`.
## `unchangedUnder` is the equality specialization;
## `metamorphics` takes a `seq` of transforms (all checked per example).
##
## Nested `forAll` from #91 makes the inner property runs compose
## cleanly without clobbering outer state.

import ./strategy, ./engine

proc metamorphic*[T, U](
    s: Strategy[T],
    prop: proc(t: T): U,
    transform: proc(t: T): T,
    relation: proc(a, b: U): bool,
    settings = defaultSettings()): Report[T] =
  ## Test: for each generated `x`, `relation(prop(x), prop(transform(x)))`
  ## must hold. Returns the standard `Report[T]` — `otFalsified` carries
  ## the input `x` that broke the relation.
  proc body(x: T) =
    let a = prop(x)
    let b = prop(transform(x))
    ensure relation(a, b)
  forAll(s, body, settings)

proc unchangedUnder*[T, U](
    s: Strategy[T],
    prop: proc(t: T): U,
    transform: proc(t: T): T,
    settings = defaultSettings()): Report[T] =
  ## Specialization where the relation is equality. Reads at the call
  ## site as "the prop's output is unchanged under this transform" —
  ## the common case (idempotence, normalization, permutation
  ## invariance, refactoring symmetry).
  metamorphic(s, prop, transform,
    proc(a, b: U): bool = a == b, settings)

proc metamorphics*[T, U](
    s: Strategy[T],
    prop: proc(t: T): U,
    transforms: openArray[proc(t: T): T {.closure.}],
    relation: proc(a, b: U): bool,
    settings = defaultSettings()): Report[T] =
  ## Multi-transform: for each generated `x`, every transform in
  ## `transforms` must produce a `prop` output that's related to
  ## `prop(x)`. Fan-out form for "this property holds under each of
  ## these transformations" — e.g. sort is invariant under both
  ## reversal and rotation.
  ##
  ## **Usage note.** Nim infers `{.noSideEffect, gcsafe.}` for proc
  ## literals, which fails to unify with the closure-typed element of
  ## the `openArray`. Declare each transform with an explicit closure
  ## type at the call site:
  ##
  ## ```nim
  ## let rev: proc(xs: seq[int]): seq[int] {.closure.} =
  ##   proc(xs: seq[int]): seq[int] = result = xs; result.reverse()
  ## ```
  let ts = @transforms   # capture by value so the closure outlives the call
  proc body(x: T) =
    let baseline = prop(x)
    for t in ts:
      let perturbed = prop(t(x))
      ensure relation(baseline, perturbed)
  forAll(s, body, settings)
