## Strategy[T] — a recipe for producing a `T` by drawing from a DataSource.
##
## A strategy is *only* a generator: it draws primitives from the source, which
## records them. There is no separate shrinker — shrinking happens by minimizing
## the recorded choice sequence and re-running the strategy. That is why every
## combinator (`map`, `filter`, `flatMap`, …) preserves shrinking for free: they
## just transform the value or re-run the generator over the same source.
##
## It is a value `object` wrapping a closure, so combinators capture their inputs
## and compose; the closure environment allocates once per strategy construction,
## not per draw — build strategies outside the test loop.

import ./datasource, ./int128

type
  Strategy*[T] = object
    run*: proc(src: var DataSource): T {.closure.}

  Rejection* = object of CatchableError
    ## Raised by `filter`/`assume` to discard an example. The engine catches it,
    ## doesn't count the example, and (within a budget) generates another.

proc newStrategy*[T](run: proc(src: var DataSource): T): Strategy[T] =
  ## Build a strategy from a raw generation closure (the escape hatch for custom
  ## strategies; prefer the combinators below).
  Strategy[T](run: run)

proc generate*[T](s: Strategy[T], src: var DataSource): T =
  ## Produce one value, drawing (and thereby recording) from `src`.
  s.run(src)

proc just*[T](value: T): Strategy[T] =
  ## The constant strategy: always `value`, consuming no choices.
  Strategy[T](run: proc(src: var DataSource): T = value)

proc sampledFrom*[T](items: openArray[T]): Strategy[T] =
  ## Uniformly pick one of `items`. Records the index, so it shrinks toward the
  ## first element.
  let xs = @items
  Strategy[T](run: proc(src: var DataSource): T =
    let i = toInt64(src.drawInteger(toInt128(0), toInt128(xs.high), toInt128(0)))
    xs[int(i)])

proc oneOf*[T](strategies: openArray[Strategy[T]]): Strategy[T] =
  ## Uniformly pick one of `strategies` and generate from it. Records the index
  ## first, so it shrinks toward the first strategy.
  let ss = @strategies
  Strategy[T](run: proc(src: var DataSource): T =
    let i = toInt64(src.drawInteger(toInt128(0), toInt128(ss.high), toInt128(0)))
    ss[int(i)].run(src))

proc map*[T, U](s: Strategy[T], f: proc(x: T): U): Strategy[U] =
  ## Transform generated values with `f`. Shrinking is preserved automatically:
  ## `f` runs after the draw, so the recorded choices are unchanged and the
  ## shrinker minimizes them exactly as for `s`.
  Strategy[U](run: proc(src: var DataSource): U = f(s.run(src)))

proc filter*[T](s: Strategy[T], pred: proc(x: T): bool): Strategy[T] =
  ## Keep only values satisfying `pred`; reject the example otherwise. Prefer
  ## constructive generation over heavy filtering — a strict predicate burns the
  ## engine's rejection budget. Shrinking is preserved (the predicate is just
  ## re-checked on each regenerated candidate).
  Strategy[T](run: proc(src: var DataSource): T =
    result = s.run(src)
    if not pred(result):
      raise newException(Rejection, "filtered example rejected"))

proc flatMap*[T, U](s: Strategy[T], f: proc(x: T): Strategy[U]): Strategy[U] =
  ## Dependent generation: draw a `T`, then draw a `U` from the strategy `f`
  ## chooses. Both draw from the same source in sequence, so the shrinker can
  ## reduce the left and right draws in any order — the monadic-bind case the
  ## choice-sequence model handles cleanly (where integrated rose trees fail).
  Strategy[U](run: proc(src: var DataSource): U =
    let t = s.run(src)
    f(t).run(src))

proc integers*(lo, hi: int): Strategy[int] =
  ## Integers uniformly in `[lo, hi]`, shrinking toward 0 (clamped into range).
  Strategy[int](run: proc(src: var DataSource): int =
    toInt64(src.drawInteger(toInt128(lo), toInt128(hi), toInt128(0))).int)
