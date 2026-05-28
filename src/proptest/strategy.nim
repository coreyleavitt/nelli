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

import std/[enumutils, macros, tables, sets, options]
import ./datasource, ./int128, ./choice

type
  Strategy*[T] = object
    run*: proc(src: var DataSource): T {.closure.}
    display*: proc(t: T): string {.closure.}
      ## Optional custom counterexample renderer. `nil` means fall back to
      ## the default `$t` at report time. Type-indexed on `T`, which is
      ## why type-changing combinators (`map`, `flatMap`) drop it — there's
      ## no general way to lift a `T → string` through a `T → U`. Attach a
      ## fresh one downstream via `displayWith`, or use `mapWithDisplay`.

  Rejection* = object of CatchableError
    ## Raised by `filter`/`assume` to discard an example. The engine catches it,
    ## doesn't count the example, and (within a budget) generates another.

proc newStrategy*[T](run: proc(src: var DataSource): T): Strategy[T] =
  ## Build a strategy from a raw generation closure (the escape hatch for custom
  ## strategies; prefer the combinators below).
  Strategy[T](run: run)

proc displayWith*[T](s: Strategy[T],
                     f: proc(t: T): string {.closure.}): Strategy[T] =
  ## Return a copy of `s` carrying `f` as its counterexample renderer.
  ## On falsification, `forAll` invokes `f` on the shrunk value and stores
  ## the resulting string in `Report.displayed`; `repro()` and the DSL
  ## checkpoint prefer that string over the default `$value`.
  result = s
  result.display = f

proc generate*[T](s: Strategy[T], src: var DataSource): T =
  ## Produce one value, drawing (and thereby recording) from `src`.
  s.run(src)

proc valueType*[T](s: Strategy[T]): T = default(T)
  ## Phantom used by the `property` DSL to extract `T` from a strategy via
  ## `typeof(valueType(strat))`. Never actually called at runtime — only its
  ## type matters.

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

proc sampledFromWhere*[T](items: openArray[T],
                          pred: proc(t: T): bool): Strategy[T] =
  ## Eager-filter variant of `sampledFrom`: pre-computes the subset of
  ## `items` for which `pred(item)` holds and draws uniformly from that.
  ## Construction-time filtering means the rejection budget isn't touched
  ## at draw time — strictly better than `sampledFrom(items).filter(pred)`
  ## for finite corpora. Raises `ValueError` at construction if no items
  ## match (a strategy that always rejects would burn the budget at
  ## runtime; failing loud is honest).
  var filtered: seq[T]
  for x in items:
    if pred(x): filtered.add x
  if filtered.len == 0:
    raise newException(ValueError,
      "sampledFromWhere: no items satisfy the predicate")
  sampledFrom(filtered)

proc oneOf*[T](strategies: openArray[Strategy[T]]): Strategy[T] =
  ## Pick one of `strategies` and generate from it.
  ##
  ## Implements **swarm testing**: each branch is independently muted with
  ## ~20% probability per call (with at least one branch always enabled). The
  ## mute mask is recorded as `N` boolean choice nodes *before* the index
  ## draw — so replay is fully deterministic, and the shrinker gets free
  ## "mute more branches" as another reduction pass (a minimal counterexample
  ## may use only the branches strictly required to expose the bug).
  let ss = @strategies
  # All branches share `T`, so the first non-nil display is a sensible
  # inherited renderer for the union. Users wanting a different policy
  # can `.displayWith(...)` the resulting strategy.
  var inheritedDisplay: proc(t: T): string {.closure.}
  for s in ss:
    if s.display != nil:
      inheritedDisplay = s.display
      break
  Strategy[T](run: proc(src: var DataSource): T =
    var enabled: seq[int]
    for i in 0 ..< ss.len:
      if src.drawBoolean(0.8): enabled.add i
    if enabled.len == 0:
      enabled.add 0  # safety: never all-muted
    let pick = toInt64(src.drawInteger(toInt128(0), toInt128(enabled.high),
                                       toInt128(0)))
    ss[enabled[int(pick)]].run(src),
    display: inheritedDisplay)

proc map*[T, U](s: Strategy[T], f: proc(x: T): U): Strategy[U] =
  ## Transform generated values with `f`. Shrinking is preserved automatically:
  ## `f` runs after the draw, so the recorded choices are unchanged and the
  ## shrinker minimizes them exactly as for `s`. Any `displayWith` on `s` is
  ## *dropped* because there is no general way to lift a `T → string` through
  ## a `T → U`; attach a fresh renderer downstream, or use `mapWithDisplay`.
  Strategy[U](run: proc(src: var DataSource): U = f(s.run(src)))

proc mapWithDisplay*[T, U](s: Strategy[T], f: proc(x: T): U,
                           display: proc(y: U): string {.closure.}): Strategy[U] =
  ## `s.map(f)` plus a `U`-renderer in one call. Syntactic sugar — equivalent
  ## to `s.map(f).displayWith(display)`. Common for derived types whose
  ## default `$` is unreadable (`arbitrary(MyDoc).mapWithDisplay(toDoc, encode)`).
  result = map(s, f)
  result.display = display

proc filter*[T](s: Strategy[T], pred: proc(x: T): bool): Strategy[T] =
  ## Keep only values satisfying `pred`; reject the example otherwise. Prefer
  ## constructive generation over heavy filtering — a strict predicate burns the
  ## engine's rejection budget. Shrinking is preserved (the predicate is just
  ## re-checked on each regenerated candidate). The display proc (if any) is
  ## preserved — `T` is unchanged, so any `displayWith` attached upstream
  ## still renders the filtered value correctly.
  Strategy[T](run: proc(src: var DataSource): T =
    result = s.run(src)
    if not pred(result):
      raise newException(Rejection, "filtered example rejected"),
    display: s.display)

proc recursive*[T](base: Strategy[T],
                   extend: proc(child: Strategy[T]): Strategy[T],
                   maxDepth = 4): Strategy[T] =
  ## Build a bounded-depth recursive strategy: `base` is the non-recursive
  ## escape, `extend(child)` is a strategy that may use `child` for the
  ## recursive position. The result allows up to `maxDepth` nested `extend`
  ## applications — at the innermost level, recursive sub-positions fall back
  ## to `base`, so a generated value can be at most `maxDepth` deep.
  ##
  ## Used for hand-written recursive strategies (trees, linked lists, ASTs).
  ## Note: `arbitrary(T)` auto-synthesizes a `recursive(...)` wrapper for
  ## directly-recursive types (variants with a non-recursive branch, ref-
  ## object self-fields, `seq[Self]` / `HashSet[Self]` / `Table[_, Self]` /
  ## `Option[Self]` fields), so reach for this combinator manually only when
  ## the auto-derivation path errors (mutually-recursive types, self-
  ## references nested deeper than one wrapper).
  result = base
  for _ in 0 ..< maxDepth:
    result = extend(result)

proc enums*[E: enum](): Strategy[E] =
  ## Uniformly pick an enum value. Handles hole-y enums correctly: we enumerate
  ## the *declared* values (via `enumutils.items`) and sample by index, so we
  ## never emit an undeclared ordinal regardless of how the enum's values are
  ## laid out.
  var values: seq[E]
  for e in E.items: values.add e
  sampledFrom(values)

proc tuples2*[A, B](sa: Strategy[A], sb: Strategy[B]): Strategy[(A, B)] =
  ## Cartesian product of two strategies (the explicit 2-arg form, kept for
  ## clarity / direct use). For more than two strategies — and for type
  ## inference of arbitrary arity — use the `tuples` macro below.
  Strategy[(A, B)](run: proc(src: var DataSource): (A, B) =
    let a = sa.run(src)
    let b = sb.run(src)
    (a, b))

macro tuples*(args: varargs[untyped]): untyped =
  ## A heterogeneous tuple strategy of arbitrary arity: draws each component
  ## in sequence and returns a positional tuple `(v_0, …, v_{N-1})`. Tuple
  ## element types are derived from the supplied strategies via
  ## `typeof(valueType(s_i))`, so callers don't have to spell out the tuple
  ## type. Both draws live in the same choice sequence, so shrinking is
  ## uniform across components.
  if args.len == 0:
    error("tuples: at least one strategy required", args)
  let srcSym = genSym(nskParam, "src")
  var tupleType = newNimNode(nnkTupleConstr)
  var procBody = newStmtList()
  var vSyms: seq[NimNode]
  for i in 0 ..< args.len:
    let s = args[i]
    tupleType.add newCall(bindSym"typeof", newCall(bindSym"valueType", s))
    let vSym = genSym(nskLet, "v" & $i)
    vSyms.add vSym
    procBody.add newLetStmt(vSym,
                            newCall(newDotExpr(s, ident"run"), srcSym))
  var tupleConstr = newNimNode(nnkTupleConstr)
  for v in vSyms: tupleConstr.add v
  procBody.add tupleConstr
  let innerProc = newProc(
    params = @[tupleType,
               newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
    body = procBody,
    procType = nnkLambda)
  result = newCall(bindSym"newStrategy", innerProc)

proc flatMap*[T, U](s: Strategy[T], f: proc(x: T): Strategy[U]): Strategy[U] =
  ## Dependent generation: draw a `T`, then draw a `U` from the strategy `f`
  ## chooses. Both draw from the same source in sequence, so the shrinker can
  ## reduce the left and right draws in any order — the monadic-bind case the
  ## choice-sequence model handles cleanly (where integrated rose trees fail).
  ## Any `displayWith` on `s` is dropped (the output strategy is dynamic in
  ## `t`, so even forwarding `f(t).display` would be inconsistent across
  ## draws); use `flatMapWithDisplay` to attach a fresh `U`-renderer.
  Strategy[U](run: proc(src: var DataSource): U =
    let t = s.run(src)
    f(t).run(src))

proc flatMapWithDisplay*[T, U](s: Strategy[T], f: proc(x: T): Strategy[U],
                               display: proc(y: U): string {.closure.}):
                               Strategy[U] =
  ## `s.flatMap(f)` plus a `U`-renderer. Sugar for
  ## `s.flatMap(f).displayWith(display)`.
  result = flatMap(s, f)
  result.display = display

proc integers*(lo, hi: int,
               weights: openArray[(int, float)] = []): Strategy[int] =
  ## Integers in `[lo, hi]`, shrinking toward 0. The default distribution mixes
  ## uniform random with boundary injection and small-magnitude bias (handled
  ## inside `drawInteger`). Optional `weights = @[(v, p), …]` give specific
  ## values an extra `p` probability of being drawn (cumulative — the sum of
  ## probabilities is the chance any weighted value is picked; the remainder
  ## falls through to the biased uniform path). A forced-weighted draw still
  ## records the original constraints so the shrinker can move off it.
  let ws = @weights
  Strategy[int](run: proc(src: var DataSource): int =
    if not src.isReplaying and ws.len > 0:
      var total = 0.0
      for w in ws: total += w[1]
      let roll = src.nextRoll
      if roll < total:
        var cum = 0.0
        for w in ws:
          cum += w[1]
          if roll < cum:
            return toInt64(src.drawInteger(toInt128(lo), toInt128(hi),
                                           toInt128(0),
                                           some(toInt128(w[0])))).int
    toInt64(src.drawInteger(toInt128(lo), toInt128(hi), toInt128(0))).int)

const
  labelListElement* = 1
    ## Opaque span label for one iteration of a `lists` draw.
  labelTableEntry* = 3
    ## Opaque span label for one entry of a `tables` draw.
  labelSetEntry* = 4
    ## Opaque span label for one entry of a `sets` draw.

proc lists*[T](elem: Strategy[T], minLen = 0, maxLen = 100): Strategy[seq[T]] =
  ## A sequence of `elem` with length in `[minLen, maxLen]`. Generated *element
  ## at a time*: a continue-boolean precedes each element (forced true below
  ## minLen, forced false at maxLen). Each iteration is wrapped in a span — so
  ## the shrinker can drop one element with one structure-respecting deletion.
  Strategy[seq[T]](run: proc(src: var DataSource): seq[T] =
    result = @[]
    while true:
      src.startSpan(labelListElement)
      let p = if result.len < minLen: 1.0
              elif result.len >= maxLen: 0.0
              else: 0.9
      let cont = src.drawBoolean(p)
      if not cont:
        src.endSpan()
        break
      result.add elem.run(src)
      src.endSpan())

proc booleans*(): Strategy[bool] =
  ## Uniform booleans.
  Strategy[bool](run: proc(src: var DataSource): bool = src.drawBoolean(0.5))

proc tables*[K, V](keyStrat: Strategy[K], valStrat: Strategy[V],
                   minSize = 0, maxSize = 16): Strategy[Table[K, V]] =
  ## A `Table[K, V]` strategy: generated entry-at-a-time with a per-entry
  ## continue-bool, just like `lists`. Iterations are bounded by `minSize..
  ## maxSize`; colliding keys dedup naturally via Table semantics, so the
  ## resulting `Table.len` may be ≤ the iteration count.
  Strategy[Table[K, V]](run: proc(src: var DataSource): Table[K, V] =
    result = initTable[K, V]()
    var iter = 0
    while true:
      src.startSpan(labelTableEntry)
      let p = if iter < minSize: 1.0
              elif iter >= maxSize: 0.0
              else: 0.9
      if not src.drawBoolean(p):
        src.endSpan()
        break
      let k = keyStrat.run(src)
      let v = valStrat.run(src)
      result[k] = v
      src.endSpan()
      inc iter)

proc sets*[T](elemStrat: Strategy[T],
              minSize = 0, maxSize = 16): Strategy[HashSet[T]] =
  ## A `HashSet[T]` strategy: generated element-at-a-time with per-element
  ## continue-bool. Colliding elements dedup naturally; result size may be
  ## ≤ iteration count.
  Strategy[HashSet[T]](run: proc(src: var DataSource): HashSet[T] =
    result = initHashSet[T]()
    var iter = 0
    while true:
      src.startSpan(labelSetEntry)
      let p = if iter < minSize: 1.0
              elif iter >= maxSize: 0.0
              else: 0.9
      if not src.drawBoolean(p):
        src.endSpan()
        break
      result.incl(elemStrat.run(src))
      src.endSpan()
      inc iter)

proc bitsets*[T: Ordinal](): Strategy[set[T]] =
  ## A strategy for Nim's built-in `set[T]` bitset: draws an include-boolean
  ## per element of `low(T)..high(T)`, recording each as a choice node so the
  ## shrinker can mute included elements toward the empty set.
  Strategy[set[T]](run: proc(src: var DataSource): set[T] =
    for v in low(T) .. high(T):
      if src.drawBoolean(0.5):
        result.incl v)

proc arrays*[N: static int, T](elem: Strategy[T]): Strategy[array[N, T]] =
  ## A fixed-size `array[N, T]`. Length is static, so there is no continue-bool
  ## per element — we just draw `N` values. The shrinker can still lower each
  ## element via per-kind passes; length isn't shrinkable because the type
  ## dictates it.
  Strategy[array[N, T]](run: proc(src: var DataSource): array[N, T] =
    for i in 0 ..< N:
      result[i] = elem.run(src))

proc strings*(minLen = 0, maxLen = 100): Strategy[string] =
  ## Strings of printable ASCII (codepoints 0x20–0x7E), with length in
  ## codepoints in `[minLen, maxLen]`. The most common case — for arbitrary
  ## Unicode ranges, pass an `IntervalSet` (see the overload below).
  let iv = intervals([(0x20'i32, 0x7e'i32)])
  Strategy[string](run: proc(src: var DataSource): string =
    src.drawString(iv, minLen, maxLen))

proc strings*(intervalSet: IntervalSet,
              minLen = 0, maxLen = 100): Strategy[string] =
  ## Strings whose every codepoint lies in `intervalSet`. Pair with the
  ## `intervals(...)` constructor for arbitrary Unicode ranges
  ## (surrogates rejected at construction time so produced strings are
  ## always well-formed UTF-8). Length in codepoints, in `[minLen, maxLen]`.
  Strategy[string](run: proc(src: var DataSource): string =
    src.drawString(intervalSet, minLen, maxLen))

proc floats*(min = NegInf, max = Inf, allowNan = true): Strategy[float] =
  ## Floats over `[min, max]`. Defaults span the whole real line and include
  ## NaN/±Inf (the values that break code); pass `allowNan = false` / finite
  ## bounds for tamer floats.
  Strategy[float](run: proc(src: var DataSource): float =
    src.drawFloat(min, max, allowNan, 0.0))
