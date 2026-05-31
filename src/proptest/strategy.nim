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

import std/[enumutils, macros, tables, sets, options, unicode, algorithm]
import ./datasource, ./int128, ./choice, ./autolabel

# #108 — strategy distribution auto-labels.
#
# Every built-in combinator emits one `autoLabel(...)` per draw,
# describing what it produced. The labels live in the reserved `auto.`
# namespace (see `autolabel.autoLabelPrefix`) so they can't collide with
# manual `event()` calls. The runtime sink is nil unless the engine
# installs one (i.e. unless `Settings.autoLabels = true`); calls are
# zero-cost when the sink is off.

proc labelLen(family: string, n, minLen, maxLen: int): string =
  ## Bucket a container length into a precedence-ordered size category.
  ## Family is the strategy class ("list-len", "string-len", "table-size",
  ## "set-size", "array-len"); kept generic so all containers share one
  ## bucketing policy.
  ##
  ## Precedence (highest first): empty (n==0) > max (n==maxLen) >
  ## near-max (n ≥ minLen + 3*(maxLen-minLen)/4 but < maxLen) >
  ## small (n ≤ minLen + (maxLen-minLen)/4) > medium.
  if n == 0: return "auto." & family & ":empty"
  if n >= maxLen: return "auto." & family & ":max"
  let span = maxLen - minLen
  if n >= minLen + (3 * span) div 4: return "auto." & family & ":near-max"
  if n <= minLen + span div 4: return "auto." & family & ":small"
  "auto." & family & ":medium"

proc labelFloat(v: float): string =
  ## Float distribution bucket. NaN must be checked first (it doesn't
  ## compare equal to anything); ±Inf collapse to a single "inf"
  ## category since both arise from overflow. "subnormal" catches
  ## denormal nonzero values — bugs at the subnormal-flush threshold
  ## are surprisingly common in numeric code.
  if v != v: return "auto.float:nan"
  if v == 0.0: return "auto.float:zero"
  if v == Inf or v == NegInf: return "auto.float:inf"
  # IEEE 754 binary64 subnormal threshold is 2^-1022 ≈ 2.225e-308.
  const subnormalMag = 2.2250738585072014e-308
  if abs(v) < subnormalMag: return "auto.float:subnormal"
  "auto.float:other"

proc labelInt(v, lo, hi, shrinkTowards: int): string =
  ## Bucket an integer draw into a precedence-ordered category.
  ## Precedence (highest first): zero > shrinkTowards > near-lo >
  ## near-hi > other. `near` = within `max(10, width/100)` of the bound.
  ##
  ## Width is computed in uint64 so `integers(low(int), high(int))` —
  ## whose `hi - lo` overflows signed — still gives a well-defined
  ## bucket. The `near-lo` / `near-hi` predicates use uint64 distance
  ## from the bound, sidestepping signed overflow on `v - lo` / `hi - v`.
  if v == 0: return "auto.int:zero"
  if v == shrinkTowards: return "auto.int:shrinkTowards"
  let widthU = uint64(hi) - uint64(lo)                # wrap-safe
  var deltaU = widthU div 100'u64
  if deltaU < 10'u64: deltaU = 10'u64
  let nearLoU = uint64(v) - uint64(lo)
  let nearHiU = uint64(hi) - uint64(v)
  if nearLoU <= deltaU: return "auto.int:near-lo"
  if nearHiU <= deltaU: return "auto.int:near-hi"
  "auto.int:other"

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

proc valueType*[T](s: Strategy[T]): T =
  ## Compile-time phantom used by the `property`/`given` DSL to recover a
  ## strategy's element type via `typeof(valueType(strat))`. Only the
  ## *type* of the call is ever observed — the body never executes.
  ##
  ## The body must therefore satisfy the return type `T` *without constructing a
  ## `T`*: a `default(T)` body is invalid for `{.requiresInit.}` element types
  ## (object variants, value types that must be fully initialized), which would
  ## otherwise make such a strategy unbindable through the DSL purely because of
  ## how `T` is recovered. A `raise`-terminated body type-checks for every `T`
  ## and constructs nothing, so requiresInit types bind cleanly. (See
  ## REQUIRESINIT_DSL_FRICTION.md.)
  raise newException(Defect,
    "proptest.valueType is a compile-time phantom; it must never be called")

proc just*[T](value: T): Strategy[T] =
  ## The constant strategy: always `value`, consuming no choices.
  Strategy[T](run: proc(src: var DataSource): T = value)

proc sampledFrom*[T](items: openArray[T]): Strategy[T] =
  ## Uniformly pick one of `items`. Records the index, so it shrinks toward the
  ## first element.
  let xs = @items
  Strategy[T](run: proc(src: var DataSource): T =
    let i = toInt64(src.drawInteger(toInt128(0), toInt128(xs.high), toInt128(0)))
    autoLabel("auto.sampledFrom:idx-" & $i)
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
    let chosen = enabled[int(pick)]
    autoLabel("auto.oneOf:branch-" & $chosen)
    ss[chosen].run(src),
    display: inheritedDisplay)

proc frequency*[T](weighted: openArray[(int, Strategy[T])]): Strategy[T] =
  ## Weighted `oneOf`: pick branch `i` with probability `wᵢ / Σw` and generate
  ## from it. The realized distribution is proportional to the integer weights.
  ##
  ## Unlike `oneOf`, `frequency` makes a distributional promise and keeps it: the
  ## selector is drawn **unbiased** (so the boundary/small-window injection that
  ## `drawInteger` applies to *value* draws doesn't skew the branch frequencies)
  ## and it does **no swarm muting** (which would renormalize the weights away).
  ## Shrinking still heads toward the **first listed** branch, so put the
  ## simplest / base-case alternative first.
  ##
  ## A weight of `0` registers a branch that is never drawn (excluded entirely).
  ## A negative weight, an empty list, or an all-zero list raises `ValueError` at
  ## construction.
  var branches: seq[Strategy[T]]
  var cum: seq[int]
  var total = 0
  for (w, s) in weighted:
    if w < 0:
      raise newException(ValueError,
        "frequency: weight must be non-negative, got " & $w)
    if w == 0: continue   # registered but disabled
    total += w
    branches.add s
    cum.add total
  if branches.len == 0:
    raise newException(ValueError,
      "frequency: at least one branch must have a positive weight")
  let bs = branches
  let cumBounds = cum
  let tot = total
  Strategy[T](run: proc(src: var DataSource): T =
    # Unbiased selector: the realized branch distribution must reflect the
    # weights, not `drawInteger`'s value-edge-case bias. `shrinkTowards 0`
    # keeps shrinking pointed at the first branch.
    let r = toInt64(src.drawInteger(toInt128(0), toInt128(tot - 1), toInt128(0),
                                    biased = false))
    # `cumBounds` is the ascending prefix-sum of the weights, so the chosen
    # branch is the first bucket whose upper bound exceeds `r` — an O(log n)
    # `upperBound` rather than a linear walk. `r ∈ [0, tot-1] < cumBounds[^1]`,
    # so the result is always a valid branch index.
    let idx = upperBound(cumBounds, r.int)
    autoLabel("auto.frequency:branch-" & $idx)
    bs[idx].run(src))

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

proc isStrategyArg(n: NimNode): bool =
  ## True iff the typed expression `n` has type `Strategy[_]`. Used by the
  ## variadic `map` to partition leading component strategies from an optional
  ## trailing combining function.
  let t = n.getTypeInst
  (t.kind == nnkBracketExpr and t[0].eqIdent("Strategy")) or t.eqIdent("Strategy")

macro map*[A, B](s1: Strategy[A], s2: Strategy[B],
                 rest: varargs[typed]): untyped =
  ## Applicative product of two or more strategies — the N-ary generalization
  ## of the unary `map` (functor) above. Draws each component **in declaration
  ## order from one `DataSource`** (so shrinking is uniform across the whole
  ## product) and then either returns the drawn values as a positional tuple or,
  ## when the final argument is a combining function, applies it:
  ##
  ## ```nim
  ##   map(sa, sb)               # -> Strategy[(A, B)]
  ##   map(sa, sb, sc)           # -> Strategy[(A, B, C)]
  ##   map(sa, sb, sc, f)        # -> Strategy[R]   where f: (A, B, C) -> R
  ##   map(sa, sb, sc) do (a: A, b: B, c: C) -> R: ...   # trailing-block form
  ## ```
  ##
  ## The no-function form replaces the old `tuples`/`tuples2`; the function form
  ## replaces `tuples(…).map(unpack)`, with no intermediate tuple. Nothing is
  ## default-constructed, so `{.requiresInit.}` component types are fine. The
  ## unary `map(s, f)` still resolves to the functor `proc` above; this overload
  ## engages only with two or more leading strategies.
  var comps = @[s1, s2]
  for r in rest: comps.add r
  var nStrats = 0
  for a in comps:
    if isStrategyArg(a): inc nStrats else: break
  let hasFn = nStrats == comps.len - 1
  if not hasFn and nStrats != comps.len:
    error("map: expected component strategies optionally followed by a " &
          "single combining function (got a non-strategy in component " &
          "position)", comps[nStrats])

  let srcSym = genSym(nskParam, "src")
  var body = newStmtList()
  var vSyms: seq[NimNode]
  for i in 0 ..< nStrats:
    let v = genSym(nskLet, "v" & $i)
    vSyms.add v
    body.add newLetStmt(v, newCall(newDotExpr(comps[i], ident"run"), srcSym))

  var resultExpr: NimNode
  if hasFn:
    resultExpr = newCall(comps[^1])     # f(v0, v1, …, v{n-1})
    for v in vSyms: resultExpr.add v
  else:
    resultExpr = newNimNode(nnkTupleConstr)  # (v0, v1, …, v{n-1})
    for v in vSyms: resultExpr.add v
  body.add resultExpr

  # `auto` return: `newStrategy[T]` infers the element type from the lambda's
  # body (the tuple, or f's result), so requiresInit element types never get
  # default-constructed by a declared `var`/tuple type.
  let lam = newProc(
    params = @[ident"auto",
               newIdentDefs(srcSym, newTree(nnkVarTy, ident"DataSource"))],
    body = body, procType = nnkLambda)
  result = newCall(bindSym"newStrategy", lam)

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
            result = toInt64(src.drawInteger(toInt128(lo), toInt128(hi),
                                             toInt128(0),
                                             some(toInt128(w[0])))).int
            autoLabel(labelInt(result, lo, hi, 0))
            return
    result = toInt64(src.drawInteger(toInt128(lo), toInt128(hi), toInt128(0))).int
    autoLabel(labelInt(result, lo, hi, 0)))

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
      src.endSpan()
    autoLabel(labelLen("list-len", result.len, minLen, maxLen)))

proc booleans*(): Strategy[bool] =
  ## Uniform booleans.
  Strategy[bool](run: proc(src: var DataSource): bool =
    result = src.drawBoolean(0.5)
    autoLabel(if result: "auto.bool:true" else: "auto.bool:false"))

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
      inc iter
    autoLabel(labelLen("table-size", iter, minSize, maxSize)))

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
      inc iter
    autoLabel(labelLen("set-size", iter, minSize, maxSize)))

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
      result[i] = elem.run(src)
    # Arrays have a static length, so the bucket is constant across draws.
    # We still emit it so `autoLabels` users see arrays in their histogram
    # (matching every other container family).
    autoLabel(labelLen("array-len", N, N, N)))

proc strings*(minLen = 0, maxLen = 100): Strategy[string] =
  ## Strings of printable ASCII (codepoints 0x20–0x7E), with length in
  ## codepoints in `[minLen, maxLen]`. The most common case — for arbitrary
  ## Unicode ranges, pass an `IntervalSet` (see the overload below).
  let iv = intervals([(0x20'i32, 0x7e'i32)])
  Strategy[string](run: proc(src: var DataSource): string =
    result = src.drawString(iv, minLen, maxLen)
    autoLabel(labelLen("string-len", result.runeLen, minLen, maxLen)))

proc strings*(intervalSet: IntervalSet,
              minLen = 0, maxLen = 100): Strategy[string] =
  ## Strings whose every codepoint lies in `intervalSet`. Pair with the
  ## `intervals(...)` constructor for arbitrary Unicode ranges
  ## (surrogates rejected at construction time so produced strings are
  ## always well-formed UTF-8). Length in codepoints, in `[minLen, maxLen]`.
  Strategy[string](run: proc(src: var DataSource): string =
    result = src.drawString(intervalSet, minLen, maxLen)
    autoLabel(labelLen("string-len", result.runeLen, minLen, maxLen)))

proc floats*(min = NegInf, max = Inf, allowNan = true): Strategy[float] =
  ## Floats over `[min, max]`. Defaults span the whole real line and include
  ## NaN/±Inf (the values that break code); pass `allowNan = false` / finite
  ## bounds for tamer floats.
  Strategy[float](run: proc(src: var DataSource): float =
    result = src.drawFloat(min, max, allowNan, 0.0)
    autoLabel(labelFloat(result)))
