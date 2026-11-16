## nelli/smt/witness_render -- a symex witness rendered as a `seq[ChoiceNode]`.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. `symex.nim` re-exports
## `renderAsChoices`; the helpers stay private to this module.

import std/[tables, sets, algorithm]
import ../choice

# ---- Witness → ChoiceNode bridge -------------------------------------------
#
# A symex witness is a Nim tuple (the proc's parameter list). Phase 7
# linearises it into a `seq[ChoiceNode]` so the same regression-seed
# substrate nelli already uses for random examples can carry
# symex-derived counterexamples. The encoding is deterministic and
# length-prefixed for variable-cardinality container shapes.

const sxIntMin = low(int64)
const sxIntMax = high(int64)
const sxLenMax = high(int64)

proc sortedKeysOf[K, V](t: Table[K, V]): seq[K] =
  ## Returns `t`'s keys in deterministic ascending order. Used by
  ## `renderAsChoices` to defeat Nim's undefined hash-iteration
  ## order so identical witnesses produce identical choice
  ## sequences. Local helper to dodge z3's shadowing of
  ## `tables.keys` at the `renderAsChoices` call-site scope.
  for k, _ in t: result.add k
  sort(result)

proc sortedElemsOf[E](s: HashSet[E]): seq[E] =
  ## HashSet counterpart of `sortedKeysOf`.
  for e in s: result.add e
  sort(result)

proc renderInto[T](w: T; res: var seq[ChoiceNode]; cells: var seq[pointer]) =
  ## The body of `renderAsChoices`. `cells` lists the ref / ptr cells
  ## rendered so far, in rendering order (RFC-0005 S8n): the one piece of
  ## state a witness graph needs, since a cell reached twice (an alias, a
  ## cycle) renders as a back-reference the second time.
  when T is bool:
    res.add booleanChoice(w, 0.5)
  elif T is SomeFloat:
    # Phase 15 F7: a symex float witness rides as a single `floatChoice`.
    # The constraint window is fully permissive — `[-Inf, +Inf]`, `allowNan
    # = true`, `smallestNonzeroMagnitude = 0.0` — so any IEEE-754 bit pattern
    # (NaN, ±Inf, subnormals, ±0) passes `permits` and round-trips through the
    # choice IR / `floats` replay strategy. `floatVal` is a float64, so a
    # float32 witness widens losslessly on the way in and narrows back on read.
    res.add floatChoice(float64(w), -Inf, Inf, allowNan = true,
                           smallestNonzeroMagnitude = 0.0)
  elif T is SomeSignedInt:
    res.add integerChoice(int64(w), sxIntMin, sxIntMax, 0'i64)
  elif T is SomeUnsignedInt:
    # Symex's uint widths fit in int64 modulo width; cast for the
    # constraint window. Witness values are non-negative.
    res.add integerChoice(int64(w), 0'i64, sxIntMax, 0'i64)
  elif T is string:
    # Full Unicode minus the UTF-16 surrogate block — `intervals`
    # rejects any range intersecting `[surrogateLo, surrogateHi]`.
    res.add stringChoice(w,
      intervals(@[(0'i32, surrogateLo - 1),
                   (surrogateHi + 1, maxCodepoint)]),
      0, w.len)
  elif T is array:
    for e in w:
      renderInto(e, res, cells)
  elif T is seq:
    # Continue-boolean protocol matching `lists`/`tables`/`sets`
    # strategies (strategy.nim:406-475): each element preceded by
    # `drawBoolean(0.9)` = true, list terminated by a final false.
    # The old length-prefix encoding was incompatible with replay
    # through these strategies; renderAsChoicesVersion bumps "1"
    # → "2" to invalidate stale collection witnesses in the DB.
    for e in w:
      res.add booleanChoice(true, 0.9)
      renderInto(e, res, cells)
    res.add booleanChoice(false, 0.9)
  elif T is HashSet:
    # Sort by element before iterating: Nim's HashSet iteration
    # order is undefined, and the cache key is content-addressed on
    # the choice sequence — same logical witness must round-trip to
    # identical choices across runs.
    for e in sortedElemsOf(w):
      res.add booleanChoice(true, 0.9)
      renderInto(e, res, cells)
    res.add booleanChoice(false, 0.9)
  elif T is Table:
    # Sort by key for the same determinism reason.
    for k in sortedKeysOf(w):
      res.add booleanChoice(true, 0.9)
      renderInto(k, res, cells)
      renderInto(w[k], res, cells)
    res.add booleanChoice(false, 0.9)
  elif T is ref or T is ptr:
    # RFC-0005 S8n: a ref / ptr witness is one integer tag, then its pointee:
    # 0 = nil; 1 = a cell not rendered before, followed by the pointee's
    # choices; k + 2 = the k-th cell already rendered (an alias or a cycle),
    # with nothing after it. The bounds are [0, 1 + cells rendered so far],
    # so a tree-shaped witness is all 0 / 1 tags. Before S8n a ref had no
    # arm: a SUT with a ref param could not reach `assertCoveredBy` or a
    # `symex` phase at all (the `{.error.}` below, at compile time). Keeping
    # identity makes the encoding total over cyclic witnesses and tells an
    # aliased pair from two equal cells.
    let hi = int64(cells.len + 1)
    if w == nil:
      res.add integerChoice(0'i64, 0'i64, hi, 0'i64)
    else:
      let cell = cast[pointer](w)
      let seen = cells.find(cell)
      if seen >= 0:
        res.add integerChoice(int64(seen + 2), 0'i64, hi, 0'i64)
      else:
        res.add integerChoice(1'i64, 0'i64, hi, 0'i64)
        cells.add cell
        renderInto(w[], res, cells)
  elif T is tuple:
    for f in fields(w):
      renderInto(f, res, cells)
  elif T is enum:
    # Phase 11 cycle 8 — enums (and variant discriminators) ride as
    # integer choices keyed on ordinal value. shrinkTowards points
    # at low(T) so the shrinker collapses to the first enum
    # constant by convention.
    res.add integerChoice(int64(ord(w)),
                              int64(ord(low(T))), int64(ord(high(T))),
                              int64(ord(low(T))))
  elif T is object:
    # For variant objects, Nim's `fields(w)` iterates the
    # discriminator plus only the *active arm's* fields — inactive
    # arms are skipped. Result: positional order is [discriminator,
    # active-arm field 1, active-arm field 2, …], which matches
    # Phase 11 cycle 8's contract.
    for f in fields(w):
      renderInto(f, res, cells)
  else:
    {.error: "renderAsChoices: unsupported witness shape".}

proc renderAsChoices*[T](w: T): seq[ChoiceNode] =
  var cells: seq[pointer]
  renderInto(w, result, cells)
