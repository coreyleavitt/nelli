import std/[unittest, unicode]
import nelli
import nelli/[rng, datasource]

# The variadic applicative `map` — the single combinator for combining >=2
# strategies. `map(s1, .., sN)` draws each component in order from one source
# and returns the positional tuple; `map(s1, .., sN, f)` applies the trailing
# function to the drawn values (no intermediate tuple). It subsumes the old
# `tuples`/`tuples2` and the `tuples(..).map(unpack)` idiom nim-z3 had to write.
# The unary `map(s, f)` functor overload must keep resolving to its proc.

suite "applicative map: tuple form (no function)":
  test "map(s1, s2, s3) draws a flat (A, B, C), each from its own strategy":
    let s = map(integers(1, 5), strings(1, 3), booleans())
    var ds = newDataSource(initSplitMix64(11))
    for _ in 0 ..< 80:
      let v = s.generate(ds)
      check v[0] in 1 .. 5
      check v[1].runeLen in 1 .. 3
      discard v[2]  # bool — always valid

  test "map(s1, s2) is the 2-tuple form (replaces tuples2)":
    let s = map(integers(0, 9), booleans())
    var ds = newDataSource(initSplitMix64(3))
    for _ in 0 ..< 50:
      let v = s.generate(ds)
      check v[0] in 0 .. 9
      discard v[1]

suite "applicative map: apply form (trailing function)":
  test "map(s1, s2, s3, f) applies f to build a domain object (the nim-z3 case)":
    type Ternary = object
      lo, mid, hi: int
    let s = map(integers(0, 9), integers(10, 19), integers(20, 29),
                proc(a, b, c: int): Ternary = Ternary(lo: a, mid: b, hi: c))
    var ds = newDataSource(initSplitMix64(7))
    for _ in 0 ..< 80:
      let v = s.generate(ds)
      check v.lo in 0 .. 9
      check v.mid in 10 .. 19
      check v.hi in 20 .. 29

  test "trailing do-block form reads as a constructor":
    type P = object
      n: int
      flag: bool
    let s = map(integers(0, 4), booleans()) do (n: int, flag: bool) -> P:
      P(n: n, flag: flag)
    var ds = newDataSource(initSplitMix64(99))
    for _ in 0 ..< 40:
      let v = s.generate(ds)
      check v.n in 0 .. 4
      discard v.flag

suite "applicative map: shrinking and DSL":
  test "a falsifying property shrinks uniformly across all three components":
    # Fails iff every component >= 1; all three share one choice sequence, so
    # the minimal counterexample is (1, 1, 1) — shrinking reaches every slot.
    proc prop(t: (int, int, int)) =
      ensure not (t[0] >= 1 and t[1] >= 1 and t[2] >= 1)
    let r = forAll(
      map(integers(0, 100), integers(0, 100), integers(0, 100)), prop)
    check r.outcome == otFalsified
    check r.counterexample.get == (1, 1, 1)

  property "tuple form binds through the given DSL":
    given t in map(integers(0, 9), booleans(), strings(0, 4))
    ensure t[0] in 0 .. 9 and (t[1] or not t[1]) and t[2].len <= 4

  property "apply form binds through the given DSL":
    given n in map(integers(0, 9), integers(0, 9), proc(a, b: int): int = a + b)
    ensure n in 0 .. 18

suite "applicative map: unary functor overload is preserved":
  test "map(s, f) still resolves to the functor proc":
    let s = integers(0, 9).map(proc(x: int): string = $x)
    var ds = newDataSource(initSplitMix64(5))
    for _ in 0 ..< 30:
      let v = s.generate(ds)
      check v.len >= 1
