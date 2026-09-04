import std/unittest
import std/algorithm  # for reversed
import nelli

suite "DSL: property":
  property "increment is monotone":
    given x in integers(0, 100)
    ensure x + 1 > x

  property "reverse-reverse is identity on lists":
    given xs in lists(integers(0, 9), maxLen = 8)
    ensure xs.reversed.reversed == xs

  property "addition commutes":
    given a in integers(-50, 50), b in integers(-50, 50)
    ensure a + b == b + a

  property "list concat preserves total length":
    given xs in lists(integers(0, 9), maxLen = 6),
          ys in lists(integers(0, 9), maxLen = 6)
    ensure (xs & ys).len == xs.len + ys.len

  property "integer addition is associative":
    given a in integers(-50, 50), b in integers(-50, 50), c in integers(-50, 50)
    ensure (a + b) + c == a + (b + c)

  property "four-arg property (mixed types) runs":
    given a in integers(-10, 10),
          b in integers(-10, 10),
          flag in booleans(),
          xs in lists(integers(0, 9), maxLen = 4)
    ensure (a + b == b + a) and (flag or not flag) and (xs.len <= 4)

suite "DSL: settings clause":
  test "property accepts a custom Settings via `with` clause":
    # Without a Settings clause, the DSL silently defaults — DB integration
    # (`testId`/`dbPath`), explicit seed, etc. are unreachable from the
    # DSL. The `with` form makes them first-class. Use a side-effect
    # counter to confirm the custom Settings actually controls the run.
    var ranCount = 0
    property "honors custom maxExamples":
      with Settings(maxExamples: 12, maxRejections: 1000, seed: 99,
                    flakyRetries: 0, maxShrinks: 50,
                    useSA: false, targetedSAIters: 0)
      given x in integers(0, 100)
      discard x
      inc ranCount
      ensure true
    check ranCount == 12

# RFC-0010 round D (D1). `given x in int` — a typedesc on the right-hand side
# of a binding means "whatever `arbitrary(int)` derives".
#
# The seed proposed `given x: int`. That is NOT mechanical: the colon produces
# `nnkCommand(given, nnkExprColonExpr(...))`, a different AST shape from the
# `nnkInfix(in, ...)` the parse loop requires, and `given x: int, y in ys` does
# not parse as intended at all because the colon swallows the remainder.
# Keeping the single `in` shape preserves mixed bindings for free.
suite "property DSL — typedesc bindings":

  test "a typedesc binding derives its strategy":
    var seen = 0
    property "int binding":
      with Settings(maxExamples: 15, seed: 4)
      given x in int
      inc seen
      ensure x == x
    check seen == 15

  test "typedesc and strategy bindings mix in one `given`":
    var seen = 0
    property "mixed bindings":
      with Settings(maxExamples: 12, seed: 5)
      given a in int, b in integers(0, 10), c in bool
      inc seen
      ensure b >= 0 and a == a and c == c
    check seen == 12

  test "a derived object type works as a binding":
    type Point = object
      x, y: int
    var seen = 0
    property "object binding":
      with Settings(maxExamples: 8, seed: 6)
      given p in Point
      inc seen
      ensure p.x == p.x
    check seen == 8
