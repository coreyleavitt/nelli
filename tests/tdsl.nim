import std/unittest
import std/algorithm  # for reversed
import proptest

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
