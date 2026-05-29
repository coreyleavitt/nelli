import std/unittest
import proptest

# #114 — Daikon-style property mining.
#
# A trace recorder runs a strategy through a function-under-test,
# capturing (input, output) pairs. A miner evaluates each candidate
# invariant template against every trace and reports survivors: the
# templates that held across all observed examples — the "likely
# invariants" Daikon surfaces for human review.

suite "collectTraces — input/output recorder":
  test "runs the strategy n times and records (input, output) pairs":
    proc sq(x: int): int = x * x
    let traces = collectTraces(integers(0, 100), sq, n = 50, seed = 1)
    check traces.len == 50
    for t in traces:
      check t.input * t.input == t.output

suite "mineInvariants — survivor/failure split":
  test "template that always holds is reported with full support":
    # Property to mine: output >= 0 — true for squares of any int.
    proc sq(x: int): int = x * x
    let traces = collectTraces(integers(-100, 100), sq, n = 200, seed = 7)
    let nonNeg = Template[int, int](
      name: "output >= 0",
      holds: proc(t: Trace[int, int]): bool = t.output >= 0)
    let survivors = mineInvariants(traces, @[nonNeg])
    check survivors.len == 1
    check survivors[0].name == "output >= 0"
    check survivors[0].support == 200

  test "template that fails on any trace is suppressed":
    # `output == input` only holds at fixed points x=0 and x=1.
    # Over a wide range, almost every trace breaks it; miner should
    # not report it.
    proc sq(x: int): int = x * x
    let traces = collectTraces(integers(2, 100), sq, n = 50, seed = 11)
    let isIdentity = Template[int, int](
      name: "output == input",
      holds: proc(t: Trace[int, int]): bool = t.output == t.input)
    let survivors = mineInvariants(traces, @[isIdentity])
    check survivors.len == 0

suite "built-in numeric templates":
  test "abs: discovers output >= 0":
    proc absInt(x: int): int = abs(x)
    let traces = collectTraces(integers(-100, 100), absInt, n = 200, seed = 1)
    let survivors = mineInvariants(traces, defaultNumericTemplates[int]())
    var sawNonNeg = false
    for s in survivors:
      if s.name == "output >= 0": sawNonNeg = true
    check sawNonNeg

  test "identity: discovers output == input":
    proc id(x: int): int = x
    let traces = collectTraces(integers(-100, 100), id, n = 100, seed = 2)
    let survivors = mineInvariants(traces, defaultNumericTemplates[int]())
    var sawIdentity = false
    for s in survivors:
      if s.name == "output == input": sawIdentity = true
    check sawIdentity

  test "max(x, 5): discovers output >= input and output >= 0":
    proc clampLow(x: int): int = max(x, 5)
    let traces = collectTraces(integers(-100, 100), clampLow, n = 200, seed = 3)
    let survivors = mineInvariants(traces, defaultNumericTemplates[int]())
    var sawGE = false
    var sawNonNeg = false
    for s in survivors:
      if s.name == "output >= input": sawGE = true
      if s.name == "output >= 0":     sawNonNeg = true
    check sawGE
    check sawNonNeg

  test "negate: identity does NOT survive":
    proc neg(x: int): int = -x
    let traces = collectTraces(integers(1, 100), neg, n = 50, seed = 4)
    let survivors = mineInvariants(traces, defaultNumericTemplates[int]())
    for s in survivors:
      check s.name != "output == input"
      check s.name != "output >= input"   # also wrong: -x < x for x > 0

suite "end-to-end: custom + default template composition":
  test "abs on signed range discovers all of {>=0, >=input on positive only}":
    # On the full signed range, abs surfaces output>=0 (universal). It
    # does NOT surface output==input because abs(-3) != -3. A custom
    # template specifically checking "output == abs(input) algebraically"
    # is what the user would add after reviewing the defaults.
    proc absInt(x: int): int = abs(x)
    let traces = collectTraces(integers(-1000, 1000), absInt, n = 300, seed = 5)
    let customAbs = Template[int, int](
      name: "output == |input|",
      holds: proc(t: Trace[int, int]): bool =
        let m = if t.input < 0: -t.input else: t.input
        t.output == m)
    let allTempls = defaultNumericTemplates[int]() & @[customAbs]
    let survivors = mineInvariants(traces, allTempls)
    var sawCustom = false
    var sawNonNeg = false
    for s in survivors:
      if s.name == "output == |input|": sawCustom = true
      if s.name == "output >= 0":       sawNonNeg = true
    check sawCustom
    check sawNonNeg

  test "mining over divisible inputs surfaces 'output mod 2 == 0' for double":
    proc dbl(x: int): int = x * 2
    let traces = collectTraces(integers(0, 1000), dbl, n = 100, seed = 6)
    let survivors = mineInvariants(traces, defaultNumericTemplates[int]())
    var sawEven = false
    for s in survivors:
      if s.name == "output mod 2 == 0": sawEven = true
    check sawEven
