import std/[unittest, strutils]
import nelli
import zerofill  # RFC-0010 A1 pin; removed by A3

# `explain` phase: after a falsifying example is shrunk, mark each
# choice in the sequence as `nNecessary` (perturbing it makes the
# property pass — the bug depends on this value) or `nFree` (the
# failure persists regardless — the choice doesn't carry information
# about the bug). This is choice-sequence engines' superpower for
# debugging: we annotate the IR itself, not just print the value.

suite "explain: per-choice necessity":
  test "Report.necessity has one entry per choice on a falsification":
    let r = forAll(integers(0, 100),
                   proc(x: int) = (ensure x < 50),
                   zeroFilled(Settings(maxExamples: 200, seed: 1,
                                       flakyRetries: 0, maxShrinks: 200,
                                       maxRejections: 200)))
    check r.outcome == otFalsified
    check r.necessity.len == r.choices.len
    check r.necessity.len > 0

  test "the choice that the failure depends on is nNecessary; an unused choice is nFree":
    # x's choice causes the failure (x must be < 50; if it's 50+, fail).
    # y is drawn but the property doesn't read it → y is free.
    # Property is over a tuple (x, y) so both choices appear in the IR.
    let strat = map(integers(0, 100), integers(0, 100))
    let r = forAll(strat,
                   proc(xy: (int, int)) = (ensure xy[0] < 50),
                   zeroFilled(Settings(maxExamples: 200, seed: 4,
                                       flakyRetries: 0, maxShrinks: 200,
                                       maxRejections: 200)))
    check r.outcome == otFalsified
    # Find the choice corresponding to x (the larger integer; or just
    # the one with intVal >= 50 since y was minimized).
    var sawNecessary, sawFree = false
    for n in r.necessity:
      if n == nNecessary: sawNecessary = true
      if n == nFree: sawFree = true
    check sawNecessary
    check sawFree

suite "explain in repro()":
  test "repro() annotates each choice with [necessary] / [free]":
    let r = forAll(map(integers(0, 100), integers(0, 100)),
                   proc(xy: (int, int)) = (ensure xy[0] < 50),
                   zeroFilled(Settings(maxExamples: 200, seed: 5,
                                       flakyRetries: 0, maxShrinks: 200,
                                       maxRejections: 200)))
    check r.outcome == otFalsified
    let text = repro(r)
    check "necessary" in text
    check "free" in text

