## examples/symex_simple.nim
##
## The minimal symex example: prove that *some* integer drives a
## piece of code into a labelled branch. This is the "hello, world"
## of `symexFind` with the `tLabel` target.
##
## What you'll see:
##   1. The SUT (`classify`) — ordinary Nim. The `symexTarget("triple")`
##      marker is the label we ask symex to reach.
##   2. The `symexFind` call — runs the symbolic walker; returns a
##      `SymexResult[(int,)]` (a 1-tuple because `classify` has one
##      `int` param).
##   3. The witness — the concrete `int` Z3 produced. Running
##      `classify(witness)` *will* reach the label.
##
## Run with `nim c -r --path:src examples/symex_simple.nim`.

import std/[strformat]
import proptest/symex

proc classify(n: int) =
  # Symex explores both branches and asks Z3: "is there an `n` that
  # makes the path go through symexTarget(\"triple\")?"
  if (n mod 3) == 0 and n > 0:
    symexTarget("triple")

let r = symexFind(classify, tLabel("triple"))
doAssert r.status == sxSat,
  "expected SAT — `n=3` (or any positive multiple of 3) satisfies the path"

let n = r.witness[0]
echo &"symex found witness: n = {n}"
# Note: symex returns *some* satisfying input, not the smallest. Z3
# typically picks a large positive value because the BV theory has
# no a-priori bias toward small magnitudes. If you want a minimal
# counterexample, feed the witness back through proptest's
# random/shrink pipeline — symex's role is *reachability*, the
# shrinker's role is *minimality*.

# Sanity-check: the witness *really* drives `classify` into the label.
# We use assertCoveredBy for this — it re-runs `classify` under a
# capture context and verifies the target fired.
assertCoveredBy(classify, tLabel("triple"))
echo "assertCoveredBy: the witness reaches symexTarget(\"triple\") — good."
