# Tutorial — symex from first principles

A 30-minute walkthrough. By the end you'll know what symex computes,
how it computes it, why the answers are sound, and how to use it
inside nelli.

## §1. The question

> *Is there an input that makes this code take this branch?*

That's it. Every other capability — assertion-violation hunting,
out-of-bounds finding, test-adequacy verification — is a
specialisation of that one question.

A random PBT engine answers the question *statistically*: throw
enough inputs at the code and we'll probably hit the branch. Symex
answers it *deterministically* by reasoning about the input space
algebraically. Where random succeeds, symex confirms; where random
fails because the branch is reached only at one specific value out
of `2^64`, symex finds it in one solver call.

This is not a replacement for random PBT. It's a complement:

| Random PBT | Symex |
|---|---|
| Good at finding inputs that violate a property *somewhere* in a wide region. | Good at proving a *specific* point is reachable or not. |
| Discovers properties you didn't think to assert (via shrinking + display). | Verifies coverage claims you've explicitly made. |
| Cheap per example. | Expensive per query, but answers a stronger question. |

nelli's Phase 7 wires them together via `assertCoveredBy`: the
random run does the bulk of the testing; symex provides per-target
adequacy proof.

## §2. The model — path-frontier execution

Imagine running the program on a symbolic input rather than a
concrete one. Every branch becomes a fork in the execution: the
"true" side proceeds with `cond ∧ pc_before` as its path condition;
the "false" side with `¬cond ∧ pc_before`. The walker maintains a
*frontier* of surviving paths, each one a snapshot of:

- the current environment (variable bindings, each as a Z3 term),
- the path condition so far (a conjunction of Z3 formulas),
- a flag marking whether the path has touched anything we admitted
  ignorance about (`uncertain`).

When a path reaches a target:

- Under `tLabel("name")` — when control flow walks past
  `symexTarget("name")`, the path condition is sent to Z3 with
  "find a satisfying assignment". If Z3 says SAT, the assignment is
  the witness.
- Under `tAssertionViolation()` — at every `symexAssert(cond)`, the
  walker forks: the *violating* branch (with `¬cond` in the pc) is
  the one we want to satisfy.
- Under `tIndexError()` — at every `arr[i]` access, the walker
  forks: the OOB branch (`i < 0 ∨ i ≥ N`) is solved.

If no surviving path can be made satisfiable, the answer is
`sxUnsat` — the target is unreachable. If all paths that *might*
reach the target are marked uncertain (e.g. because we ran out of
loop-unwind budget), the answer is `sxUnknown`.

This is the standard model from Cadar & Sen's
[*Symbolic execution for software testing*](https://dl.acm.org/doi/10.1145/2408776.2408795)
(CACM 2013) — KLEE, SAGE, and Pex all build on it. nelli's
specific implementation choices come from this lineage plus some
deliberate restrictions for staying in the type-safe Nim regime.

## §3. The integer floor — BV[W] with selective abstraction

Programs do arithmetic. The walker has to model that arithmetic in
a way that matches Nim's runtime *exactly*, or the witnesses will
be unsound (Z3 says yes; the real program disagrees).

Nim's integers wrap modulo `2^W` for fixed widths. So does Z3's
bit-vector theory. We make `int8`, `int16`, `int32`, `int64`, and
their unsigned counterparts all map to `BV[W]`. That gives bit-
exact semantics — overflow, two's complement, shift-by-width, all
modelled correctly.

Pure bit-vector reasoning is sometimes slow, though. Integer
intervals like `[0, 10000]` (from `Natural`, `range[0..10000]`, or
a `0 ≤ x ≤ 10000` assertion) compose much faster in Z3's integer
theory than in BV. ADR-0001 codifies the trade-off:

| Mode | Default? | Witness soundness |
|---|---|---|
| `isExact` | no | BV[W] everywhere. Bit-perfect. Slower. |
| `isOptimised` | **yes** | BV[W] floor + Z3Int when the value provably stays inside its BV window. Bit-perfect by construction. |
| `isLoose` | no | Z3Int everywhere; ignores overflow. Research-only; emits a stderr banner. |

The `isOptimised` mode (the default) tracks, for every value, an
abstract interval; it promotes to `Z3Int` only when the interval
fits in the value's BV window. Soundness is proved structurally:
arithmetic stays within window → no overflow → BV[W] and Z3Int
agree. See [abstraction-internals.md](abstraction-internals.md)
for the full obligation set with worked examples.

## §4. The three target kinds in action

### §4.1 `tLabel` — explicit coverage points

```nim
proc classify(n: int) =
  if (n mod 3) == 0 and n > 0:
    symexTarget("triple")

let r = symexFind(classify, tLabel("triple"))
# r.status = sxSat
# r.witness[0] is some positive multiple of 3
```

This is the workhorse target. Annotate the branches you care about
and prove they're reachable.

Full example: [examples/symex_simple.nim](../../examples/symex_simple.nim).

### §4.2 `tAssertionViolation` — invariant hunting

```nim
proc mustBeNonneg(x: int) =
  symexAssert(x >= 0)

let r = symexFind(mustBeNonneg, tAssertionViolation())
# r.status = sxSat
# r.witness[0] is some negative integer
```

The walker forks at every `symexAssert(cond)`: the violating branch
gets `¬cond` added to the pc, and the solver finds a falsifying
input. This is the symex analogue of `forAll` + `check` — proves
a counterexample *exists* in one call.

### §4.3 `tIndexError` — memory-safety witnesses

```nim
proc readSlot(arr: array[10, int], i: int) =
  let v = arr[i]
  discard v

let r = symexFind(readSlot, tIndexError())
# r.status = sxSat
# r.witness[1] is < 0 or >= 10
```

Full example: [examples/symex_oob.nim](../../examples/symex_oob.nim).

## §5. `assertCoveredBy` — the verifier role

The Phase 7 CI primitive. Given a SUT, a target, and a test
function the user claims exercises the target, prove it:

```nim
proc handle(req: int) =
  if req == 0:           symexTarget("zero")
  elif req mod 13 == 0:  symexTarget("magic-13")
  else:                  discard

proc thoroughTest(req: int) =
  handle(req)  # exercises every reachable branch on the witness

assertCoveredBy(handle, tLabel("zero"),     thoroughTest)
assertCoveredBy(handle, tLabel("magic-13"), thoroughTest)
```

If `thoroughTest` is missing a case, `assertCoveredBy` raises
`AssertionDefect` with a message identifying the uncovered target.
The multi-target form `assertCoveredBy(fn, [tLabel("a"), tLabel("b")])`
aggregates failures into one report.

Full example: [examples/symex_assert_covered.nim](../../examples/symex_assert_covered.nim).

## §6. Loops and the unwind budget

Symex's bounded-model-checking model k-unwinds each loop:

```nim
proc loopShort(x: int) =
  var i = 0
  while i < x:
    i = i + 1
  if i == 3:
    symexTarget("hit-3")  # reachable in ≤ 5 iterations
```

`maxLoopUnwind` (default 5) caps the unrolling. Paths surviving k
iterations are marked uncertain. If a path needs more iterations
than the budget allows, the final status is `sxUnknown` — *not*
`sxUnsat`. Symex is honest about not knowing.

Three honest moves when you hit UNKNOWN:

1. Bump `maxLoopUnwind` in `SymexSettings`.
2. Accept UNKNOWN as covered via `acceptUnknownAsCovered = true` —
   right for code you don't want to verify symbolically.
3. Refactor the SUT so the relevant target is reachable within
   budget (often the correct CS answer).

Full example: [examples/symex_loops.nim](../../examples/symex_loops.nim).

## §7. Containers — symex finds the data structure

When a path condition mentions `t.hasKey("alice")` and `t["alice"] > 100`,
Z3's array theory models the table as two functions (`data: K → V`,
`present: K → Bool`) and finds a model:

```nim
proc score(t: Table[string, int]) =
  if t.hasKey("alice") and t["alice"] > 100:
    symexTarget("hi-alice")

let r = symexFind(score, tLabel("hi-alice"))
# r.witness[0] is some Table satisfying both constraints
```

Same story for `seq[T]` (length + Z3 array data) and
`HashSet[T]/set[T]` (membership + cardinality).

Full example: [examples/symex_table.nim](../../examples/symex_table.nim).

## §8. Extending — `{.symexOpaque.}`

For user procs the walker shouldn't enter — FFI, IO, hardware
reads — annotate with the pragma:

```nim
proc readSensor(channel: int): int {.symexOpaque.} =
  ...  # walker never enters this body

proc dispatch(channel: int) =
  let v = readSensor(channel)
  if v > 1000:
    symexTarget("alarm")
```

Calls to `readSensor` become fresh symbolic returns; the surviving
path is marked uncertain. The example
[symex_stdlib_model.nim](../../examples/symex_stdlib_model.nim)
walks through why this is the right model.

## §9. Where to go next

- The full reference: [README.md](README.md)
- Internals (proof obligations, interval arithmetic): [abstraction-internals.md](abstraction-internals.md)
- Extending the stdlib registry: [extending-stdlib.md](extending-stdlib.md)
- Z3-version determinism: [determinism.md](determinism.md)
- ADRs — [ADR-0001](ADR-0001-integer-semantics.md), [ADR-0002](ADR-0002-dsl-factoring.md)

For the live build plan and per-phase commit list see
[../SYMEX_PLAN.md](../SYMEX_PLAN.md).

## References

- C. Cadar, K. Sen. *Symbolic execution for software testing*. CACM 2013.
- C. Cadar, D. Dunbar, D. Engler. *KLEE: Unassisted and Automatic Generation of High-Coverage Tests for Complex Systems Programs*. OSDI 2008.
- P. Godefroid, M. Levin, D. Molnar. *Automated Whitebox Fuzz Testing*. NDSS 2008.
- N. Tillmann, J. de Halleux. *Pex — White Box Test Generation for .NET*. TAP 2008.
