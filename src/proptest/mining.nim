## Daikon-style property mining (#114).
##
## **The dual of writing properties manually.** A user supplies a
## strategy for inputs, a function under test, and a template library
## of candidate invariants. We run the function across many traces and
## report the templates that *always* held — the "likely invariants"
## the human reviews to accept or reject as real properties.
##
## **v1 scope.** Templates are typed `Template[I, O]` records the user
## composes; the miner enumerates surviving templates ranked by
## support (raw "how many traces survived" — v1 always has full
## support since we filter to all-holds). Real Daikon goes further:
## **constant inference** (templates with auto-determined `c` in
## `output > c`), **implication discovery** (if-then templates with
## splitter inference), and **statistical confidence**. Those are
## genuinely useful extensions; defer until a concrete consumer needs
## them.

import std/options
import ./strategy, ./datasource, ./rng

type
  Trace*[I, O] = object
    ## One recorded function call.
    input*: I
    output*: O

  Template*[I, O] = object
    ## A candidate invariant. `holds` returns true iff the trace
    ## satisfies the template; surviving templates are those for which
    ## `holds` returned true on *every* recorded trace.
    name*: string
    holds*: proc(t: Trace[I, O]): bool {.closure.}

  MinedInvariant*[I, O] = object
    ## A surviving template. `support` is the trace count it held over.
    name*: string
    support*: int

proc collectTraces*[I, O](inputs: Strategy[I],
                          fn: proc(x: I): O,
                          n: int,
                          seed: uint64 = 0): seq[Trace[I, O]] =
  ## Draw `n` inputs from `inputs`, run `fn` on each, return the
  ## `(input, output)` pairs. Deterministic in `seed`. Traces are
  ## generated independently — the corpus is the substrate the miner
  ## evaluates templates against.
  result = newSeqOfCap[Trace[I, O]](n)
  var rng = initSplitMix64(if seed == 0: 0xDA1C0'u64 else: seed)
  for _ in 0 ..< n:
    var ds = newDataSource(initSplitMix64(rng.next))
    let inp = inputs.run(ds)
    let outp = fn(inp)
    result.add Trace[I, O](input: inp, output: outp)

proc mineInvariants*[I, O](traces: seq[Trace[I, O]],
                           templates: openArray[Template[I, O]]
                          ): seq[MinedInvariant[I, O]] =
  ## Evaluate each template against every trace. Report the templates
  ## that held universally — those are the "likely invariants" the
  ## user reviews. Empty trace seq returns every template (no
  ## counterexample → all templates survive vacuously); document this
  ## as the natural identity.
  for t in templates:
    var allHold = true
    for tr in traces:
      if not t.holds(tr):
        allHold = false
        break
    if allHold:
      result.add MinedInvariant[I, O](name: t.name, support: traces.len)

# --- built-in numeric template library --------------------------------------
#
# Eight starter templates spanning equality, sign, ordering, and parity.
# Daikon's full template library is much larger (constant inference, mod-N
# parity, sum invariants, linear inequalities, etc.); these eight catch
# the most common cases users care about and demonstrate the architecture.
# Adding more templates is mechanical: define a typed Template and append
# to the suite.

proc templOutputEqInput*[T](): Template[T, T] =
  Template[T, T](name: "output == input",
                 holds: proc(t: Trace[T, T]): bool = t.output == t.input)

proc templOutputEqZero*[T: SomeNumber](): Template[T, T] =
  Template[T, T](name: "output == 0",
                 holds: proc(t: Trace[T, T]): bool = t.output == T(0))

proc templOutputGE0*[T: SomeNumber](): Template[T, T] =
  Template[T, T](name: "output >= 0",
                 holds: proc(t: Trace[T, T]): bool = t.output >= T(0))

proc templOutputGT0*[T: SomeNumber](): Template[T, T] =
  Template[T, T](name: "output > 0",
                 holds: proc(t: Trace[T, T]): bool = t.output > T(0))

proc templOutputLE0*[T: SomeNumber](): Template[T, T] =
  Template[T, T](name: "output <= 0",
                 holds: proc(t: Trace[T, T]): bool = t.output <= T(0))

proc templOutputGEInput*[T: SomeNumber](): Template[T, T] =
  Template[T, T](name: "output >= input",
                 holds: proc(t: Trace[T, T]): bool = t.output >= t.input)

proc templOutputLEInput*[T: SomeNumber](): Template[T, T] =
  Template[T, T](name: "output <= input",
                 holds: proc(t: Trace[T, T]): bool = t.output <= t.input)

proc templOutputEven*[T: SomeInteger](): Template[T, T] =
  Template[T, T](name: "output mod 2 == 0",
                 holds: proc(t: Trace[T, T]): bool = (t.output mod T(2)) == T(0))

proc defaultNumericTemplates*[T: SomeNumber](): seq[Template[T, T]] =
  ## The eight built-in numeric templates. Composable: users typically
  ## start from this list and append domain-specific templates.
  result = @[
    templOutputEqInput[T](),
    templOutputEqZero[T](),
    templOutputGE0[T](),
    templOutputGT0[T](),
    templOutputLE0[T](),
    templOutputGEInput[T](),
    templOutputLEInput[T]()]
  when T is SomeInteger:
    result.add templOutputEven[T]()
