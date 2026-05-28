## Fuzz integration — the bytes-as-DataSource entry point and (in a
## later issue) the coverage-guided runner.
##
## This module is the **partitioned-fuzz half** of proptest: it shares
## the choice-sequence IR, Strategy[T], DataSource, ExampleDatabase,
## and shrinker with the PBT runner, but lives behind its own entry
## points so a user who only wants property tests never touches the
## fuzz API. Per the M12 design discussion, the partitioning is the
## architecture that lets us combine PBT and structured fuzzing in
## one library without entangling them.
##
## The first capability here is `fuzzOnce(s, prop, bytes)`: run a
## strategy + property against an externally-supplied byte buffer.
## This is the integration point for libFuzzer / AFL / custom mutator
## harnesses — they hand us bytes, we hand them back a verdict.

import std/options
import ./strategy, ./datasource, ./engine

type
  FuzzOnceOutcome* = enum
    foOk,         ## strategy produced a value; property held
    foRejected,   ## the byte buffer was too short to satisfy the strategy
                  ## (or a `filter`/`assume` rejected the example); the
                  ## fuzzer should drop this input from its corpus
    foFalsified   ## the property raised `FalsifiedError`; the bytes
                  ## are a crash-reproducing input (libFuzzer keeps it)

  FuzzOnceResult*[T] = object
    outcome*: FuzzOnceOutcome
    value*: Option[T]
      ## `some(x)` iff the strategy produced a value before the property
      ## ran. `none` on `foRejected` when the strategy itself overran.
    message*: string
      ## On `foFalsified`, the `ensure` / raised exception's message;
      ## empty otherwise.

proc fuzzOnce*[T](s: Strategy[T], prop: proc(x: T),
                  bytes: seq[byte]): FuzzOnceResult[T] =
  ## Run `s` then `prop` against a byte buffer. Per the libFuzzer
  ## convention, any kind of "input was malformed" (insufficient bytes,
  ## strategy-side rejection) is the same outcome as a filter-rejected
  ## example — the fuzzer drops the input. A property failure is the
  ## interesting one and what the fuzzer corpus retains.
  var ds = newReplaySourceFromBytes(bytes)
  var x: T
  try:
    x = s.generate(ds)
  except Rejection, Overrun:
    return FuzzOnceResult[T](outcome: foRejected)
  result.value = some(x)
  try:
    prop(x)
    result.outcome = foOk
  except Rejection:
    result.outcome = foRejected
  except FalsifiedError as e:
    result.outcome = foFalsified
    result.message = e.msg
  except CatchableError as e:
    result.outcome = foFalsified
    result.message = $e.name & ": " & e.msg
  except Defect as e:
    result.outcome = foFalsified
    result.message = "crashed: " & $e.name & ": " & e.msg
