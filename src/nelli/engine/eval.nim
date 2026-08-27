## Eval primitive — replay-and-check.
##
## `evalReplay` runs a strategy over a recorded choice sequence and
## checks the property, classifying the outcome as `ekPassed`,
## `ekFalsified` (with the value or `none` when the strategy itself
## raised before assigning), or `ekRejected`. The shrinker and every
## phase that needs to "try this candidate input" calls into here.
##
## Also hosts the user-facing `assume` / `ensure` / `assumeOk` /
## `assumeSome` templates — they belong with the eval primitive
## because they're the in-property side of the rejection /
## falsification handshake `evalReplay` decodes.

import std/[options, tables]
import ../strategy, ../datasource, ../choice, ../optbox, ../crashinfo
import ./types, ./frame

type
  EvalKind* = enum ekPassed, ekFalsified, ekRejected

  Eval*[T] = object
    case kind*: EvalKind
    of ekPassed:
      # No value field: the passing value is never consumed (only `scores`
      # feed the Pareto front), and a by-value `T` here would force
      # `default(T)` when an `Eval` of a *different* kind is constructed —
      # invalid for a `{.requiresInit.}` element type. See `optbox`.
      scores*: ScoreMap
      choices*: seq[ChoiceNode]
    of ekFalsified:
      fValue*: Opt[T]
        ## `box(x)` when `prop(x)` raised after `x` was assigned;
        ## empty when the strategy itself raised before assigning.
      fChoices*: seq[ChoiceNode]
      fMsg*: string
      fNotes*: seq[(string, string)]
      fCrash*: Option[CrashInfo]
        ## RFC-fuzzer-nextgen U0: set (`kind: ckException`) only when this
        ## falsification came from a caught `Defect` — the same in-process
        ## crash-isolation boundary `fuzz`'s `Worker`/`inProcessTarget` uses
        ## (`observeInProcess`'s except chain). `none` for a `FalsifiedError`
        ## (`ensure`) or an ordinary `CatchableError` falsification — those
        ## aren't crashes, and their shape is unchanged by U0.
    of ekRejected: discard

# --- in-property assertion templates -----------------------------------------

template assume*(cond: untyped) =
  ## Discard the current example unless `cond` holds (raises `Rejection`,
  ## which the runner counts against the rejection budget). Prefer
  ## constraining the strategy over heavy `assume`.
  if not cond:
    raise newException(Rejection, "assumption failed: " & astToStr(cond))

template ensure*(cond: untyped) =
  ## Assert a property; raises `FalsifiedError` (which the engine catches).
  if not cond:
    raise newException(FalsifiedError, "ensure failed: " & astToStr(cond))

template assumeOk*(expr: untyped): auto =
  ## `let r = expr; assume r.isOk; r.get` in one expression. Duck-typed
  ## on `.isOk: bool` + `.get`.
  let r = expr
  assume r.isOk
  r.get

template assumeSome*(expr: untyped): auto =
  ## `Option[T]` form of `assumeOk`.
  let o = expr
  assume o.isSome
  o.get

# --- evalReplay --------------------------------------------------------------

proc evalReplay*[T](s: Strategy[T], prop: proc(x: T),
                    candidate: seq[ChoiceNode]): Eval[T] =
  ## Replay a candidate through the strategy and check the property.
  ## Returns the verdict; per-example state (`scores`, `notes`) is
  ## cleared on the current frame before each call.
  var ds = newReplaySource(candidate)
  currentFrame().scores.clear(); currentFrame().notes.setLen(0)
  # Bind the generated value with a `try`-expression rather than a
  # pre-declared `var x: T`: the latter default-constructs `T`, which is
  # invalid for `{.requiresInit.}` element types. (See
  # REQUIRESINIT_DSL_FRICTION.md.)
  let x =
    try:
      s.generate(ds)
    except Rejection, Overrun:
      return Eval[T](kind: ekRejected)
    except FalsifiedError as e:
      return Eval[T](kind: ekFalsified, fValue: empty[T](), fChoices: ds.recorded,
                     fNotes: currentFrame().notes,
                     fMsg: "strategy raised: " & e.msg)
    except CatchableError as e:
      return Eval[T](kind: ekFalsified, fValue: empty[T](), fChoices: ds.recorded,
                     fNotes: currentFrame().notes,
                     fMsg: "strategy raised: " & $e.name & ": " & e.msg)
    except Defect as e:
      let crash = classifyDefect(e, "strategy crashed")
      return Eval[T](kind: ekFalsified, fValue: empty[T](), fChoices: ds.recorded,
                     fNotes: currentFrame().notes, fMsg: crash.message,
                     fCrash: some(crash))
  try:
    prop(x)
    Eval[T](kind: ekPassed, scores: currentFrame().scores,
            choices: ds.recorded)
  except Rejection:
    Eval[T](kind: ekRejected)
  except FalsifiedError as e:
    Eval[T](kind: ekFalsified, fValue: box(x), fChoices: ds.recorded,
            fNotes: currentFrame().notes, fMsg: e.msg)
  except CatchableError as e:
    Eval[T](kind: ekFalsified, fValue: box(x), fChoices: ds.recorded,
            fNotes: currentFrame().notes,
            fMsg: $e.name & ": " & e.msg)
  except Defect as e:
    # RFC-fuzzer-nextgen U0: the property-invocation crash-isolation
    # boundary — the SAME classification `fuzz.nim`'s `observeInProcess`
    # applies at its own `prop(x)` call (via the shared `classifyDefect`,
    # R30), so a Defect here becomes a normal falsification (shrinkable,
    # reported with typed `CrashInfo`) instead of escaping. `except Defect`
    # is already reachable at ordinary (panics off) builds; under
    # `--panics:on`, per `engine.nim`'s standing warning, a Defect is
    # fatal/uncatchable by Nim's own design and no in-process boundary can
    # change that.
    let crash = classifyDefect(e)
    Eval[T](kind: ekFalsified, fValue: box(x), fChoices: ds.recorded,
            fNotes: currentFrame().notes, fMsg: crash.message,
            fCrash: some(crash))
