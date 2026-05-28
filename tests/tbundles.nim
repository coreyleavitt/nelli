import std/[unittest, strutils, sequtils, sets]
import proptest

# Stateful Bundles: a named typed pool that lives inside `S` (user-owned
# storage). A rule with `consumes = b` is auto-disabled when the bundle is
# empty and receives a sampled-from-pool argument when not. That makes
# "open file → read file" patterns trivial: the file-handle pool is just
# a `seq` field in S, and the `read` rule consumes from it.

type FileState = object
  handles: seq[int]      # the bundle pool — plain field on S
  closed: HashSet[int]

suite "Bundle: auto-precondition (empty pool disables the rule)":
  test "a consumes-rule never fires while its bundle is empty":
    # No `open` rule → bundle stays empty → `close` rule must be skipped.
    # The state machine has only `close` (consumes from handles); given
    # an empty initial state, no rule is eligible → the strategy
    # terminates immediately without invoking `close`.
    let bHandles = bundle[FileState, int](
      "handles", proc(s: FileState): seq[int] = s.handles)
    let sm = StateMachine[FileState](
      initial: just(FileState()),
      rules: @[
        rule[FileState, int]("close", consumes = bHandles,
          proc(s: var FileState, h: int) =
            # Should never execute — empty bundle should gate this rule.
            doAssert false, "close fired with empty bundle!"),
      ])
    let r = forAll(stateful(sm, maxSteps = 10),
                   proc(s: FileState) = (ensure s.handles.len == 0),
                   Settings(maxExamples: 30, seed: 1,
                            flakyRetries: 0, maxShrinks: 20,
                            maxRejections: 100))
    check r.outcome == otPassed

suite "Bundle: integration — file-handle machine":
  test "buggy close (re-closes handles) is caught and shrunk":
    # The bug: `close` removes the handle from `handles` but a buggy
    # variant doesn't, allowing the same handle to be drawn again →
    # double-close on the next consume → invariant fires.
    let bHandles = bundle[FileState, int](
      "handles", proc(s: FileState): seq[int] = s.handles)
    var nextId = 0
    let sm = StateMachine[FileState](
      initial: just(FileState()),
      rules: @[
        # open: append a fresh handle to the pool.
        rule[FileState, int]("open", just(0),
          proc(s: var FileState, _: int) =
            inc nextId
            s.handles.add nextId),
        # buggy close: consumes a handle index, marks closed — but
        # forgets to remove from `s.handles` → handle remains
        # consumable → next draw can pick the same closed handle.
        rule[FileState, int]("close", consumes = bHandles,
          proc(s: var FileState, h: int) =
            doAssert h notin s.closed,
              "double-close on handle " & $h
            s.closed.incl h),
      ])
    let r = forAll(stateful(sm, maxSteps = 8),
                   proc(s: FileState) = (ensure true),
                   Settings(maxExamples: 100, seed: 3,
                            flakyRetries: 0, maxShrinks: 200,
                            maxRejections: 200))
    check r.outcome == otFalsified
    check "double-close" in r.message
