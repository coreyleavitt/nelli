import std/[unittest, options, locks, atomics, os]
import nelli
import nelli/[datasource, rng]

# parallelCheck: the convenience layer over isLinearisable. Generates
# a parallel plan (sequential prefix + N parallel suffixes), runs each
# suffix on its own thread with barrier synchronization + jitter
# injection, builds a history, and checks linearisability. Repetitions
# re-run the same plan to surface scheduler-dependent races.

# A trivial counter SUT for the round-trip tests.
type
  Counter = object
    count: int
    lock: Lock

  CounterState = object
    count: int

proc newSafeCounter(): ptr Counter =
  result = cast[ptr Counter](allocShared0(sizeof(Counter)))
  initLock(result[].lock)

proc safeInc(c: ptr Counter): int {.gcsafe.} =
  withLock c[].lock:
    inc c[].count
    result = c[].count

proc safeGet(c: ptr Counter): int {.gcsafe.} =
  withLock c[].lock:
    result = c[].count

proc applyIncModel(s: var CounterState): int =
  inc s.count
  s.count

proc applyGetModel(s: var CounterState): int = s.count

proc intEq(a, b: int): bool = a == b

suite "parallelCheck: trivial round-trip":
  test "spec with no ops produces a trivially-linearisable result":
    # Edge case: spec with empty ops list. Generates an empty plan,
    # builds an empty history, isLinearisable trivially accepts.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[])
    var ds = newDataSource(initSplitMix64(1))
    let s = parallelCheck(spec, intEq,
                         prefixSteps = 0,
                         parallelSteps = 0,
                         threads = 0,
                         repetitions = 1,
                         maxJitter = 0)
    let r = s.generate(ds)
    check r.linearisable

  test "prefix-only plan produces a sequential history of the right length":
    # 5 incs on the main thread, no parallel suffixes. The witness
    # length matches the number of prefix steps (history is purely
    # sequential, trivially linearisable).
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = safeInc(c),
          applyModel: applyIncModel),
      ])
    var ds = newDataSource(initSplitMix64(2))
    let s = parallelCheck(spec, intEq,
                         prefixSteps = 5,
                         parallelSteps = 0,
                         threads = 0,
                         repetitions = 1,
                         maxJitter = 0)
    let r = s.generate(ds)
    check r.linearisable
    check r.witness.len == 5

suite "parallelCheck: thread-safe SUT (no race)":
  test "locked counter passes parallelCheck under forAll":
    # The properly-locked counter is linearisable for any schedule.
    # forAll across many examples should always see linearisable=true.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = safeInc(c),
          applyModel: applyIncModel),
        LinOpDef[CounterState, ptr Counter, int](
          opId: 1,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = safeGet(c),
          applyModel: applyGetModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 1,
                    parallelSteps = 2,
                    threads = 2,
                    repetitions = 3,
                    maxJitter = 50),
      prop,
      Settings(maxExamples: 20, seed: 1,
               flakyRetries: 0, maxShrinks: 20,
               maxRejections: 50))
    check r.outcome == otPassed

# A racy (lock-free WRONG) counter: read, +1, write — no atomicity.
# Two concurrent incs from `count = N` both read N, both write N+1,
# both return N+1. The model says one should return N+1 and the
# other N+2.
proc racyInc(c: ptr Counter): int {.gcsafe.} =
  let v = c[].count
  # Deliberately widen the race window between the read and the
  # write. Without this, the two are back-to-back instructions: on
  # an oversubscribed host (e.g. six concurrent sweep containers)
  # the OS time-slices the two threads instead of truly running them
  # concurrently, so the nanosecond-wide gap almost never straddles
  # a context switch and the race is never observed -- every history
  # comes out linearisable and the test flakes red for the wrong
  # reason. Sleeping here forces the scheduler to actually run the
  # other thread inside the window, so it reads the same pre-write
  # value we did. This does not change what's wrong with the
  # counter -- it is still an unsynchronized read-modify-write --
  # it just makes the wrongness observable regardless of machine
  # load. Do not remove this "for performance"; it is load-bearing
  # for the test's ability to catch the race at all.
  #
  # `parallelCheck`'s between-op jitter (`maxJitter`, below) cannot
  # replace this: it only ever runs BETWEEN two ops, never while an
  # op's own body is executing, so it structurally cannot widen a gap
  # that lives inside `racyInc` (see `parallelCheck`'s doc comment in
  # parallel.nim). Confirmed empirically too: with `spinJitter` now a
  # real OS scheduler-yield (see parallel.nim) instead of a nanosecond
  # busy spin, deleting this `sleep(1)` and relying on that alone
  # still failed to catch the race in 1 of 10 idle runs (9/10) -- not
  # reliable enough to keep in a suite that must prove the catch. That
  # 9/10 figure, like every catch-rate figure this module's doc
  # comments quote, is a ONE-TIME measurement taken at the commit that
  # introduced it, not a property any test re-verifies on every sweep
  # -- see the "NOTE on the doc figures (L4)" comment in the suite below
  # for what IS continuously checked. The library also offers
  # `parallelJitterPoint()` / `{.jitterPoints.}`, usable from inside an
  # op body precisely for this shape of race, but their delay length is
  # scheduler-dependent (a yield, not a guaranteed pause) and this
  # `sleep(1)` was kept because it is the one already proven reliable
  # here across idle and CPU-contended runs.
  sleep(1)
  c[].count = v + 1
  v + 1

proc racyGet(c: ptr Counter): int {.gcsafe.} = c[].count

# `{.jitterPoints.}` self-reporting fallback -- "still fires on" note.
# `insertJitterBoundaries` (parallel.nim) warns at compile time whenever it
# meets a node that (a) itself holds a nested statement list and (b) is
# not one of its two deliberate exclusion sets --
# `jitterNestedCallableKinds` (wrong ATTRIBUTION: a separate callable's
# body, not this proc's control flow) or `jitterCannotExecuteAtRuntimeKinds`
# (cannot run a real jitter call at all). Every node kind this fallback has
# caught so far sorts into exactly one of three outcomes:
#
# 1. GIVEN A REAL ARM. `nnkDefer` and `nnkWhenStmt` (round 13 findings
#    R13-2/R13-6), then `nnkPragmaBlock` (`{.cast(gcsafe).}: ...` and
#    similar -- found by the fallback firing while verifying the first
#    two, not by a new review round; see `racyIncPragmaCastGcsafe` below).
#
# 2. MOVED INTO A DELIBERATE EXCLUSION, so the fallback is now SILENT on
#    it: `nnkStaticStmt` (`static: ...`). Giving it the same copy-paste
#    arm as (1) would be actively WRONG, not just pending: a `static:`
#    body runs at COMPILE time (Nim's CTFE VM), and
#    `parallelJitterPoint()` bottoms out in a real `importc`'d syscall
#    (`posix.sched_yield`/`SwitchToThread`) that cannot execute there at
#    all -- verified empirically: a bare `static: parallelJitterPoint()`
#    fails to compile with "cannot 'importc' variable at compile time;
#    sched_yield". This is exactly the same "a warning that fires on
#    correct code trains people to ignore every warning after it"
#    principle that originally justified excluding nested callables (round
#    13 finding R13-1's lesson, applied to this fallback itself) -- so
#    `nnkStaticStmt` was moved into `jitterCannotExecuteAtRuntimeKinds`
#    rather than left to warn forever.
#
# 3. LEFT WARNING ON PURPOSE, because it sorts into NEITHER of the above:
#    a trailing-block call like `withLock lock: <body>` --
#    `nnkCommand`/`nnkCall` with an `nnkStmtList` as its last argument
#    (generic do-notation-without-`do` sugar; this shape is not specific
#    to `withLock` -- it is how ANY template/macro with an `untyped` last
#    parameter receives a trailing block). Unlike `defer`/`when`/pragma
#    blocks, whose body-splicing semantics are fixed by the compiler, the
#    real owner of a trailing-block call's body is whatever macro/template
#    it is handed to -- `jitterPoints` is an `untyped` macro running
#    pre-expansion and has no way to know whether that callee tolerates an
#    extra spliced-in statement (`withLock` clearly would; a macro that
#    pattern-matches its block argument's exact shape might not).
#    Blanket-instrumenting every trailing-block call would be UNSOUND in
#    general, so this is not an "add an arm" case -- but it is also not
#    "always wrong to instrument" the way `static:` is, so it does not
#    belong in an exclusion set either. The warning firing here is
#    reporting a real, judgment-requiring gap, not noise; it is left as
#    future work rather than fixed blind.
#
# So the allow-list does NOT simply converge to "eventually every
# statement-holding node kind gets an arm" -- outcome (2) shows some hits
# need a documented exclusion instead, and outcome (3) shows some hits are
# genuinely ambiguous (sound for the specific macro a SUT author used, not
# sound in general) and are correctly left as an open, actionable warning
# rather than force-classified into either bucket.

# Same race as `racyInc`, but the read/write window is widened with the
# library's low-level intra-op primitive instead of a hand-rolled
# `sleep(1)`. Unlike `racyInc`, this proc has never had a `sleep` in it.
# `{.jitterPoints.}` (below) is the recommended surface for new code; this
# hand-placed call remains supported for the case where the author already
# knows the exact point and wants exactly one yield there.
proc racyIncJitterPoint(c: ptr Counter): int {.gcsafe.} =
  let v = c[].count
  parallelJitterPoint()
  c[].count = v + 1
  v + 1

# Same race again, this time widened purely by annotating the proc
# `{.jitterPoints.}` — no hand-placed `parallelJitterPoint()` call, no
# `sleep`, and no knowledge on the author's part of where the race window
# is. The pragma rewrites the body to yield between every top-level
# statement boundary; here that's the (`let v = ...`) / (`c[].count = ...`)
# boundary and the (`c[].count = ...`) / (`v + 1`) boundary.
proc racyIncPragma(c: ptr Counter): int {.gcsafe, jitterPoints.} =
  let v = c[].count
  c[].count = v + 1
  v + 1

# Round 12 finding Q3: the same race again, but relocated entirely INSIDE a
# `for` loop body. Before the recursion fix, `insertJitterBoundaries` only
# ever split the proc's OWN top-level statement list -- and this proc's
# top-level list is a SINGLE statement (the `for` loop itself), so the
# pre-fix macro would also have hit round 12 finding L12-2 (silent zero
# insertions) on top of Q3's "loop bodies are uninstrumented". Catching the
# race here proves the recursion actually reaches into a `for` body, not
# just past it.
proc racyIncPragmaLoop(c: ptr Counter): int {.gcsafe, jitterPoints.} =
  for _ in 0 ..< 1:
    let v = c[].count
    c[].count = v + 1
    result = v + 1

# Round 13 finding R13-2: the same race again, but the read/write pair sits
# entirely INSIDE a `defer:` body. Before that round's fix, `nnkDefer` had no
# arm in `insertJitterBoundaries` and fell through to the (then-unreported)
# fallback, so this proc's only statement boundary -- the one between the
# `defer` body's own three statements -- got zero jitter points. It was
# SILENT: the proc's top-level statement list has exactly one statement (the
# `defer` itself), so nothing else in the proc kept the total insertion
# count positive either, but nobody had a test here to notice. `result` is
# assigned from inside the deferred block (not before it) so the returned
# value is the post-increment count even though `defer` runs after the rest
# of the (here, empty) body -- the same shape a real deferred-cleanup SUT
# would use to report its final state.
proc racyIncPragmaDefer(c: ptr Counter): int {.gcsafe, jitterPoints.} =
  defer:
    let v = c[].count
    c[].count = v + 1
    result = v + 1

# Round 13 finding R13-6: the same race again, but the read/write pair sits
# inside a `when true:` body in STATEMENT position. Before that round's fix,
# `nnkWhenStmt` had no arm and fell through uninstrumented, same as
# `nnkDefer` above -- and the doc comment at the time incorrectly claimed
# `when` was a genuine expression position with nowhere to put a call,
# which does not hold for `when` used as a statement (its branches are
# ordinary `nnkStmtList` bodies, identical in shape to `if`'s). `jitterPoints`
# runs pre-semantic-analysis, so the untaken `else` branch here (and
# anything the macro inserts into it) is discarded before codegen -- the
# same idiom `coverage.nim`'s `instrumentNode` already relies on for its
# combined `nnkIfStmt, nnkIfExpr, nnkWhenStmt` arm.
proc racyIncPragmaWhen(c: ptr Counter): int {.gcsafe, jitterPoints.} =
  when true:
    let v = c[].count
    c[].count = v + 1
    result = v + 1
  else:
    result = 0

# The self-reporting fallback's own third catch: the read/write pair sits
# inside a `{.cast(gcsafe).}:` pragma block. Before `nnkPragmaBlock` got its
# own arm, this fell through uninstrumented and the fallback warned about
# it -- found while manually verifying the `defer`/`when` fix above, not by
# a new review round (see the "still fires on" note further up). A
# `{.cast(gcsafe).}` block is a very plausible real SUT shape: it is
# exactly how a Nim author tells the compiler "trust me, this is
# thread-safe" around code that is, in fact, the unsynchronized
# read-modify-write this whole module exists to catch. Verified that
# inserting `parallelJitterPoint()` here does not launder an effect
# violation: `parallelJitterPoint` already compiles inside a REAL
# (non-cast) `{.gcsafe.}` block, which requires the compiler to PROVE
# gcsafe-ness rather than merely assert it (see `racyIncJitterPoint`,
# `racyIncPragma` above, both plain `{.gcsafe.}` with no cast) -- so it is
# genuinely gcsafe, not merely accepted through the cast's override.
proc racyIncPragmaCastGcsafe(c: ptr Counter): int {.gcsafe, jitterPoints.} =
  {.cast(gcsafe).}:
    let v = c[].count
    c[].count = v + 1
    result = v + 1

suite "parallelCheck: racy SUT is caught":
  test "lock-free wrong counter is detected as non-linearisable":
    # This test is inherently nondeterministic in nature — racy bugs
    # depend on scheduling. `racyInc` widens its own read/write
    # window with an explicit sleep (see comment there) so the race
    # is caught deterministically in practice, independent of host
    # load. On top of that we use many repetitions per plan + many
    # examples + jitter (staggering thread start times) to maximize
    # the chance of catching it within the budget even if the sleep
    # trick alone weren't enough on some platform.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyInc(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 50),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    # `otFalsified` is a clean catch; `otFlaky` is also a catch — the
    # property is non-deterministic, which is exactly what a race
    # causes (sometimes linearisable, sometimes not, depending on
    # the schedule).
    check r.outcome in {otFalsified, otFlaky}
    # For otFalsified, the diverging op surfaces. For otFlaky, the
    # counterexample captured may be from a *replay* that happened
    # to schedule benignly — we don't assert divergingOp in that
    # case, since the post-shrink replay can land on a linearisable
    # schedule even though the original was racy.
    if r.outcome == otFalsified and r.counterexample.isSome:
      check r.counterexample.get.divergingOp.isSome
      check r.counterexample.get.divergingOp.get == 0

  test "lock-free wrong counter is detected via parallelJitterPoint (no sleep)":
    # Same race as above, widened with `parallelJitterPoint()` called from
    # inside `applySUT` instead of a hand-rolled `sleep(1)` -- the low-level
    # primitive `{.jitterPoints.}` (tested below) is built on, and still
    # supported for a hand-chosen point. `maxJitter` is 0 here deliberately:
    # between-op jitter must contribute nothing, so a catch can only be
    # credited to the intra-op hook itself.
    #
    # NOTE on the doc figures (L4): `parallel.nim`'s doc comments quote
    # 20/20 idle and 10/10 CPU-contended catch rates for this hook, and the
    # `racyInc` comment above quotes 9/10 for between-op jitter alone.
    # Those are ONE-TIME measurements taken when the mechanism was
    # introduced, not properties this suite re-verifies every run -- this
    # test (a single seeded `forAll` run, `seed: 1`, `maxExamples: 30`) is
    # what actually runs on every sweep, and it guards the basic catch (an
    # `otFalsified`/`otFlaky` outcome), not the specific ratio. Re-running
    # 20+30 repeated `forAll` passes here to keep the ratio continuously
    # true would multiply this file's cost on every sweep for a guarantee
    # the single-run check doesn't need; if the real catch rate regresses
    # (e.g. to 15/20), this test can still pass by chance on its one seed.
    # Anyone who needs the rate re-measured should re-run the manual sweep
    # this comment describes, the same way it was produced originally.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyIncJitterPoint(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 0),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    check r.outcome in {otFalsified, otFlaky}

  test "lock-free wrong counter nested in a for loop is detected via {.jitterPoints.}":
    # Round 12 Q3: the read/write pair lives inside `racyIncPragmaLoop`'s
    # `for` body, and the proc's own top-level statement list is a single
    # statement (the loop) -- exactly the shape that both L12-2 (single
    # top-level statement -> zero insertions) and Q3 (no recursion into
    # loop bodies) independently caused to go uninstrumented before the
    # round-12 fix. `maxJitter` is 0 for the same reason as the tests
    # above: a catch can only be credited to the pragma's OWN recursion
    # into the loop body, not to any between-op jitter.
    #
    # See the L4 note further up -- the same one-time-measurement framing
    # applies here. Measured (manual, outside this suite, by looping this
    # same spec/settings over 20 distinct seeds -- op-index/jitter draws
    # are degenerate with a single op and maxJitter=0, so the seed itself
    # contributes no variance; the catch or miss on each iteration comes
    # entirely from real OS thread-scheduling nondeterminism, same as the
    # flat-case figures above): 20/20 idle runs, and 20/20 caught again
    # under CPU contention (`nproc`+2 busy-loop processes pinning every
    # core; two independent 20-iteration contended sweeps were run, both
    # 20/20).
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyIncPragmaLoop(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 0),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    check r.outcome in {otFalsified, otFlaky}

  test "lock-free wrong counter is detected via {.jitterPoints.} (no sleep, no hand-placed call)":
    # Same race again, widened purely by `{.jitterPoints.}` on `racyIncPragma`
    # -- no hand-placed `parallelJitterPoint()` call anywhere in the SUT, no
    # `sleep`, and no knowledge on the test author's part of where the race
    # window sits (the pragma yields at every top-level statement boundary,
    # not just the read/write one). `maxJitter` is 0 here for the same
    # reason as the test above: a catch can only be credited to the pragma.
    #
    # See the L4 note on the test above -- the same one-time-measurement
    # framing applies here.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyIncPragma(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 0),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    check r.outcome in {otFalsified, otFlaky}

  test "lock-free wrong counter inside a defer body is detected via {.jitterPoints.}":
    # Round 13 finding R13-2: the read/write pair lives inside
    # `racyIncPragmaDefer`'s `defer:` body, and the proc's own top-level
    # statement list is a single statement (the `defer` itself) -- the
    # `nnkDefer` arm added for this finding is what reaches the boundary
    # between the deferred block's three statements. `maxJitter` is 0 for
    # the same reason as the tests above: a catch can only be credited to
    # the pragma's own recursion into the defer body, not to any
    # between-op jitter.
    #
    # See the L4 note further up -- the same one-time-measurement framing
    # applies here. Measured (manual, outside this suite, the same way as
    # `racyIncPragmaLoop`'s figure: looping this same spec/settings over 20
    # distinct seeds, idle host): 20/20.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyIncPragmaDefer(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 0),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    check r.outcome in {otFalsified, otFlaky}

  test "lock-free wrong counter inside a when-statement body is detected via {.jitterPoints.}":
    # Round 13 finding R13-6: the read/write pair lives inside
    # `racyIncPragmaWhen`'s `when true:` branch, in statement position (not
    # the expression position the pre-fix doc comment incorrectly lumped it
    # in with). The proc's own top-level statement list is a single
    # statement (the `when`), so before the `nnkWhenStmt` arm existed this
    # was uninstrumented and silent, same shape as the `defer` case above.
    # `maxJitter` is 0 for the same reason as every other test in this
    # file: a catch can only be credited to the pragma's own recursion into
    # the `when` branch body.
    #
    # See the L4 note further up -- the same one-time-measurement framing
    # applies here. Measured (manual, outside this suite, the same way as
    # the `defer` test above: looping this same spec/settings over 20
    # distinct seeds, idle host): 20/20.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyIncPragmaWhen(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 0),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    check r.outcome in {otFalsified, otFlaky}

  test "lock-free wrong counter inside a {.cast(gcsafe).} block is detected via {.jitterPoints.}":
    # The self-reporting fallback's third catch (see the "still fires on"
    # note further up): the read/write pair lives inside
    # `racyIncPragmaCastGcsafe`'s `{.cast(gcsafe).}:` block, and the
    # proc's own top-level statement list is a single statement (the
    # pragma block itself) -- the `nnkPragmaBlock` arm added for this
    # finding is what reaches the boundary between the block's three
    # statements. `maxJitter` is 0 for the same reason as every other test
    # in this file: a catch can only be credited to the pragma's own
    # recursion into the pragma-block body.
    #
    # See the L4 note further up -- the same one-time-measurement framing
    # applies here. Measured (manual, outside this suite, the same way as
    # the `defer`/`when` tests above: looping this same spec/settings over
    # 20 distinct seeds, idle host): 20/20.
    let spec = LinSpec[CounterState, ptr Counter, int](
      modelInitial: CounterState(),
      newSUT: proc(): ptr Counter {.gcsafe.} = newSafeCounter(),
      ops: @[
        LinOpDef[CounterState, ptr Counter, int](
          opId: 0,
          applySUT: proc(c: ptr Counter): int {.gcsafe.} = racyIncPragmaCastGcsafe(c),
          applyModel: applyIncModel),
      ])
    proc prop(lr: LinResult[int, int]) = (ensure lr.linearisable)
    let r = forAll(
      parallelCheck(spec, intEq,
                    prefixSteps = 0,
                    parallelSteps = 5,
                    threads = 2,
                    repetitions = 30,
                    maxJitter = 0),
      prop,
      Settings(maxExamples: 30, seed: 1,
               flakyRetries: 0, maxShrinks: 5,
               maxRejections: 50))
    check r.outcome in {otFalsified, otFlaky}
