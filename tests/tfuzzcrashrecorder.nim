## RFC-fuzzer-nextgen R27: `CrashRecorder` (fuzzcrash.nim) exercised
## directly — plain string keys, no `Coverage`/`Observation[T]`/`fuzz()`
## campaign. Proves the de-dup (6a) + stop-on-first-crash (F4) +
## `lastCrashIter` (S5a) seam extracted from `fuzz[T]`'s
## `recordCrashIfInteresting` closure really owns its state.

import std/unittest
import nelli/fuzzcrash

suite "CrashRecorder — de-dup (FUZZ_PLAN 6a)":

  test "the first sighting of a key is always recordable":
    var r = newCrashRecorder()
    let d = observe(r, 1, "keyA")
    check d.recordable

  test "a duplicate key is NOT recordable by default (keepAllCrashes: false)":
    var r = newCrashRecorder()
    discard observe(r, 1, "keyA")
    let d = observe(r, 2, "keyA")
    check not d.recordable

  test "a distinct key is recordable even after another key was already seen":
    var r = newCrashRecorder()
    discard observe(r, 1, "keyA")
    let d = observe(r, 2, "keyB")
    check d.recordable

  test "keepAllCrashes: true makes every observation (dup included) recordable":
    var r = newCrashRecorder(keepAllCrashes = true)
    discard observe(r, 1, "keyA")
    let d = observe(r, 2, "keyA")
    check d.recordable

suite "CrashRecorder — stop-on-first-crash (F4)":

  test "stopOnFirstCrash: false never signals a stop, new or duplicate":
    var r = newCrashRecorder(stopOnFirstCrash = false)
    check not observe(r, 1, "keyA").shouldStop
    check not observe(r, 2, "keyA").shouldStop
    check not observe(r, 3, "keyB").shouldStop

  test "stopOnFirstCrash: true signals a stop on the first (new) crash":
    var r = newCrashRecorder(stopOnFirstCrash = true)
    check observe(r, 1, "keyA").shouldStop

  test "a duplicate never signals a stop, even under stopOnFirstCrash":
    var r = newCrashRecorder(stopOnFirstCrash = true)
    discard observe(r, 1, "keyA")   # this call already signaled stop
    check not observe(r, 2, "keyA").shouldStop

  test "keepAllCrashes and stopOnFirstCrash together: a dup is recorded but never re-stops":
    var r = newCrashRecorder(keepAllCrashes = true, stopOnFirstCrash = true)
    let first = observe(r, 1, "keyA")
    check first.recordable and first.shouldStop
    let dup = observe(r, 2, "keyA")
    check dup.recordable and not dup.shouldStop

suite "CrashRecorder — lastCrashIter (S5a)":

  test "starts at 0 (no crash observed yet)":
    let r = newCrashRecorder()
    check lastCrashIter(r) == 0

  test "set on every observation, dup or new":
    var r = newCrashRecorder()
    discard observe(r, 5, "keyA")
    check lastCrashIter(r) == 5
    discard observe(r, 9, "keyA")   # duplicate — still updates lastCrashIter
    check lastCrashIter(r) == 9
    discard observe(r, 12, "keyB")
    check lastCrashIter(r) == 12
