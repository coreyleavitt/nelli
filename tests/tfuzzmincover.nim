## F3 (docs/rfc/0001-chapulin-hardening.md ~line 634): `minimalCovering*` is exported
## from `fuzz.nim` so a caller can minimize an external corpus offline — given the
## entries' choice-IRs and their observed `Coverage` — without driving a full
## `fuzz` run. This test exercises it purely through the public `nelli` import
## (it would fail to COMPILE if the proc were still unexported), and pins the
## greedy set-cover behavior: redundant entries drop, ties break to lowest index.

import std/unittest
import nelli
import nelli/[choice]

suite "F3: minimalCovering is public API":

  test "greedy set cover keeps a minimal covering subset, drops the redundant entry":
    # e0 covers edges {0,1}; e1 covers {1,2}; e2 covers {2} (⊆ e1, redundant).
    let entries = @[
      @[integerChoice(0, 0, 10, 0)],
      @[integerChoice(1, 0, 10, 0)],
      @[integerChoice(2, 0, 10, 0)],
    ]
    let covs = @[
      Coverage(counters: @[1'u8, 1, 0]),   # {0,1}
      Coverage(counters: @[0'u8, 1, 1]),   # {1,2}
      Coverage(counters: @[0'u8, 0, 1]),   # {2}  — redundant given e1
    ]
    let m = minimalCovering(entries, covs)
    # Union of all edges is {0,1,2}. Greedy: e0 and e1 tie at gain 2 → e0 (lowest
    # index) first (covers {0,1}), then e1 covers the remaining {2}. e2 adds
    # nothing new → dropped. Minimal covering set = {e0, e1}.
    check m.len == 2
    check m[0] == entries[0]
    check m[1] == entries[1]

  test "an entry that covers nothing (unrun seed) is dropped":
    let entries = @[
      @[integerChoice(0, 0, 10, 0)],
      @[integerChoice(1, 0, 10, 0)],
    ]
    let covs = @[
      Coverage(counters: @[1'u8, 0]),      # {0}
      Coverage(counters: @[0'u8, 0]),      # {} — covers nothing
    ]
    let m = minimalCovering(entries, covs)
    check m.len == 1
    check m[0] == entries[0]

  test "empty input yields empty covering set":
    let m = minimalCovering(newSeq[seq[ChoiceNode]](0), newSeq[Coverage](0))
    check m.len == 0
