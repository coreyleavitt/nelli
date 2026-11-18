## RFC-0016 K8b (INT-56, section 12 item 4) -- the admission-axis fuzzer
## suite for the magic axis (second half of its stream): generated programs, each packing several exact rows'
## fragments (tests/s0016_k8b_snippets.nim), run through `symexFind` and the
## native differential with one rotating metamorphic relation (dead code under
## a false guard, extract-to-proc, wrap-in-template, and the fragments in
## reverse order where none raises). The cells-exercised records name the
## rows; K1 (`tsymex_0016_universe`) judges each axis's figure against
## `tests/0016-axis-rows.floor` (`s0016_k8b_axes.axisJoinProblems`).
##   -d:k8bSeed=N   (the stream's seed)
import std/[unittest, os, strutils, sets, math]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const k8bSeed {.intdefine.} = 20261117

axisBatch(axMagic, "mgb", runBatch_mgb, "tsymex_0016_k8b_axes_magic_b.nim",
          k8bSeed, (((axisSnippets[axMagic].len + 5) div 6) div 2), (((axisSnippets[axMagic].len + 5) div 6) - ((axisSnippets[axMagic].len + 5) div 6) div 2), 6)
