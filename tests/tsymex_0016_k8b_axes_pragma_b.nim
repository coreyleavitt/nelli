## RFC-0016 K8b (INT-56, section 12 item 4) -- the admission-axis fuzzer
## suite for the pragma axis (second half of its stream): generated programs, one exact row's
## fragment each (tests/s0016_k8b_snippets.nim, `per` = 1: packing several
## rows into one query multiplies the solve cost), run through `symexFind`
## and the native differential with one rotating metamorphic relation (dead
## code under a false guard, extract-to-proc, wrap-in-template). A row blocked
## by an open worklist defect (`blockedRows`) is left out and counts as not
## exercised. The cells-exercised records name the rows; K1
## (`tsymex_0016_universe`) judges each axis's figure against
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

axisBatch(axPragma, "pgb", runBatch_pgb, "tsymex_0016_k8b_axes_pragma_b.nim",
          k8bSeed, streamRows(axPragma) * 1 div 2,
          streamRows(axPragma) * 2 div 2 - streamRows(axPragma) * 1 div 2, 1)
