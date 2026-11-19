## RFC-0016 K8b (INT-56, section 12 item 4) -- the pragma axis's C++ rows
## (`routine/importcpp`, `routine/exportcpp`, `type/importcpp`): Nim accepts
## them on the cpp backend only (`exportcpp requires cpp backend`; an
## `importcpp` routine does not link under C), so they are out of the axis
## stream (`ownRows`) and run here, through `symexFind` and the native
## differential with one rotating metamorphic relation, on the cpp legs. A C
## build writes one `skipped` record. K1 judges the figure.
##   -d:k8bSeed=N   (the stream's seed)
import std/[unittest, os, strutils, sets, math]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const k8bSeed {.intdefine.} = 20261117

ownAxisBatch(axPragma, defined(cpp),
             "the C++ pragma rows need the cpp backend: the cpp legs exercise them",
             "pgcpp", runBatch_pgcpp, "tsymex_0016_k8b_axes_pragma_cpp.nim",
             k8bSeed)
