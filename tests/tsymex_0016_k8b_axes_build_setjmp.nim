## RFC-0016 K8b (INT-56, section 12 item 4) -- the build axis's `exceptions/setjmp` row:
## its fragment (tests/s0016_k8b_snippets.nim) compiled under the switch (this
## file's `.nims`), run through `symexFind` and the native differential
## with one rotating metamorphic relation. The libpcre rows and the axis's
## other switches run in `tsymex_0016_k8b_axes_build*`; K1 judges the figure.
##   -d:k8bSeed=N   (the stream's seed)
import std/[unittest, os, strutils, sets, math]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/buildprofile
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const k8bSeed {.intdefine.} = 20261117

buildAxisBatch(["exceptions/setjmp"], buildSemantics.exceptions == exSetjmp,
               "setjmp exceptions cannot be built here: the cpp backend has no setjmp " &
               "mode, and a Windows setjmp walk crashes entering its fiber (INT-12)",
               "bsetjmp", runBatch_bsetjmp,
               "tsymex_0016_k8b_axes_build_setjmp.nim", k8bSeed, @["exceptions/setjmp"])
