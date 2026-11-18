## RFC-0016 K8b (INT-56, section 12 item 4) -- the admission-axis fuzzer
## suite for the build axis's libpcre rows (`pcre_engine.pcreLibs`) in the
## default build: a generated program around a regex call per row
## (tests/s0016_k8b_snippets.nim), run through `symexFind` and the native
## differential with one rotating metamorphic relation. The row is the
## library the binary loaded, so only the host's row is recorded (the Linux
## image's 8.45 interpreter, the Windows legs' 8.37 JIT). The switch rows run
## in their own binaries (`tsymex_0016_k8b_axes_build_*`, each compiled under
## its switch). K1 (`tsymex_0016_universe`) judges the axis figure against
## `tests/0016-axis-rows.floor`.
##   -d:k8bSeed=N   (the stream's seed)
import std/[unittest, os, strutils, sets, math, re]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/pcre_engine
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const k8bSeed {.intdefine.} = 20261117

proc hostPcreKey(): string =
  ## `pcreLibs`' key for the library std/re loaded: `version|engine`.
  pcreVersion() & "|" & (if pcreRunsJit(): "jit" else: "interp")

buildAxisBatch(["8.45 2021-06-15|interp", "8.37 2015-04-28|jit",
                "8.37 2015-04-28|interp"], true, "", "bpcre", runBatch_bpcre,
               "tsymex_0016_k8b_axes_build.nim", k8bSeed, @[hostPcreKey()])
