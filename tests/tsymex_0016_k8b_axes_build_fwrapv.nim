## RFC-0016 K8b (INT-56, section 12 item 4) -- the build axis's `fwrapv` row:
## its fragment (tests/s0016_k8b_snippets.nim) compiled under the switch (this
## file's `.nim.cfg`), run through `symexFind` and the native differential
## with one rotating metamorphic relation. The libpcre rows and the axis's
## other switches run in `tsymex_0016_k8b_axes_build*`; K1 judges the figure.
##
## As in `tsymex_0016_k5b_cfg_fwrapv`, a build `nelli/symex` refuses (vcc has
## no `-fwrapv`) cannot import it, nor `s8cu_helpers`: that arm asserts the
## refusal and writes the suite's `skipped` record itself, on the row the
## leg is with the switch off, so K1 still sees the suite ran there.
##   -d:k8bSeed=N   (the stream's seed)
import std/options
import nelli/smt/buildprofile
const
  refusal = admitBuild(buildSemantics, buildProvenance)
  fileName = "tsymex_0016_k8b_axes_build_fwrapv.nim"
when refusal.isSome:
  import std/[unittest, strutils, json, os, times]
  suite "K8b axis build: fwrapv (refused build)":
    test "symex refuses the build by name, and the suite records it ran":
      check buildSemantics.fwrapv
      check refusal.get.field == bfFwrapv
      var b = buildSemantics
      b.fwrapv = false
      let row = rowOf(b, HostSemantics(z3: z3Unread), buildProvenance)
      check row.isSome
      let dir = getEnv("NELLI_PIN_DIR", "tests" / ".pins")
      createDir(dir)
      let rec = %*{"kind": "exercised",
        "runId": splitFile(getAppFilename()).name & "-" & $getCurrentProcessId(),
        "testFile": fileName, "family": "build", "seed": 0, "progId": 0,
        "variant": "orig", "outcome": "skipped", "cells": newJArray(),
        "build": "", "row": (if row.isSome: $row.get else: ""),
        "date": now().utc.format("yyyy-MM-dd'T'HH:mm:ss'Z'")}
      let f = open(dir / ("tsymex_0016_k8b_axes_build_fwrapv-exercised-" &
                          $getCurrentProcessId() & ".jsonl"), fmAppend)
      f.writeLine($rec)
      f.close()
else:
  import std/[unittest, os, strutils, sets, math]
  import nelli
  import nelli/symex
  import nelli/smt/admission
  import ./s8cu_helpers
  import ./s0016_k8a_gen
  import ./s0016_k8b_suite

  const k8bSeed {.intdefine.} = 20261117

  buildAxisBatch(["fwrapv"], buildSemantics.fwrapv,
                 "the build does not define nelliFwrapv",
                 "bfwrapv", runBatch_bfwrapv, fileName, k8bSeed, @["fwrapv"])
