## RFC-0016 K8b (INT-56, section 12 item 4) -- the pragma axis's
## `routine/base` row: a `{.base.}` method's call is decided only where the
## toolchain writes the method dispatch table (`replayproc.hasMethodTable`,
## PRC-02b); a stock compiler's build declines the call
## (`feGlobalRouteUnproved`) by design. The row is out of the axis stream
## (`ownRows`) and runs here, through `symexFind` and the native differential
## with one rotating metamorphic relation, on a leg whose toolchain has the
## table. Any other leg writes one `skipped` record. K1 judges the figure.
##   -d:k8bSeed=N   (the stream's seed)
import std/[unittest, os, strutils, sets, math]
import nelli
import nelli/symex
import nelli/smt/admission
from nelli/smt/replayproc import hasMethodTable
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const k8bSeed {.intdefine.} = 20261117

ownAxisBatch(axPragma, hasMethodTable,
             "no method dispatch table in this toolchain (PRC-02b): a leg " &
             "built with the 0008-patched Nim exercises the row, and no leg " &
             "has one until that toolchain is published as the 2.2.10 " &
             "artifacts the Windows legs use",
             "pgdisp", runBatch_pgdisp, "tsymex_0016_k8b_axes_pragma_dispatch.nim",
             k8bSeed)
