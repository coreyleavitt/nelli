## RFC-0016 K8b (INT-56, section 12 item 4) -- the pragma axis's rows for
## foreign code of a backend no leg builds: `routine/importjs` and
## `type/importjs` (Nim: "`importjs` pragma requires the JavaScript target",
## and `nelli/symex` is not built for JavaScript) and `routine/importObjC`
## (the module then compiles as Objective-C, and no leg's image has an
## Objective-C compiler, `cc1obj`). They are out of the axis stream
## (`ownRows`); every leg writes one `skipped` record here, so K1 still sees
## the suite ran. A leg on either backend would exercise them.
##   -d:k8bSeed=N   (the stream's seed)
import std/[unittest, os, strutils, sets, math]
import nelli
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers
import ./s0016_k8a_gen
import ./s0016_k8b_suite

const k8bSeed {.intdefine.} = 20261117

ownAxisBatch(axPragma, defined(js),
             "no leg builds the JavaScript backend (importjs) or has an " &
             "Objective-C compiler (importObjC): no leg exercises these rows",
             "pgforeign", runBatch_pgforeign,
             "tsymex_0016_k8b_axes_pragma_foreign.nim", k8bSeed)
