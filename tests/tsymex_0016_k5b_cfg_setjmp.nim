## RFC-0016 K5b (W-58): the `--exceptions:setjmp` cross-build cfg suite (its
## `.nims`, which applies it to the c backend off Windows only: the cpp backend
## cannot build setjmp, and the Windows walk crashes entering its fiber, INT-12).
## Where it cannot be built the suite records `skipCell`, never a bare `skip`.
## The pins are `k5b_cfg_body.nim`'s.
import nelli/smt/buildprofile
const
  cfgName = "exceptions/setjmp"
  cfgApplies = buildSemantics.exceptions == exSetjmp
  cfgWhy = "setjmp exceptions cannot be built here: the cpp backend has no " &
           "setjmp mode, and a Windows setjmp walk crashes entering its fiber (INT-12)"
include ./k5b_cfg_body
