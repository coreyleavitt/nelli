## RFC-0016 K5b (W-58): the `mm=arc` cross-build cfg suite (its `.nim.cfg`). The
## pins are `k5b_cfg_body.nim`'s.
import nelli/smt/buildprofile
const
  cfgName = "mm=arc"
  cfgApplies = buildSemantics.mm == mmArc
  cfgWhy = ""
include ./k5b_cfg_body
