## RFC-0016 K5b (W-58): the `release` cross-build cfg suite (its `.nim.cfg`). The
## pins are `k5b_cfg_body.nim`'s.
import nelli/smt/buildprofile
const
  cfgName = "release"
  cfgApplies = buildSemantics.release
  cfgWhy = ""
include ./k5b_cfg_body
