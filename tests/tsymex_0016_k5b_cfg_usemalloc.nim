## RFC-0016 K5b (W-58): the `useMalloc` cross-build cfg suite (its `.nim.cfg`). The
## pins are `k5b_cfg_body.nim`'s.
const
  cfgName = "useMalloc"
  cfgApplies = defined(useMalloc)
  cfgWhy = ""
include ./k5b_cfg_body
