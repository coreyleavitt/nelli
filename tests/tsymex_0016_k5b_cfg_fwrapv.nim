## RFC-0016 K5b (W-58): the `-d:nelliFwrapv` cross-build cfg suite (its
## `.nim.cfg`), checks left ON: the verdicts are the default build's, which is
## what `rowOf` claims when it calls `fwrapv` neutral. (With checks off the wrap
## is modelled: `tsymex_0016_k5a_fwrapv`.) Under vcc the build is refused by
## design and cannot import `nelli/symex`; the cell is recorded as skipped there
## and the refusal is `tsymex_0016_k5a_fwrapv`'s.
import nelli/smt/buildprofile
const
  cfgName = "fwrapv"
  cfgApplies = buildSemantics.fwrapv and buildProvenance.ccFamily != ccVcc
  cfgWhy = "-d:nelliFwrapv is refused under vcc, which has no -fwrapv"
when defined(vcc):
  import ./s8cu_helpers
  skipCell(cellKey(axBuild, cfgName), cfgWhy)
else:
  include ./k5b_cfg_body
