## RFC-0016 K5b (W-58): the `-d:nelliFwrapv` cross-build cfg suite (its
## `.nim.cfg`), checks left ON: the verdicts are the default build's, which is
## what `rowOf` claims when it calls `fwrapv` neutral. (With checks off the wrap
## is modelled: `tsymex_0016_k5a_fwrapv`.)
##
## The suite keys on the product's own admission of the build, never on the C
## compiler: `nelli/symex` runs `admitBuild` at compile time and refuses a build
## it cannot model (under vcc, which has no `-fwrapv`, signed overflow stays
## undefined, so `-d:nelliFwrapv` would claim a wrap the C compiler does not
## give). A refused build cannot import `nelli/symex` (nor `s8cu_helpers`,
## which does), so that arm asserts the refusal by name; an admitted build runs
## the pins. The msvc row's cell is allowlisted
## (`tests/0016-allowlist/build.txt`, `rows=msvc`). Intake #176 (INT-49).
import std/options
import nelli/smt/buildprofile
const
  cfgName = "fwrapv"
  cfgApplies = buildSemantics.fwrapv
  cfgWhy = "the build does not define nelliFwrapv"
  admission = admitBuild(buildSemantics, buildProvenance)
when admission.isSome:
  import std/[unittest, strutils]
  suite "K5b: -d:nelliFwrapv cfg suite (refused build)":
    test "symex refuses the build by name":
      check buildSemantics.fwrapv
      check admission.get.field == bfFwrapv
      check "-fwrapv" in admission.get.reason
else:
  include ./k5b_cfg_body
