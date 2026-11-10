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
  # This arm cannot import `nelli/symex` (nor `s8cu_helpers`, which does): the
  # build is refused at compile time. It asserts the refusal through
  # `admitBuild`, as `tsymex_0016_k5a_fwrapv` does; the msvc row's cell is
  # allowlisted (`tests/0016-allowlist/build.txt`, `rows=msvc`).
  import std/[unittest, strutils, options]
  suite "K5b: -d:nelliFwrapv cfg suite (vcc)":
    test "symex refuses the build by name":
      let refusal = admitBuild(buildSemantics, buildProvenance)
      check refusal.isSome
      if refusal.isSome:
        check refusal.get.field == bfFwrapv
        check "-fwrapv" in refusal.get.reason
else:
  include ./k5b_cfg_body
