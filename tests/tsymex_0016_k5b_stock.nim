## RFC-0016 K5b: the profile test that runs on BOTH toolchains. It imports the
## profile alone, never `nelli/symex` (which a stock Nim refuses at the
## import), so an unmodified Nim 2.2.10 can compile it. On the patched Nim it
## asserts the build is admitted as patched; on a stock Nim (run by
## `tsymex_0016_k5b_refusals` when `NELLI_STOCK_NIM` is set) it asserts the
## build is refused by name and echoes "stock Nim: refused by name".
import std/[unittest, options, strutils]
import nelli/smt/buildprofile

suite "K5b: the toolchain the profile saw":
  when buildProvenance.stockNim:
    test "an unmodified Nim is refused by name":
      let r = admitBuild(buildSemantics, buildProvenance)
      check r.isSome
      check r.get.field == bfNim
      check "[field: nim]" in refusalMessage(r.get)
      check rowOf(buildSemantics, unreadHost, buildProvenance).isNone
      check buildProvenance.patchset.len < "backport-25858,backport-26093".len
      echo "stock Nim: refused by name"
  else:
    test "the patched Nim is not refused for its toolchain":
      check buildProvenance.patchset == "backport-25858,backport-26093"
      let r = admitBuild(buildSemantics, buildProvenance)
      check r.isNone or r.get.field != bfNim
