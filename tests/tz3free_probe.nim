## Z3-free probe: `import nelli` must compile with no z3 on the path.
##
## RFC-z3-optional. Compiled (not run) by the fuzzer CI legs under
## `--skipProjCfg --skipParentCfg --skipUserCfg --noNimblePath --path:src`
## and NO z3/softlink path, so any transitive `import z3` reintroduced
## anywhere under `src/` fails here. All four skips are load-bearing: the
## first two alone still leave the user config and ~/.nimble/pkgs2 able to
## resolve `import z3`, which would make this check go silently green on a
## machine that happens to have a nimble-installed z3.
##
## S1c widened it: the symex MARKERS are Z3-free annotations meant for
## production code, so "compiles with no z3 on the path" must cover a
## marker-annotated SUT too, not just a bare import. Behavior is pinned
## separately in `tests/tfuzzsymexmarkers.nim`; what this file adds is that
## the markers resolve with the walker genuinely unreachable.
import nelli

proc probeAnnotatedSut(x: int): int =
  symexAssume(x >= 0)
  if x > 10:
    symexTarget("big")
    result = x * 2
  else:
    symexTarget("small")
    result = x
  symexAssert(result >= 0)

when isMainModule:
  doAssert probeAnnotatedSut(20) == 40
  echo "z3-free probe OK"
