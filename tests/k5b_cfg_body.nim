## RFC-0016 K5b (W-58, W-51): the pins every cross-build cfg suite runs. A thin
## `tsymex_0016_k5b_cfg_*.nim` file with its own `.nim.cfg` (or `.nims`) sets
## `cfgName` (the `build:` cell it records), `cfgApplies` (the configuration
## really is this build) and `cfgWhy` (why not, when it cannot be built here),
## then `include`s this file. `rowOf` calls each of these configurations
## neutral; the pins say the verdicts are the default build's, and the memory
## pins (W-51) say the heap model agrees with native under it.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

type CfgCell = ref object
  x: int

proc sutAdd(v: int) =
  ## Arithmetic: the same witness in every configuration.
  if v + 1 == 6: symexTarget("hit")

proc sutOverflow(v: int) =
  ## Overflow checks stay on in every configuration here (`release` keeps
  ## them): the add at `high(int)` raises.
  discard v + 1

proc sutAlias(v: int) =
  ## W-51: two names for one heap object (aliasing through a shared ref).
  var a: CfgCell
  new(a)
  let b = a
  b.x = v
  a.x = a.x + 1
  if a.x == 6: symexTarget("hit")

proc sutZeroInit(v: int) =
  ## W-51: `new` zero-initialises the object in every memory model.
  var a: CfgCell
  new(a)
  if a.x == 0 and v == 3: symexTarget("hit")

proc sutDistinct(v: int) =
  ## W-51: two `new`s are two objects.
  var a, b: CfgCell
  new(a); new(b)
  a.x = v
  b.x = v + 1
  if a.x == 4 and b.x == 5: symexTarget("hit")

const cfgKey = cellKey(axBuild, cfgName)

suite "K5b cfg suite: " & cfgName:
  when cfgApplies:
    test "the build is the configuration":
      check parseInt(symexWalkerVersion) >= 288
      check cfgApplies

    test "arithmetic agrees with native":
      let r = pinExact(sutAdd, cfgKey, domain = sampled([5, 0, 7]))
      check r.status == sxSat
      check r.trusted

    test "an overflow raises, as in the default build":
      let r = pinExact(sutOverflow, cfgKey, target = tRaisedExn("OverflowDefect"),
                       domain = sampled([high(int), 0, 7]))
      check r.status == sxRaised

    test "memory: aliasing through a shared ref":
      let r = pinExact(sutAlias, cfgKey, domain = sampled([5, 0, 7]))
      check r.status == sxSat
      check r.trusted

    test "memory: new zero-initialises":
      let r = pinExact(sutZeroInit, cfgKey, domain = sampled([3, 0, 7]))
      check r.status == sxSat
      check r.trusted

    test "memory: two objects stay two":
      let r = pinExact(sutDistinct, cfgKey, domain = sampled([4, 0, 7]))
      check r.status == sxSat
      check r.trusted
  else:
    test "this configuration cannot be built here":
      skipCell(cfgKey, cfgWhy)
