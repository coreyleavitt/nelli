## RFC-0016 0.10.0 review, finding H3: `modelPins` pins no opaque-call
## havoc epoch.
##
## `modelPins` pinned `heap_<k>@ep<n>` for n >= 1 as well as the input heap
## `heap_<k>`. An epoch is the result of a callee the walk does not model
## (`havocOpaqueHeaps`), not an input: the tail walk recreates the same-named
## constant, so the pin fixed the callee's effect to the explore model's
## value, and a tail the real callee drives into an overflow was a trusted,
## replay-confirmed `sxSat`.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

# The file builds with `--overflowChecks:off` (its `.nim.cfg`): a signed
# overflow is `ubSignedOverflow`.

type Box = ref object
  v: int

proc ext(b: Box) {.symexOpaque.} =
  b.v = 7

proc epochPre(b: Box; x: int64): int64 =
  ## `b.v` is read before the label, so the explore model interprets the
  ## callee's havoc epoch; the real callee writes 7 and the tail overflows.
  ext(b)
  if b.v != 5 and x > 100:
    symexTarget("hit")
  if b.v == 7: result = x + high(int64)
  else: result = x

proc epochPost(b: Box; x: int64): int64 =
  ## `b.v` first read after the label.
  ext(b)
  if x > 100:
    symexTarget("hit")
  if b.v == 7: result = x + high(int64)
  else: result = x

proc epochPreDefined(b: Box; x: int64): int64 =
  ## Control: the same epoch read before the label, a tail defined on both
  ## arms.
  ext(b)
  if b.v != 5 and x > 100:
    symexTarget("hit")
  if b.v == 7: result = x - 1
  else: result = x

suite "CR2 H3: the tail walk does not pin a callee's havoc epoch":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 355

  test "the finding's trigger: the real callee's effect overflows the tail":
    let r = symexFind(epochPre, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.witness[1] > 100
    # Natively: `ext` writes 7, so the tail computes x + high(int64), which
    # overflows for every x > 0.
    check not r.trusted
    check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds

  test "the epoch first read after the label: not a trusted sat":
    # The explore model does not interpret an epoch nothing before the label
    # reads, so nothing pinned it; the verdict is not trusted either way.
    let r = symexFind(epochPost, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check not r.trusted
    if r.status == sxSat:
      check UbKind(ubSignedOverflow) in r.soundness.undefinedKinds

  test "control: a defined tail over the epoch stays trusted":
    let r = symexFind(epochPreDefined, tLabel("hit"), pinSettingsConst)
    checkpoint show(r.errors)
    checkpoint $r.soundness
    check r.status == sxSat
    check r.trusted
    check r.soundness.undefinedKinds == {}
