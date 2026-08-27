## RFC-fuzzer-nextgen R27 (code review, MEDIUM/design): the S2/S3 mutation-
## operator-selection collaborator extracted from the `fuzz[T]` loop
## (`fuzz.nim`).
##
## Before this module, `fuzz[T]` built its `arms` seq and `opBandit`
## (`nelli/bandit.OperatorBandit`) as two separate loop-locals, constructed
## from three different `FuzzSettings` fields (`guidance.enableI2S`,
## `scheduling.uniformHavoc`, plus a checkpoint-restore branch keyed on arm
## count), and every pick/credit call site had to keep `arms`/`opBandit` in
## sync by hand (an index into one always meant the same arm in the other).
## `OperatorSelector` owns both together: the arm space is fixed at
## construction (a pure function of `enableI2S`/`uniformHavoc`, exactly
## reproducing the pre-R27 loop's arm-building order), and `pick`/`credit`/
## `pullsOf` are the bandit's own read/write surface, scoped to this arm
## space.
##
## Byte-for-byte behavior preserved from the pre-R27 loop:
## - Arm order/membership is EXACTLY the loop's own construction: the five
##   base arms always present, `maI2SReplace` appended iff `enableI2S`, then
##   (iff NOT `uniformHavoc`) `maInterestingValue` unconditionally and
##   `maDictInsert` iff `enableI2S` — same four-line sequence, same order.
## - `pick(uniform=true)` reproduces `rng.next mod pickMax` (now with the
##   `int` conversion happening immediately rather than at each use site,
##   which changes no value: the mod result always fits `pickMax.int`).
## - `pick(uniform=false)` is exactly `bandit.chooseOperator(rng)`.
## - `restore` is the loop's own arm-count-matching gate (unchanged: the
##   CALLER still checks `pulls.len == selector.len` before calling this —
##   see `fuzz.nim`'s S6 checkpoint-restore site — so a settings-changed
##   mismatch degrades to "no restore" exactly as before).

import ./rng, ./bandit

type
  MutationArm* = enum
    maPerturbInt, maKindBoundary, maSpanSplice, maSpanDelete, maSpanDuplicate,
    maI2SReplace, maInterestingValue, maDictInsert

  OperatorSelector* = object
    arms: seq[MutationArm]
    bandit: OperatorBandit

proc newOperatorSelector*(enableI2S: bool; uniformHavoc: bool): OperatorSelector =
  var arms = @[maPerturbInt, maKindBoundary, maSpanSplice, maSpanDelete, maSpanDuplicate]
  if enableI2S: arms.add maI2SReplace
  if not uniformHavoc:
    arms.add maInterestingValue
    if enableI2S: arms.add maDictInsert
  OperatorSelector(arms: arms, bandit: newOperatorBandit(arms.len))

proc len*(o: OperatorSelector): int = o.arms.len

proc bandit*(o: OperatorSelector): OperatorBandit = o.bandit
  ## Read access to the underlying `OperatorBandit` — needed by the caller's
  ## own checkpoint save (`CheckpointManager.save`, fuzzcheckpoint.nim takes
  ## a plain `OperatorBandit`, not this module's type, so it has no
  ## dependency on `fuzzoperator`).

proc armAt*(o: OperatorSelector; idx: int): MutationArm = o.arms[idx]

proc restore*(o: var OperatorSelector; pulls, rewardSum: seq[float]; totalPulls: float) =
  ## Replace the bandit's learned weights with a checkpoint's — the CALLER
  ## is responsible for only calling this when `pulls.len == o.len` (arm
  ## index is positional; see `fuzz.nim`'s S6 restore site), same
  ## precondition the pre-R27 loop enforced inline before this extraction.
  o.bandit = restoreOperatorBandit(pulls, rewardSum, totalPulls)

proc pick*(o: var OperatorSelector; rng: var SplitMix64; uniform: bool): int =
  ## The pre-S2 uniform fallback (`rng.next mod pickMax`) or the discounted-
  ## UCB1 bandit's own choice — consumes `rng` identically to the pre-R27
  ## loop in both branches.
  if uniform: int(rng.next mod uint64(o.arms.len))
  else: chooseOperator(o.bandit, rng)

proc credit*(o: var OperatorSelector; picks: seq[int]; reward: float) =
  ## Credit every arm in `picks` (a havoc-stacked iteration's full operator
  ## sequence, possibly with repeats) with `reward` — the pre-R27 loop's
  ## "credit the whole stack" policy (S2 deliverable 2 / S3), unchanged.
  for p in picks: credit(o.bandit, p, reward)

proc pullsOf*(o: OperatorSelector; idx: int): float = pullsOf(o.bandit, idx)
