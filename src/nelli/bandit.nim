## RFC-fuzzer-nextgen S2: a multi-armed bandit over the fuzz loop's mutation
## operators (MOpt in spirit — weight operator selection by RECENT admission
## yield, replacing the uniform `mod N` pick).
##
## Leaf module: depends only on `./rng`. Nothing engine-side imports back, so
## this stays independently testable like `fuzzir`'s mutators.
##
## **Algorithm: discounted UCB1** (Garivier & Moulines 2008), not plain UCB1
## and not MOpt's PSO swarm. Reasoning:
##
## - **Must explore.** UCB1's `mean + c*sqrt(ln(totalPulls)/pulls[arm])` bonus
##   term already guarantees this — an arm's bonus grows without bound as it
##   goes un-pulled while its siblings accumulate pulls, so it is eventually
##   re-tried no matter how poor its past yield. A never-yet-pulled arm gets
##   `+Inf` priority explicitly (see below), so exploration starts immediately
##   rather than waiting for the bonus term to grow large enough to win.
## - **Must adapt / handle non-stationarity.** Plain UCB1 keeps a running
##   mean over ALL history, which makes an operator's estimate sticky long
##   after the corpus outgrows the region it used to be productive in —
##   exactly the failure mode the RFC calls out. Discounted UCB1 multiplies
##   EVERY arm's accumulated pull-count and reward-sum by a decay factor
##   `banditDecay` on every selection tick (not just the chosen arm's), so
##   old evidence fades geometrically and the running estimate is dominated
##   by recent history — an effective sliding window without the memory cost
##   of literally storing one.
## - **Simpler than MOpt's swarm optimizer** while keeping its spirit
##   ("weight operators by recent admission yield, don't starve any of
##   them") — UCB1 is the standard, well-understood instantiation of that
##   spirit and needs no extra machinery (particle velocities/positions) the
##   fuzz loop would otherwise have to carry.
##
## **Never-starved cold arm, made exact by construction.** `pulls[i]` starts
## at `0.0` and decay only ever MULTIPLIES existing mass (`0.0 * gamma ==
## 0.0`, exactly, in IEEE 754) — so an arm literally never yet chosen has
## `pulls[i] == 0.0` on the nose, no epsilon-comparison needed. `chooseOperator`
## checks for this exactly and gives such arms absolute priority over any
## UCB1 score, uniformly among ties (RNG-driven, rejection-free via
## `rng.bounded`).

import ./rng
import std/math

type
  OperatorBandit* = object
    ## Per-arm discounted pull-count and reward-sum, plus the discounted
    ## grand total (kept in lockstep so `ln(totalPulls)` never drifts from
    ## `sum(pulls)`). Arm indices are the caller's — this module knows
    ## nothing about what an "operator" is (matches `fuzzir`'s mutators
    ## being agnostic of the fuzz loop that calls them).
    pulls: seq[float]
    rewardSum: seq[float]
    totalPulls: float

const
  banditDecay = 0.97
    ## RFC-fuzzer-nextgen R38: an internal tuning constant of the discounted-
    ## UCB1 algorithm itself, not a configuration knob — no `FuzzSettings`
    ## caller threads a value through, and no demand for varying it
    ## per-campaign has come up (contrast `SchedulingConfig.cullCadence`/
    ## `stallRounds`, which are genuinely load-bearing). Not `*`-exported;
    ## keep it that way rather than adding an unused config field just to
    ## make the export non-dead.
    ##
    ## Per-tick discount factor applied to every arm's (pulls, rewardSum)
    ## and to `totalPulls`, before that tick's pull is recorded. Chosen close
    ## to (but under) 1.0: an effective window of roughly `1/(1-decay)` ≈ 33
    ## recent pulls — long enough that a handful of unlucky rejections don't
    ## erase an operator's earned share, short enough that the schedule
    ## visibly re-weights within a few hundred iterations as the corpus
    ## matures (the same order of magnitude `fuzz`'s `maxIterations`-driven
    ## test campaigns run over).
  banditExploration = 1.4142135623730951 # sqrt(2), the canonical UCB1 constant
    ## RFC-fuzzer-nextgen R38: likewise an internal tuning constant — the
    ## textbook UCB1 exploration coefficient, not something a caller has
    ## ever needed to vary. Not `*`-exported; see `banditDecay`'s note.

proc newOperatorBandit*(numArms: int): OperatorBandit =
  ## `numArms` is the caller's arm count (5 IR mutators, or 6 with G5's I2S
  ## arm folded in — see `FuzzSettings.enableI2S`). Every arm starts fully
  ## cold (`pulls[i] == 0.0`), so the first `numArms` selections are exactly
  ## one pass over every arm in some RNG-determined order, before UCB1 ever
  ## compares scores.
  OperatorBandit(pulls: newSeq[float](numArms), rewardSum: newSeq[float](numArms))

proc chooseOperator*(b: var OperatorBandit; rng: var SplitMix64): int =
  ## Select the next arm to pull. Decays all bookkeeping first (the
  ## non-stationarity handling), then either uniformly picks among any
  ## still-cold (never-pulled, exactly `pulls[i] == 0.0`) arms, or the
  ## highest discounted-UCB1 score among warm arms (ties broken to the
  ## lowest index — deterministic, no RNG consumed on a warm tie). Records
  ## the pull (`pulls[arm] += 1`, `totalPulls += 1`) before returning, so a
  ## caller that never follows up with `credit` still correctly marks the
  ## arm as no-longer-cold and contributes to `totalPulls`.
  doAssert b.pulls.len > 0, "chooseOperator: bandit has no arms"
  for i in 0 ..< b.pulls.len:
    b.pulls[i] *= banditDecay
    b.rewardSum[i] *= banditDecay
  b.totalPulls *= banditDecay

  var coldArms: seq[int]
  for i in 0 ..< b.pulls.len:
    if b.pulls[i] == 0.0: coldArms.add i

  var arm: int
  if coldArms.len > 0:
    arm = coldArms[int(rng.bounded(uint64(coldArms.len)))]
  else:
    var bestScore = NegInf
    for i in 0 ..< b.pulls.len:
      let mean = b.rewardSum[i] / b.pulls[i]
      let bonus = banditExploration * sqrt(ln(max(b.totalPulls, 1.0)) / b.pulls[i])
      let score = mean + bonus
      if score > bestScore:
        bestScore = score
        arm = i

  b.pulls[arm] += 1.0
  b.totalPulls += 1.0
  arm

proc credit*(b: var OperatorBandit; arm: int; reward: float) =
  ## Fold `reward` (the fuzz loop passes `1.0` on an admitted/interesting
  ## outcome, and simply never calls this on a rejected/no-yield one — same
  ## effect as crediting `0.0`) into `arm`'s discounted reward-sum. Silently
  ## ignores an out-of-range `arm` (defensive; every real caller passes back
  ## exactly what `chooseOperator` returned).
  if arm < 0 or arm >= b.rewardSum.len: return
  b.rewardSum[arm] += reward

proc armCount*(b: OperatorBandit): int = b.pulls.len

proc banditSnapshot*(b: OperatorBandit): tuple[pulls, rewardSum: seq[float], totalPulls: float] =
  ## RFC-fuzzer-nextgen S6: read-only access to every field for checkpoint
  ## serialization (`nelli/learnedstate`) — `pulls`/`rewardSum`/`totalPulls`
  ## are otherwise private.
  (pulls: b.pulls, rewardSum: b.rewardSum, totalPulls: b.totalPulls)

proc restoreOperatorBandit*(pulls, rewardSum: seq[float], totalPulls: float): OperatorBandit =
  ## RFC-fuzzer-nextgen S6: the inverse of `banditSnapshot` — rebuild an
  ## `OperatorBandit` from a checkpoint's decoded per-arm state. The
  ## restored `armCount` is `pulls.len`; a caller resuming into a
  ## DIFFERENT arm count (e.g. `enableI2S`/`uniformHavoc` changed between
  ## runs, changing how many mutation arms exist) must detect that itself
  ## before calling this — arm INDEX is positional/meaningful, so a
  ## mismatched restore would silently misattribute one operator's
  ## learned reward to a different one.
  OperatorBandit(pulls: pulls, rewardSum: rewardSum, totalPulls: totalPulls)

proc pullsOf*(b: OperatorBandit; arm: int): float =
  ## Read-only introspection for tests: the arm's CURRENT discounted pull
  ## count (post-decay history, not a raw lifetime count).
  if arm < 0 or arm >= b.pulls.len: 0.0 else: b.pulls[arm]
