## RFC-fuzzer-nextgen R27 (code review, MEDIUM/design): the checkpoint
## load/save collaborator extracted from the `fuzz[T]` loop (`fuzz.nim`).
##
## Before this module, `fuzz[T]` threaded three loop-local variables
## (`checkpointActive`, `checkpointLoaded`, `checkpointState`) by hand
## through five separate sites: the cadence/wiring gate, the up-front load
## + decode, the frontier-stats/dictionary restore, the periodic
## mid-loop save, and the final end-of-campaign save. `CheckpointManager`
## owns that state directly instead — the loop now asks it three
## questions (`active`, `resumed`, `dueAt`) and calls two actions
## (`tryResume`, `save`) rather than re-deriving the gating condition at
## each site.
##
## **Decision vs I/O**: this module never imports `nelli/db` or touches an
## `ExampleDatabase` — the caller hands it plain `proc(): seq[byte]` /
## `proc(data: seq[byte])` closures at construction (typically thin wrappers
## around `db.loadSched(testId)`/`db.saveSched(testId, data)`). That keeps
## `CheckpointManager` constructible and testable with an in-memory `var
## seq[byte]` and no real database, filesystem, or `ExampleDatabase` plumbing
## — the review's "policy should be testable without touching the
## filesystem" standard.
##
## Byte-for-byte behavior preserved from the pre-R27 loop:
## - `active` is exactly the old `checkpointActive` gate: cadence > 0 AND
##   both closures non-nil (mirrors the loop's own `!= nil` convention for
##   `loadSchedImpl`/`saveSchedImpl` — see `FuzzSettings.checkpointCadence`'s
##   doc, "unset section degrades to empty").
## - `tryResume` is a no-op unless `active`; a decode failure (`ok: false`,
##   e.g. a version mismatch or corrupt blob) leaves `resumed` false — the
##   same cold-start-on-mismatch contract `decodeLearnedState` documents.
## - `dueAt(iter)` reproduces `iter mod cadence == 0` exactly, still gated on
##   `active` (an inactive manager is never due).
## - `save` is inert when inactive, matching the loop's own periodic-save and
##   final-save call sites, which were both already conditioned on
##   `checkpointActive`.

import ./coverage, ./bandit, ./fuzzir, ./learnedstate

type
  CheckpointManager* = object
    cadence: int
    loadImpl: proc(): seq[byte] {.closure.}
    saveImpl: proc(data: seq[byte]) {.closure.}
    loaded: bool
    state: LearnedState

proc newCheckpointManager*(cadence: int;
                           loadImpl: proc(): seq[byte] {.closure.} = nil;
                           saveImpl: proc(data: seq[byte]) {.closure.} = nil
                           ): CheckpointManager =
  ## `cadence <= 0` (the `SchedulingConfig.checkpointCadence` default), or
  ## either closure left `nil`, makes every method below an inert no-op.
  CheckpointManager(cadence: cadence, loadImpl: loadImpl, saveImpl: saveImpl)

proc active*(m: CheckpointManager): bool =
  m.cadence > 0 and m.loadImpl != nil and m.saveImpl != nil

proc tryResume*(m: var CheckpointManager) =
  ## Load + decode once, at campaign start. No-op when `not active`, when
  ## the backing store has nothing under this key (`loadImpl()` returns
  ## empty), or when decoding fails — in every one of those cases `resumed`
  ## stays false and the caller cold-starts, exactly as the pre-R27 loop did.
  if not active(m): return
  let raw = m.loadImpl()
  if raw.len == 0: return
  let decoded = decodeLearnedState(raw)
  if decoded.ok:
    m.loaded = true
    m.state = decoded.state

proc resumed*(m: CheckpointManager): bool = m.loaded

proc resumedState*(m: CheckpointManager): LearnedState =
  ## Only meaningful when `resumed`; zero-value `LearnedState()` otherwise.
  m.state

proc dueAt*(m: CheckpointManager; iter: int): bool =
  ## Whether iteration `iter` should persist a periodic checkpoint. Always
  ## false when `not active` — `iter mod 0` would be a runtime error, and an
  ## inactive manager must never appear due regardless of `iter`.
  active(m) and iter mod m.cadence == 0

proc save*(m: CheckpointManager; stats: FrontierStats; bandit: OperatorBandit;
          dict: Dictionary) =
  ## Persist the current learned state. Inert when `not active` — the
  ## caller can call this unconditionally at both the periodic-tick site
  ## and campaign end without re-checking `active` itself, same as the
  ## pre-R27 loop's two (identically-gated) call sites collapsed into one.
  if not active(m): return
  m.saveImpl(encodeLearnedState(newLearnedState(stats, bandit, dict)))
