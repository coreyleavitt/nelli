## Shared bootstrap circuit-breaker fold (RFC-fuzzer-nextgen E4a / R29a).
##
## `BootstrapBreaker` started life in `workerproto.nim` (RFC §Open-items:
## "N consecutive dead-before-first-read spawns abort the campaign with a
## construction-not-reentrant diagnostic"). It is pure — a fold over a
## spawn pool's dead-before-first-read history, with zero dependency on any
## `fuzz.nim` type — but `workerproto.nim` itself `import`s `./fuzz` (for
## the platform-independent wire-protocol pieces that DO need `fuzz.nim`'s
## `Observation`/`CrashInfo`), so `fuzz.nim` cannot import `workerproto`
## back without a cycle. `Orchestrator.run` (fuzz.nim) therefore used to
## re-implement the breaker's increment/threshold/reset/diagnostic logic
## inline, kept in sync with this module's copy BY HAND — exactly the
## "collisions limited to shared helpers" anti-pattern the rest of this RFC
## avoids elsewhere.
##
## Living in its own leaf module (no dependents of its own — not even
## `std/tables`) lets both `workerproto.nim` (which re-exports it, so its
## own public surface is unchanged) and `fuzz.nim` (which imports it
## directly) share the ONE fold, closing the cycle without either side
## reimplementing anything. Same technique `crashinfo.nim` established for
## `CrashKind`/`CrashInfo`.

type
  BootstrapBreaker* = object
    ## RFC §Open-items / E4a: pure fold over a spawn pool's
    ## dead-before-first-read history. `threshold <= 0` disables the
    ## breaker entirely (never trips, mirrors `Orchestrator.stormWindow`'s
    ## `0 == off` convention) — the same additive-knob polarity the rest of
    ## this RFC's circuit breakers use.
    threshold*: int
    consecutiveDeaths*: int
      ## How many spawns IN A ROW died before answering their first read.
      ## Resets to 0 the moment ANY spawn's first read succeeds — a later
      ## healthy worker proves reconstruction IS reentrant after all, so an
      ## earlier transient run of deaths should not keep counting against a
      ## now-recovered pool.
    tripped*: bool
    diagnostic*: string
      ## Empty until `tripped`; the "construction-not-reentrant" message a
      ## caller/driver surfaces verbatim. Distinct wording from
      ## `RespawnStormError.msg` (fuzz.nim) — a caller must be able to tell
      ## "no worker of the pool could ever start" apart from "workers start
      ## fine but keep dying the same way," even from the message alone.

proc newBootstrapBreaker*(threshold: int): BootstrapBreaker =
  BootstrapBreaker(threshold: threshold)

proc recordDeadBeforeFirstRead*(b: var BootstrapBreaker) =
  ## Fold in one spawn whose worker died (or the spawn itself failed)
  ## before ever answering its first read. Once tripped, further deaths
  ## are still counted (so `consecutiveDeaths` stays an honest running
  ## total) but do not change the diagnostic.
  inc b.consecutiveDeaths
  if b.threshold > 0 and b.consecutiveDeaths >= b.threshold and not b.tripped:
    b.tripped = true
    b.diagnostic = "construction-not-reentrant: " & $b.threshold &
      " consecutive dead-before-first-read worker spawns"

proc recordFirstReadSucceeded*(b: var BootstrapBreaker) =
  ## Fold in one spawn whose worker answered its first read — the pool is
  ## provably able to start workers again. Resets the consecutive-death
  ## streak AND un-trips the breaker (a caller/driver polling `tripped`
  ## after this sees `false` again).
  b.consecutiveDeaths = 0
  b.tripped = false
  b.diagnostic = ""
