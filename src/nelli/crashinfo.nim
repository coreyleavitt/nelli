## Shared typed crash identity (RFC-fuzzer-nextgen E1 C1 / U0).
##
## `CrashKind`/`CrashInfo` started life in `fuzz.nim` as the taxonomy
## `fuzz`'s `Worker`/`Observation` machinery matches crashes on (dedup,
## oracle logic, and reporting key on `kind`, never parse `message` prose —
## `message` is a human rendering ONLY, DERIVED from the variant below).
##
## RFC-fuzzer-nextgen U0 gives `forAll`'s property invocation the SAME typed
## crash identity `fuzz` reports on a Defect — a property `Defect` becomes a
## shrinkable falsification carrying `kind`/`defect` alongside its message,
## the same shape `fuzz`'s `Observation.crash` uses. It does NOT route
## `forAll` through `fuzz`'s in-process `Worker` boundary itself: that
## boundary's `observeInProcess` unconditionally resets coverage/cmp-log
## state on every call (per-run isolation, by design), which would corrupt
## `forAll`'s own before/after coverage-delta bookkeeping across its own
## call sequence. So the TYPE is shared, not the execution boundary —
## `forAll`'s catch sites (`engine/eval.nim`'s `evalReplay`,
## `engine/phases.nim`'s `explicitExamplesPhase`/`randomPhase`) build
## `CrashInfo` independently of `fuzz.nim`'s `observeInProcess`, via the
## shared `classifyDefect` helper below — the classification LOGIC is
## deduplicated across those sites, but each still catches its own Defect
## at its own call boundary. That requires `engine/*` (which `fuzz.nim`
## itself imports — `fuzz.nim` sits ABOVE the engine in the dependency
## graph) to reference this type, so it lives in its own leaf module with
## no dependents of its own. `fuzz.nim` re-exports it so `import
## nelli/fuzz`'s existing `CrashInfo`/`CrashKind`/`ckException` etc.
## surface is unchanged — this is a pure move, not a new type.

type
  CrashKind* = enum
    ## The taxonomy `Observation.crash` (fuzz) and `Report.crash` (engine,
    ## U0) are both matched on.
    ckException  ## in-process: a Nim `Defect`/`CatchableError` propagated
                 ## out of the property (includes a failed `doAssert`).
    ckSignal     ## external: the child died on a signal (SIGSEGV, SIGABRT, ...).
    ckExitCode   ## external: the child exited with a nonzero/bug status code.
    ckWinException ## external, Windows: a structured-exception code from a
                    ## crashed child. Not populated until the Windows worker
                    ## (Track E) lands — the case exists so `CrashInfo` doesn't
                    ## need another breaking shape change then.

  CrashInfo* = object
    ## Typed crash identity (round-1 design fix, RFC-fuzzer-nextgen §Appendix
    ## C): before this, crash identity/dedup was a stringly-typed `message`
    ## grep. `message` is a human rendering DERIVED from the variant below —
    ## it is never itself matched on. Common field precedes the `case` per
    ## Nim's object-variant rule.
    message*: string
    case kind*: CrashKind
    of ckException:    defect*: string      ## the raising Nim Defect/exception name
    of ckSignal:        signal*: int
    of ckExitCode:      exitCode*: int
    of ckWinException:  code*: uint32

proc classifyDefect*(e: ref Defect, activity = "crashed"): CrashInfo =
  ## R30: the one place every in-process Defect-catch site in `engine/*`
  ## builds its `CrashInfo` (and derived message) — `engine/eval.nim`'s
  ## `evalReplay` (both its strategy-generation and property-call catch
  ## arms) and `engine/phases.nim`'s `explicitExamplesPhase`/`randomPhase`.
  ## Before this, each site hand-built `CrashInfo(kind: ckException, defect:
  ## $e.name, ...)` with its own copy of the message format; two more sites
  ## outside `engine/*` (`fuzz.nim`'s `fuzzOnce`/`fuzzOnceIR`) had already
  ## drifted to building no `CrashInfo` at all.
  ##
  ## `activity` is the one axis observable output legitimately differs on
  ## across call sites: what was executing when the Defect propagated —
  ## `"crashed"` (the default) for a property call, `"strategy crashed"` for
  ## a Defect raised out of strategy generation itself (before a value was
  ## even assigned). Everything else — `kind: ckException`, `defect: $e.name`,
  ## and the `"<activity>: <defect>: <msg>"` message shape — is identical by
  ## construction, so it can no longer drift between sites.
  let msg = activity & ": " & $e.name & ": " & e.msg
  CrashInfo(kind: ckException, defect: $e.name, message: msg)
