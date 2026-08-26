## Shared typed crash identity (RFC-fuzzer-nextgen E1 C1 / U0).
##
## `CrashKind`/`CrashInfo` started life in `fuzz.nim` as the taxonomy
## `fuzz`'s `Worker`/`Observation` machinery matches crashes on (dedup,
## oracle logic, and reporting key on `kind`, never parse `message` prose —
## `message` is a human rendering ONLY, DERIVED from the variant below).
##
## RFC-fuzzer-nextgen U0 routes `forAll`'s property invocation through the
## same Defect-catching boundary `fuzz`'s in-process `Worker` uses, so a
## property `Defect` becomes a shrinkable falsification carrying the SAME
## typed crash identity `fuzz` reports — "one engine," two front doors, all
## the way down to crash identity, not just execution. That requires
## `engine/*` (which `fuzz.nim` itself imports — `fuzz.nim` sits ABOVE the
## engine in the dependency graph) to reference this type, so it lives in
## its own leaf module with no dependents of its own. `fuzz.nim` re-exports
## it so `import nelli/fuzz`'s existing `CrashInfo`/`CrashKind`/`ckException`
## etc. surface is unchanged — this is a pure move, not a new type.

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
