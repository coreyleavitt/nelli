## RFC-0016 D6 (0.10.0 review, design): `src/nelli/symex.nim` is the public
## facade only. Its implementation (the witness reader emitter, the cache
## record codecs, the replay footprint and routine table, the held-set walk,
## the driver bodies) lives in `src/nelli/smt/`.
##
## Two checks:
##   * the public API visible through `import nelli/symex` is exactly the
##     recorded list below. A move that drops a symbol, or leaves one behind
##     in an implementation module, fails to compile here;
##   * a line ceiling on the facade. It is a ratchet: it may only fall. The
##     number is what the facade honestly is after the move (the macro
##     signatures, the re-exports, the layer-2/3 helpers and the thin
##     driver macros that delegate to the `smt/` bodies).
import std/[unittest, strutils]
import nelli/symex

const facadeLineCeiling = 1500

const facadeSrc = staticRead("../src/nelli/symex.nim")

# Each name is checked with `declared`, which sees procs, macros, templates,
# types and consts alike.
static:
  template need(sym: untyped) =
    doAssert declared(sym), "public symbol dropped from nelli/symex: " & astToStr(sym)
  # defined by the facade
  need renderAsChoices
  need describeTarget
  need saveSymexNotesImpl
  need loadSymexNotesImpl
  need saveSymexWitnessImpl
  need loadSymexWitnessesImpl
  need saveSymexVerdictImpl
  need loadSymexVerdictImpl
  need saveSymexRaisedImpl
  need loadSymexRaisedImpl
  need toFindingStatus
  need forAllWithSymexSeeds
  need symexForAll
  need emitTyAndReader
  need symexOpaque
  need symexTransparent
  need replayEligible
  need replayInScope
  need replayReached
  need wireTarget
  need readTarget
  need targetLabelOf
  need emitReplayWitness
  need replayWitness
  need candidateLossy
  need symexFind
  need concolicCollect
  need concolicFlip
  need allRaiseFindings
  need assertCoveredBy
  need symexCacheKeyForFn
  need saveSymexWitness
  need loadSymexWitnesses
  need saveSymexVerdict
  need loadSymexVerdict
  need symexFindAllWitnesses
  need CachedWitness
  need CachedVerdict
  need CachedRaised
  need CachedNotes
  need SymexCoverageDefect
  # re-exported
  need z3FullVersion
  need replayExecutions
  need ReplayOutcome
  need ReplayResult
  need outcome
  need child
  need detail
  need runDependence
  need SymexFinding
  need SymexFindingStatus
  need FindingGap
  need FindingUndefined
  need trusted
  need SymexCaptureCtx
  need symexCapture
  need symexCaptureBegin
  need symexCaptureEnd
  need symexCaptureRecord
  need symexTarget
  need symexAssert
  need symexAssume
  need symexCacheKey
  need symexCacheKeyPrefix
  need symexWalkerVersion
  need renderAsChoicesVersion
  need canonicalize
  need cacheKeySat
  need cacheKeyUnsat
  need cacheKeyUnknown
  need cacheKeyRaised
  need verdictCacheMaxEntries
  # module re-exports (`export db`, `export dsl`, `export choice`)
  need ExampleDatabase
  need SymexSettings
  need ChoiceNode

suite "D6: symex.nim is the facade":
  test "the public API is intact (checked at compile time above)":
    check true

  test "the facade stays under its line ceiling (ratchet: may only fall)":
    let n = facadeSrc.countLines
    check n <= facadeLineCeiling
    if n > facadeLineCeiling:
      echo "symex.nim is ", n, " lines; ceiling ", facadeLineCeiling
