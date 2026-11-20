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
##     number is what the facade honestly is after the move: 961 lines were
##     the 6186-line file's remainder (the macro signatures and their doc
##     comments, the re-exports, `forAllWithSymexSeeds`/`symexForAll`, the
##     small cache macro forms, and the `nelliVmAliasAudit` self-audit block
##     that now also audits the moved modules). Ceiling 970, a little over,
##     so a doc-comment edit is not a failure; a new body in the facade is.
##     RFC-0016 INT-34 C1 folded the four DB macro bodies into one skeleton:
##     940 lines, ceiling 950.
import std/[unittest, strutils]
import audit_scan_utils
import nelli/symex
import nelli   ## the union of both: a name hidden here is hidden under each

const facadeLineCeiling = 950

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

# R2-3 (0.10.0 review, round 2): the walker's internals are not facade API. The
# value core (`SymVal`, its helpers), the hook table, the per-run threadvars
# and their resets live in the runtime-family leaves, which the family imports
# directly; `runtime.nim` no longer re-exports them wholesale.
static:
  template hidden(sym: untyped) =
    doAssert not declared(sym),
      "walker internal leaked through the facade: " & astToStr(sym)
  hidden lowerHooks
  hidden currentWalkCtxPtr
  hidden currentLowerSinks
  hidden resetWalkState
  hidden resetLoweringSink
  hidden SymVal
  hidden plainEnglishSymValKind
  hidden splitNeedle

suite "D6: symex.nim is the facade":
  test "the public API is intact (checked at compile time above)":
    check true

  test "the facade stays under its line ceiling (ratchet: may only fall)":
    let n = facadeSrc.countLines
    check n <= facadeLineCeiling
    if n > facadeLineCeiling:
      echo "symex.nim is ", n, " lines; ceiling ", facadeLineCeiling

# R5-H1 (0.10.0 review, round 5): `when defined(nelliVmAliasAudit):` is
# semantically checked only under that define, so pruning an "unused" file-level
# import (`std/os`) broke the audit block while every ordinary compile stayed
# green. This pin needs no define: it reads the block's text and requires that
# each std module whose symbols the block names is imported somewhere in the
# file.
#
# It is a textual approximation (R6-5): it reads `codeOf` (comments and string
# bodies removed, so prose naming a symbol never counts), and the symbol map
# below lists only what the block is known to use. The real guard is the
# `s8ab_letaudit` leg, which compiles the block under the define in CI.
proc gatedBlock(src0: string): string =
  let src = codeOf(src0)
  let marker = "when defined(nelliVmAliasAudit):"
  let at = src.find(marker)
  if at < 0: return ""
  var lines: seq[string]
  for l in src[at + marker.len .. ^1].splitLines()[1 .. ^1]:
    if l.len > 0 and l[0] notin {' ', '#'}: break   # the next column-0 code line ends the block
    lines.add l
  lines.join("\n")

proc importsStd(src0, module: string): bool =
  for l in codeOf(src0).splitLines:
    let s = l.strip
    if (s.startsWith("import std/") or s.startsWith("from std/")) and module in s.split({'/', '[', ']', ',', ' ', '\t'}):
      return true

suite "D6: the self-audit block's imports resolve without the define":
  test "every std module the nelliVmAliasAudit block names is imported":
    let blk = gatedBlock(facadeSrc)
    check blk.len > 0
    # (module, the symbols of it a guarded block could be using)
    let needs = [("os", @["parentDir", "extractFilename", "joinPath", "splitFile", "splitPath", "fileExists", " / "]),
                 ("algorithm", @["sort(", "sorted(", "reversed("]),
                 ("importutils", @["privateAccess"]),
                 ("sequtils", @["mapIt", "filterIt", "toSeq"])]
    for (module, syms) in needs:
      for s in syms:
        if s in blk:
          check importsStd(facadeSrc, module)
          if not importsStd(facadeSrc, module):
            echo "the nelliVmAliasAudit block uses ", s, " but nothing imports std/", module
