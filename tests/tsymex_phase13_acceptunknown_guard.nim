## Phase 13 cycle 6 — `acceptUnknownAsCovered` integration guard.
##
## Defense-in-depth: placed BEFORE the Layer 1 wire changes in
## cycles 7-9 so a wire regression at the impl call site (e.g.,
## someone accidentally inlines the cache-key derivation in a way
## that touches `acceptUnknownAsCovered`) fires immediately.
##
## The Phase 10 contract: `acceptUnknownAsCovered` influences the
## verifier's interpretation of UNKNOWN (`assertCoveredBy` raise/
## pass) but NEVER changes the walker's output or the cached
## verdict. The canonicalize-level test at
## `tsymex_canonicalize.nim:285` pins this in `canonicalize(s)`;
## this integration test pins it at the call-site flow through
## `saveSymexVerdictImpl` and `loadSymexVerdictImpl`.
import std/[unittest, options]
import proptest/symex
import proptest/db
import proptest/smt/[types, dsl]
import proptest/engine/types

let prog   = SymexProgram(body: mkBlock(@[]))
let target = tLabel("verdict")

const settingsStrict = SymexSettings(
  integerSemantics: isOptimised, queryRLimit: 0'u,
  maxFrontierSize: 0, maxCallDepth: 3, maxLoopUnwind: 5,
  acceptUnknownAsCovered: false)
const settingsLax = SymexSettings(
  integerSemantics: isOptimised, queryRLimit: 0'u,
  maxFrontierSize: 0, maxCallDepth: 3, maxLoopUnwind: 5,
  acceptUnknownAsCovered: true)

suite "symex Phase 13 cycle 6 — acceptUnknownAsCovered integration guard":
  test "verdict cache returns identically across the acceptUnknownAsCovered toggle":
    # Save UNKNOWN under the strict (false) settings.
    # Load under the lax (true) settings — should HIT, since
    # `acceptUnknownAsCovered` is excluded from the cache key.
    # If a wire regression accidentally inlined the key derivation
    # to include this field, the load would miss.
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, prog, target,
                         settingsStrict, sfUnknown, errors)
    let loadedLax = loadSymexVerdictImpl(db, prog, target,
                                          settingsLax, errors)
    let loadedStrict = loadSymexVerdictImpl(db, prog, target,
                                             settingsStrict, errors)
    check loadedLax == some(sfUnknown)
    check loadedStrict == some(sfUnknown)
    check loadedLax == loadedStrict
