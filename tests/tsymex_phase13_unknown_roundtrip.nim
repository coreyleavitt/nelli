## Phase 13 cycle 5 — UNKNOWN verdict round-trip + settings
## rotation pins.
##
## The two slices:
## - (a) UNKNOWN save/load symmetry — same shape as cycle 4's
##   UNSAT pin, exercised on the `:unk` keyspace.
## - (b) The same (prog, target) yields different verdict-cache
##   entries under different settings: UNSAT under settings A
##   (queryRLimit=100) and UNKNOWN under settings B (queryRLimit=200)
##   coexist; loading under each settings returns the verdict
##   stored against THAT settings. Proves the content-addressing
##   correctly separates UNKNOWN from UNSAT and threads settings
##   into the key at the verdict layer.
import std/[unittest, options]
import proptest/symex
import proptest/db
import proptest/smt/[types, dsl]
import proptest/engine/types

let prog   = SymexProgram(body: mkBlock(@[]))
let target = tLabel("verdict")

# Two settings differing only in queryRLimit — produces distinct
# cache keys.
const settingsA = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 100'u, maxFrontierSize: 0, maxCallDepth: 3, maxLoopUnwind: 5))
const settingsB = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 200'u, maxFrontierSize: 0, maxCallDepth: 3, maxLoopUnwind: 5))

suite "symex Phase 13 cycle 5 — UNKNOWN round-trip + settings rotation":
  test "UNKNOWN save/load round-trip":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, prog, target,
                         defaultSymexSettings(), sfUnknown, errors)
    let loaded = loadSymexVerdictImpl(db, prog, target,
                                       defaultSymexSettings(), errors)
    check loaded == some(sfUnknown)

  test "settings rotate the verdict cache; UNSAT and UNKNOWN coexist":
    # Same prog + target. Two verdicts persisted against different
    # settings (different queryRLimit → different content-addressed
    # H). Each settings retrieves its own verdict.
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, prog, target, settingsA, sfUnsat, errors)
    saveSymexVerdictImpl(db, prog, target, settingsB, sfUnknown, errors)
    let loadedA = loadSymexVerdictImpl(db, prog, target, settingsA, errors)
    let loadedB = loadSymexVerdictImpl(db, prog, target, settingsB, errors)
    check loadedA == some(sfUnsat)
    check loadedB == some(sfUnknown)
