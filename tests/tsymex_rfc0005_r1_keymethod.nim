## RFC-0005 code review, round 1, R1-11 -- the cache and DB macros key a
## method-dispatch SUT as `symexFindAllWitnesses` does.
##
## `symexFind`, `symexFindAllWitnesses` and the concolic entries first emit
## `methodPrelude`, which registers the methods the SUT calls in the caller's
## scope, then expand again; the parse then dispatches each method call over
## its overrides. `symexCacheKeyForFn`, `saveSymexWitness`,
## `loadSymexWitnesses`, `saveSymexVerdict` and `loadSymexVerdict` parsed
## without it, so expanded before any other entry they keyed the undispatched
## (declined) program: a key `symexFindAllWitnesses` never writes. Which key
## they produced depended on the order the macros were expanded in.
##
## ORDER MATTERS IN THIS FILE: the first symex macro expanded here must be
## `symexCacheKeyForFn` (below), before anything has registered `setR11`.
import std/[unittest, options]
import nelli
import nelli/symex
import nelli/smt/canonicalize

type
  ShapeR11 = ref object of RootObj
  SquareR11 = ref object of ShapeR11

method setR11(o: ShapeR11; a: var int) {.base.} = a = 5
method setR11(o: SquareR11; a: var int) = a = 6

proc sutR11(k: int) =
  let o: ShapeR11 = SquareR11()
  var x = k
  o.setR11(x)
  if x != 6: symexTarget("r11_dead")

# The FIRST expansion of a symex macro in this module.
let keyFirst = symexCacheKeyForFn(sutR11, tLabel("r11_dead"))
let verdictFirst = block:
  let db = inMemoryDatabase()
  loadSymexVerdict(db, sutR11, tLabel("r11_dead"), defaultSymexSettings())

suite "R1-11: the cache macros register methods before keying":

  test "native truth: the override runs, so x is 6 and the label is dead":
    var x = 0
    let o: ShapeR11 = SquareR11()
    o.setR11(x)
    check x == 6

  test "symexFindAllWitnesses decides the label through the dispatch":
    let fs = symexFindAllWitnesses(sutR11, inMemoryDatabase())
    var seen = false
    for f in fs:
      if f.targetDesc == "label(\"r11_dead\")" and f.status == sfUnsat:
        seen = true
    checkpoint $fs
    check seen

  test "symexCacheKeyForFn, expanded first, is the key symexFindAllWitnesses writes":
    let db = inMemoryDatabase()
    let fs = symexFindAllWitnesses(sutR11, db)
    checkpoint $fs
    check db.loadPrimaryWithMeta(keyFirst & cacheKeyUnsat).len == 1

  test "a later expansion gives the same key":
    check symexCacheKeyForFn(sutR11, tLabel("r11_dead")) == keyFirst

  test "the verdict macros read what symexFindAllWitnesses wrote":
    check verdictFirst.isNone   # an empty database, read before the run
    let db = inMemoryDatabase()
    discard symexFindAllWitnesses(sutR11, db)
    let v = loadSymexVerdict(db, sutR11, tLabel("r11_dead"),
                             defaultSymexSettings())
    check v.isSome and v.get.status == sfUnsat
