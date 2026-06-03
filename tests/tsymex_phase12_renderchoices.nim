## Phase 12 cycle 6 — `renderAsChoices` collection encoding matches
## the `lists` / `tables` / `sets` strategy contract (per-element
## continue-boolean, no length prefix) AND emits deterministically
## for hash-keyed collections.
##
## Why this matters: a witness's choice sequence is stored in the
## example DB and later fed back into the strategy via `DataSource`
## at replay time. The strategies (strategy.nim:406-475) read a
## per-element `drawBoolean(0.9)` to decide continue-vs-stop. The
## old length-prefix encoding from Phase 5 was incompatible — a
## latent bug that never surfaced because no test rode a collection
## witness through a replay-with-strategy path.
##
## Spec correction logged at the same time: the plan v3 conflated
## this with the walker-side `RawWitness` readers (`readSeqInt`,
## `readTableStrInt`, `readSetInt`); those are on an independent
## codegen path (`emitTyAndReader`) and never crossed the
## ChoiceNode boundary. They stay untouched.
import std/[unittest, sets, tables]
import proptest/symex
import proptest/choice
import proptest/int128
from proptest/smt/canonicalize import renderAsChoicesVersion

suite "symex Phase 12 cycle 6 — renderAsChoices collection encoding":
  test "seq[int]: per-element continue-bool, terminated by stop-bool":
    let cs = renderAsChoices(@[5, 9, 13])
    # Three iterations of (continue=true, element) plus one
    # stop-bool — total 3*2 + 1 = 7 nodes.
    check cs.len == 7
    check cs[0].kind == ckBoolean and cs[0].boolVal == true
    check cs[1].kind == ckInteger and cs[1].intVal == toInt128(5)
    check cs[2].kind == ckBoolean and cs[2].boolVal == true
    check cs[3].kind == ckInteger and cs[3].intVal == toInt128(9)
    check cs[4].kind == ckBoolean and cs[4].boolVal == true
    check cs[5].kind == ckInteger and cs[5].intVal == toInt128(13)
    check cs[6].kind == ckBoolean and cs[6].boolVal == false

  test "HashSet[int]: encoding deterministic across insertion order":
    # Cache keys are content-addressed on the choice sequence;
    # `HashSet` iteration order is undefined. Two sets with the
    # same members built via different `incl` orders must render
    # to byte-identical choice sequences.
    var a = initHashSet[int]()
    a.incl(7); a.incl(3); a.incl(11)
    var b = initHashSet[int]()
    b.incl(11); b.incl(7); b.incl(3)
    let ca = renderAsChoices(a)
    let cb = renderAsChoices(b)
    check ca.len == cb.len
    for i in 0 ..< ca.len:
      check ca[i].kind == cb[i].kind
      if ca[i].kind == ckBoolean:
        check ca[i].boolVal == cb[i].boolVal
      elif ca[i].kind == ckInteger:
        check ca[i].intVal == cb[i].intVal
    # And the integers come out sorted ascending.
    check ca[1].intVal == toInt128(3)
    check ca[3].intVal == toInt128(7)
    check ca[5].intVal == toInt128(11)

  test "Table[string,int]: encoding deterministic across insertion order, sorted by key":
    var a = initTable[string, int]()
    a["b"] = 20; a["a"] = 10; a["c"] = 30
    var b = initTable[string, int]()
    b["c"] = 30; b["a"] = 10; b["b"] = 20
    let ca = renderAsChoices(a)
    let cb = renderAsChoices(b)
    check ca.len == cb.len
    for i in 0 ..< ca.len:
      check ca[i].kind == cb[i].kind
    # Per-entry pattern: bool(true), key-string, value-int. Three
    # entries plus stop-bool → 3*3 + 1 = 10 nodes. Keys come out
    # sorted: a, b, c.
    check ca.len == 10
    check ca[1].kind == ckString and ca[1].strVal == "a"
    check ca[2].intVal == toInt128(10)
    check ca[4].kind == ckString and ca[4].strVal == "b"
    check ca[5].intVal == toInt128(20)
    check ca[7].kind == ckString and ca[7].strVal == "c"
    check ca[8].intVal == toInt128(30)
    check ca[9].kind == ckBoolean and ca[9].boolVal == false

  test "seq[seq[int]] nests under continue-bool recursion":
    # Outer list of two inner lists; inner lists have 1 and 2
    # elements. The full node count:
    #   outer-cont(true), inner1: [cont(true), 5, cont(false)] (3)
    #   outer-cont(true), inner2: [cont(true), 9, cont(true), 13, cont(false)] (5)
    #   outer-cont(false)
    # Total: 1 + 3 + 1 + 5 + 1 = 11.
    let cs = renderAsChoices(@[@[5], @[9, 13]])
    check cs.len == 11
    check cs[0].boolVal == true   # outer continue
    check cs[1].boolVal == true   # inner1 continue
    check cs[2].intVal == toInt128(5)
    check cs[3].boolVal == false  # inner1 stop
    check cs[4].boolVal == true   # outer continue
    check cs[5].boolVal == true   # inner2 continue
    check cs[6].intVal == toInt128(9)
    check cs[7].boolVal == true   # inner2 continue
    check cs[8].intVal == toInt128(13)
    check cs[9].boolVal == false  # inner2 stop
    check cs[10].boolVal == false # outer stop

  test "renderAsChoicesVersion is \"2\" post-cycle":
    # Cache-key contract: cycle 6 bumps renderAsChoicesVersion to
    # invalidate stale length-prefixed collection witnesses. This
    # test pins the constant so any unintended rotation lights up.
    check renderAsChoicesVersion == "2"
