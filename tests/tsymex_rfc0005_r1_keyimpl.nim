## RFC-0005 code review, round 1, R1-09 -- the cache key covers the source of
## the routines the SUT calls, not only the parsed IR.
##
## A cached `rsConfirmed` / `witnessUnsafe` / `:raised` is a fact about the real
## `fn`, which a replay ran, including the bodies the walker keeps out of the IR
## (a `{.symexOpaque.}` callee is a name there). Each `r1_keyimpl_*` module has
## the same SUT, `sutK`; only its opaque callee, or what that calls, or the
## checks it is compiled with, differ. RED before the fix: every key equal.
import std/unittest
import nelli
import nelli/symex
import nelli/smt/canonicalize
import ./r1_keyimpl_a as a
import ./r1_keyimpl_b as b
import ./r1_keyimpl_c as c
import ./r1_keyimpl_d as d
import ./r1_keyimpl_e as e
import ./r1_keyimpl_f as f

let ka = symexCacheKeyForFn(a.sutK, tLabel("k"))
let kb = symexCacheKeyForFn(b.sutK, tLabel("k"))
let kc = symexCacheKeyForFn(c.sutK, tLabel("k"))
let kd = symexCacheKeyForFn(d.sutK, tLabel("k"))
let ke = symexCacheKeyForFn(e.sutK, tLabel("k"))
let kf = symexCacheKeyForFn(f.sutK, tLabel("k"))

suite "R1-09: the key covers the opaque callees' source":

  test "native truth: the callees differ":
    var hitA, hitB = 0
    for x in -5 .. 5:
      if a.helperK(x) == 3: inc hitA
      if b.helperK(x) == 3: inc hitB
    check hitA == 1 and hitB == 1
    check a.helperK(2) == 3 and b.helperK(1) == 3

  test "a different opaque body is a different key":
    check ka != kb

  test "the same body, in another module, is the same key":
    check ka == kc

  test "a callee compiled under other checks is a different key":
    check ka != kd

  test "what the opaque callee calls is keyed too":
    check ke != kf
    check ke != ka

  test "the cache does not serve one body's verdict to the other":
    let db = inMemoryDatabase()
    let fa = symexFindAllWitnesses(a.sutK, db)
    checkpoint $fa
    check fa.len > 0
    let fb = symexFindAllWitnesses(b.sutK, db)
    for x in fb: check not x.fromCache
    let fc = symexFindAllWitnesses(c.sutK, db)
    var served = false
    for x in fc: served = served or x.fromCache
    check served
