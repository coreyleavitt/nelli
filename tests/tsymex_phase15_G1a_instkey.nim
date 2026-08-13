## Phase 15 — Cluster G, cycle G1a: generic instantiation key.
##
## LOCKED DECISION (see RFC-phase15-reconciliation.md §F Cluster G): generic
## procs already symex via PARSE-TIME monomorphization (`ensureProcRegistered`
## + `gatherTypeSubst` + `monomorphize`). Cluster G does NOT add an
## `isGenericCall` IR. G1a fixes the REAL latent bug: `ensureProcRegistered`
## keyed `ctx.procs` by the BARE proc name and short-circuited on
## `name in ctx.procs`, so a SECOND instantiation of the same generic (at a
## different `T`) collided with the first and was silently dropped — dispatch
## then reused the FIRST (wrong) monomorphized body for the second call.
##
## For an identity generic (`proc id[T](x:T):T = x`) the collision is invisible
## because the monomorphized body is structurally the same at every `T`. The
## bug only becomes OBSERVABLE when the monomorphized body genuinely DIFFERS by
## instantiation type — e.g. `proc szof[T](x:T):int = sizeof(T)`, whose result
## is `1` at `int8` but `8` at `int64`. Under the bare-name collision the second
## instantiation reuses the first sig, so `szof(b)` returns the WRONG constant
## and the conjunction is `sxUnsat` instead of `sxSat`.
##
## G1a replaces the bare-name key with an ADR-0008 D2 instantiation key
## (`name#<bodyHash>#<sorted-concrete-type-tuple>`), used IDENTICALLY at
## registration AND at the call-site `mkCall` callee name, so two
## instantiations register as DISTINCT `ProcSig`s and dispatch resolves each.
import std/unittest
import nelli/symex

# Monomorphized body DIFFERS by instantiation type: `sizeof(T)` is a per-T
# constant the semchecker bakes in (1 at int8, 8 at int64). This is the
# load-bearing collision demonstrator.
proc szof[T](x: T): int = sizeof(T)

proc bothTypes(a: int8, b: int64) =
  # szof@int8 = 1, szof@int64 = 8. If the int64 call collides onto the int8
  # sig (the bare-name bug), `szof(b)` yields 1 and the conjunction is UNSAT.
  if szof(a) == 1 and szof(b) == 8:
    symexTarget("found")

# Reversed registration order: int64 instantiation registers first. Confirms
# the fix is order-independent (collision would bite whichever registers 2nd).
proc bothTypesRev(a: int64, b: int8) =
  if szof(a) == 8 and szof(b) == 1:
    symexTarget("found")

# Two same-shape generic calls at the SAME type (int8) must still share/cache
# correctly — no regression: same (proc, type) reuses one ProcSig.
proc sameTypeTwice(a: int8, b: int8) =
  if szof(a) == 1 and szof(b) == 1 and a == 4'i8 and b == 7'i8:
    symexTarget("found")

# An identity generic at two types — both must dispatch (the identity body is
# the same at every T, but registration must still produce distinct entries so
# the witnesses are well-typed).
proc id[T](x: T): T = x

proc idTwoTypes(a: int8, b: int64) =
  if id(a) == 5'i8 and id(b) == 9_000_000_000'i64:
    symexTarget("found")

suite "symex Phase 15 G1a — generic instantiation key (bare-name collision)":
  test "same generic at two types both dispatch (szof@int8 and szof@int64)":
    let r = symexFind(bothTypes, tLabel("found"))
    check r.status == sxSat

  test "collision fix is registration-order-independent":
    let r = symexFind(bothTypesRev, tLabel("found"))
    check r.status == sxSat

  test "same generic at the same type twice shares one ProcSig (no regression)":
    let r = symexFind(sameTypeTwice, tLabel("found"))
    check r.status == sxSat
    check r.witness[0] == 4'i8
    check r.witness[1] == 7'i8

  test "identity generic at two types both dispatch with correct witnesses":
    let r = symexFind(idTwoTypes, tLabel("found"))
    check r.status == sxSat
    check r.witness[0] == 5'i8
    check r.witness[1] == 9_000_000_000'i64
