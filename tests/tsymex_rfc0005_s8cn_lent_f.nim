## RFC-0005 slice S8cn -- a `lent` `for` loop, and a `let` over a container, with
## a write during the variable's life.
##
## The walk binds a loop variable or a `let` to the value read where it stands.
## Natively `items` over a seq or an openArray, and a Table's `values`, yield the
## element's own memory, so a write to the container in the body is seen through
## the variable. `let c = s` shares under `--mm:refc` always and under orc or arc
## when cursor inference proves it, which turns on the whole routine:
## `tsymex_rfc0005_s8cn_lentnative` pins that, on each memory manager. Both are
## declined when the body (a callee, a pointer, a global alias included) may
## write; the exact model is for RFC-0016. The forms Nim copies on every setting
## stay decided: scalar elements through `pairs`, an array's `items`, a Table's
## `pairs`. Every label runs natively.
##
## RFC-0005 S8cm: part 6 of 6 of this suite, with `tsymex_rfc0005_s8cn_lent`,
## `tsymex_rfc0005_s8cn_lent_b`, `tsymex_rfc0005_s8cn_lent_c`,
## `tsymex_rfc0005_s8cn_lent_d`, `tsymex_rfc0005_s8cn_lent_e`. Split so that
## each part compiles and runs in under 60 s on the Windows legs (the whole
## file took 95 s).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template decided(fn: typed; lbl: static string; want: typed) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == want
    var live = false
    for n in ns:
      if lbl in hits(fn(n)): live = true
    if want == sxUnsat: check not live
    else: check live

template guardN(): untyped {.dirty.} =
  if n > 1000 or n < -1000 or n == 99: return
proc lBefore(n: int) =
  guardN()
  var s = @[n]
  s[0] = n + 1
  let c = s
  if c[0] == n + 1: symexTarget("lb_live")
  else: symexTarget("lb_dead")
proc lFormal(s0: seq[int]) =
  # A formal, so a pointer may reach it; nothing here writes through one, and
  # the target's own runtime call is not a write.
  if s0.len != 1 or s0[0] > 1000 or s0[0] < -1000: return
  let c = s0
  if c[0] == s0[0]: symexTarget("lc_live")
  else: symexTarget("lc_dead")
proc lVar(n: int) =
  guardN()
  var s = @[n]
  var c = s
  s[0] = 99
  if c[0] == n: symexTarget("va_live")
  if c[0] == 99: symexTarget("va_dead")
proc lArr(n: int) =
  guardN()
  var a = [n, 0]
  let c = a
  a[0] = 99
  if c[0] == n: symexTarget("ar_live")
  if c[0] == 99: symexTarget("ar_dead")

suite "S8cn: `let` over a container with a write in its life":
  test "no write after it, a `var`, an array: decided":
    decided(lBefore, "lb_live", sxSat); decided(lBefore, "lb_dead", sxUnsat)
    decided(lVar, "va_live", sxSat); decided(lVar, "va_dead", sxUnsat)
    check symexFind(lFormal, tLabel("lc_live")).status == sxSat
    check symexFind(lFormal, tLabel("lc_dead")).status == sxUnsat
    decided(lArr, "ar_live", sxSat); decided(lArr, "ar_dead", sxUnsat)
