## RFC-0016 INT-62 helper (not a test file): the six type x memory-op rows
## of `tsymex_0016_int62_packcost`, alone and packed into one accumulator.
## In a module of their own: walked from the test module, the `seq` rows
## declined `feGlobalRouteUnproved` on `unittest`'s globals.
import nelli/symex

type
  O3 = object
    n: int
    w: array[2, int]
  O4 = object
    n: int
    w: seq[int]
  V5 = object
    case k: bool
    of false: m: int
    of true: z: int
  O5 = object
    n: int
    w: V5

template r0(acc) =
  var x0: bool = t > u
  let c0 = x0
  acc = acc + ord(c0)
template r1(acc) =
  var x1: seq[int] = @[t, u]
  let c1 = x1
  acc = acc + (c1[1] + c1.len)
template r2(acc) =
  var x2: set[char] = {chr(t + 128)}
  let c2 = x2
  acc = acc + card(c2)
template r3(acc) =
  let o3 = O3(n: t)
  acc = acc + (o3.n + o3.w[1])
template r4(acc) =
  let o4 = O4(n: t)
  acc = acc + (o4.n + o4.w.len)
template r5(acc) =
  let o5 = O5(n: t)
  acc = acc + (o5.n + o5.w.m)

template rowProc(name, goal, body: untyped) {.dirty.} =
  proc name*(a, b: int8) =
    let t {.used.} = int(a)
    let u {.used.} = int(b)
    var acc = 0
    body
    if acc == goal: symexTarget("hit")

rowProc(p0, 1): r0(acc)
rowProc(p1, 9): r1(acc)
rowProc(p2, 1): r2(acc)
rowProc(p3, 9): r3(acc)
rowProc(p4, 9): r4(acc)
rowProc(p5, 9): r5(acc)
rowProc(pAll, 17):
  r0(acc); r1(acc); r2(acc); r3(acc); r4(acc); r5(acc)

