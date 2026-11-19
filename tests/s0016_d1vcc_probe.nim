## RFC-0016 D1 stack-frame probe. The shape of `tsymex_0016_k4a_dispatch`
## (as one file): many `symexFind` expansions in ONE module top level, so
## every expansion's temporaries share the frame of `NimMainModule`. Each SUT
## calls a chain of routines, so each expansion's IR carries a stamped body
## per routine. Built and run by `tsymex_0016_d1vcc_frame` under a reduced
## stack; not a test itself.
import nelli
import nelli/symex

proc h1(k: int): int =
  result = k + 1

proc h2(k: int): int =
  result = h1(k) + 2

proc h3(k: int): int =
  result = h2(k) + 3

proc h4(k: int): int =
  result = h3(k) + 4

proc h5(k: int): int =
  result = h4(k) + 5

proc h6(k: int): int =
  result = h5(k) + 6

proc h7(k: int): int =
  result = h6(k) + 7

proc h8(k: int): int =
  result = h7(k) + 8

proc h9(k: int): int =
  result = h8(k) + 9

proc h10(k: int): int =
  result = h9(k) + 10

proc h11(k: int): int =
  result = h10(k) + 11

proc h12(k: int): int =
  result = h11(k) + 12

proc h13(k: int): int =
  result = h12(k) + 13

proc h14(k: int): int =
  result = h13(k) + 14

proc h15(k: int): int =
  result = h14(k) + 15

proc h16(k: int): int =
  result = h15(k) + 16

proc h17(k: int): int =
  result = h16(k) + 17

proc h18(k: int): int =
  result = h17(k) + 18

proc h19(k: int): int =
  result = h18(k) + 19

proc h20(k: int): int =
  result = h19(k) + 20

proc h21(k: int): int =
  result = h20(k) + 21

proc h22(k: int): int =
  result = h21(k) + 22

proc h23(k: int): int =
  result = h22(k) + 23

proc h24(k: int): int =
  result = h23(k) + 24

proc sut(k: int) =
  if h24(k) == 21: symexTarget("hit")

template site() =
  block:
    let r = symexFind(sut, tLabel("hit"))
    if r.status != sxSat: quit("not sat", 2)

site(); site(); site(); site()
site(); site(); site(); site()
site(); site(); site(); site()
site(); site(); site(); site()
echo "ok"
