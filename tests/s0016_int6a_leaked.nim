## RFC-0016 int6-a. A module imported under `{.push rangeChecks: off.}` by the
## first import to reach it (`tsymex_0016_int6a_leak` and its fallback
## suites): natively it is compiled with the push, so `leakConv(300)` keeps 300
## and does not raise.

type LR* = range[0 .. 10]

proc leakConv*(v: int): int = int(LR(v))
