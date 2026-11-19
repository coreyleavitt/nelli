## RFC-0016 int6-a. A module the importer `tsymex_0016_int6a_scopes` imports
## under `{.push rangeChecks: off.}`, and the first to do so: natively it is
## compiled with the push, so `leakConv(300)` keeps 300 and does not raise.

type LR* = range[0 .. 10]

proc leakConv*(v: int): int = int(LR(v))
