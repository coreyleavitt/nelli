## RFC-0016 int6-w2. A module that `tsymex_0016_int6w2_pragmablock` imports
## first through a template defined inside a module-level pragma block,
## unpushed, and again under `{.push rangeChecks: off.}`: natively it is
## compiled at the first, so `leakConv(300)` raises `RangeDefect`.

type LR* = range[0 .. 10]

proc leakConv*(v: int): int = int(LR(v))
