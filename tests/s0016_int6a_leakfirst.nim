## RFC-0016 int6-a, leaked scopes. A module `tsymex_0016_int6a_leak` imports
## twice: first without a push, then under `{.push rangeChecks: off.}`. The
## first import compiles it, so natively `firstConv(300)` raises `RangeDefect`.

type LF* = range[0 .. 10]

proc firstConv*(v: int): int = int(LF(v))
