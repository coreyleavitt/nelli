## RFC-0016 int6-a, leaked scopes. Compiled first by `s0016_int6a_leakvia`,
## itself compiled under `{.push rangeChecks: off.}`: natively `deepConv(300)`
## keeps 300.

type LD* = range[0 .. 10]

proc deepConv*(v: int): int = int(LD(v))
