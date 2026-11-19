## RFC-0016 int6-a, leaked scopes. Imported under `{.push rangeChecks: off.}`
## by `tsymex_0016_int6a_leak`, and the first to import
## `s0016_int6a_leakdeep`, which it therefore compiles under the same push.

import ./s0016_int6a_leakdeep

proc viaConv*(v: int): int = deepConv(v)
