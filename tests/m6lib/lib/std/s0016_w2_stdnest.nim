## RFC-0016 int6-w2. A module the check scan classifies as the stdlib by its
## path (`/lib/std/`, as `check_options.isStdlibFile` reads it), standing in
## for a stdlib routine declared inside a stdlib body that pushes check
## options (`tsymex_0016_int6w2_stdnest`). None exists on 2.2.10, by its
## text. Natively `stdNestInner` compiles under the push where it stands, so
## `stdNestHost(300)` keeps 300.

type NR* = range[0 .. 10]

proc stdNestHost*(v: int): int =
  {.push rangeChecks: off.}
  proc stdNestInner(x: int): int = int(NR(x))
  {.pop.}
  stdNestInner(v)
