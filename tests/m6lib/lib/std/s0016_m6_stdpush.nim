## RFC-0016 int6-m6. A module the check scan classifies as the stdlib by its
## path (`/lib/std/`, as `check_options.isStdlibFile` reads it), standing in
## for a stdlib routine whose body pushes check options
## (`tsymex_0016_int6m6_stdbodypush`). Natively `v + 1` here is the plain C
## addition, undefined at `high(int)`.

proc stdId(x: int): int {.noinline.} = x

proc stdOvfRegion*(v: int): int =
  {.push overflowChecks: off.}
  result = stdId(v) + 1
  {.pop.}
