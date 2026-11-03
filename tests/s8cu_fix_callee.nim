## RFC-0005 S8cu. Callees in another module, for `tsymex_rfc0005_s8cu_modules`.
type K* = enum kA, kB, kC, kD
type P* = object
  case k*: K
  of kA, kB: x*: int
  of kC: y*: int
  else: discard

proc checkedField*(v: int) =
  var o = P(k: kA, x: v)
  o.y = v

{.push fieldChecks: off.}
proc uncheckedField*(v: int) =
  var o = P(k: kA, x: v)
  o.y = v
{.pop.}

proc checkedAdd*(v: int): int = v + 1

{.push overflowChecks: off.}
proc uncheckedAdd*(v: int): int = v + 1
proc genericUnder*[T](v: T): T = v + 1
{.pop.}

proc genericClean*[T](v: T): T = v + 1

template makeAdder*(name: untyped) =
  ## A routine whose line info is here and whose options are the expansion's.
  proc name(v: int): int = v + 1
