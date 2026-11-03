## RFC-0005 S8cu. `include`d by `tsymex_rfc0005_s8cu_modules` under a push, and
## not itself under one.
proc includedPlain(v: int): int = v + 1

{.push overflowChecks: on.}
proc includedOn(v: int): int = v + 1
{.pop.}
