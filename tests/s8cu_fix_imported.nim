## RFC-0005 S8cu. First compiled by an `import` under a push, in
## `tsymex_rfc0005_s8cu_import`.
proc importedPlain*(v: int): int = v + 1

{.push overflowChecks: on.}
proc importedOn*(v: int): int = v + 1
{.pop.}
