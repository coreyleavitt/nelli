## RFC-0005 S8cu fixture: imports `s8cu_fix_hidden_m2` under a push. Nothing here
## is walked; the scan finds it by the import graph.
{.push fieldChecks: off, rangeChecks: off, objChecks: off.}
import ./s8cu_fix_hidden_m2
{.pop.}
