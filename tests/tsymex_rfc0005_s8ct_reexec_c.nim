## RFC-0005 S8ct: the isolation suite on the re-execution path Windows takes.
## Linux can test that path with `-d:nelliReplayReexec` (this file's `.nim.cfg`):
## the program re-executes itself, with the witness and what the SUT reaches
## handed over, and a replay reaching what cannot be handed over declines.
##
## RFC-0005 S8cm: part 3 of 5, with `tsymex_rfc0005_s8ct_reexec`,
## `tsymex_rfc0005_s8ct_reexec_b`, `tsymex_rfc0005_s8ct_reexec_d`,
## `tsymex_rfc0005_s8ct_reexec_e`, as the isolation suite is split into 5
## parts; each part includes one, here `tsymex_rfc0005_s8ct_isolation_c`.
include tsymex_rfc0005_s8ct_isolation_c
