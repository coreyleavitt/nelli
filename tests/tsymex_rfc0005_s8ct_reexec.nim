## RFC-0005 S8ct: the isolation suite on the re-execution path Windows takes.
## Linux can test that path with `-d:nelliReplayReexec` (this file's `.nim.cfg`):
## the program re-executes itself, with the witness and what the SUT reaches
## handed over, and a replay reaching what cannot be handed over declines.
include tsymex_rfc0005_s8ct_isolation
