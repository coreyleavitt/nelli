# S8cq progress

- Rule implemented per coordinator's inversion (commit 3a8194ec, local): by-value allowlist or proved-no-write; lvalue-with-call declines at each twice-lowering.
- All probe shapes on c/Z3 5.1: no FALSE rows left.
- New finding: `ref` by-value with callee overwriting the actual reads a freed cell under ARC/ORC (`new gR; gR[]=50; a[]` reads 50); ref only allowlisted for a local no routine reaches.
- Fixed two compile stops: alias of object (this stack only), pragma on a formal (main too).
- Tests generated, existing suites being run to list precision moves.
