# S8cp progress (items 1 and 2, batch 10 scope)

- Base: merge of origin/rfc-0005-s8cb 28ab1a7 onto e497dcf (956c8bb4). Walker 253.
- Item 2 implemented and pinned: tests/tsymex_rfc0005_s8cp_unchecked.nim, Z3 5.1 c green.
- Item 1 implemented, RED observed before the fix (s8cp-work/footprint.red2.log: false sxSat on
  three readers), pinned: tests/tsymex_rfc0005_s8cp_footprint.nim.
- Next: suites on 5.1 c, 4.13.4 c, 5.1 cpp; RFC section; gate worktree sweep; Windows.
