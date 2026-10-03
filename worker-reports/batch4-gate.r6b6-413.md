# Batch-4 gate: r6_b6_optionregion on Z3 4.13.4 at 8165899

Run alone after the sweep (box otherwise idle of gate work), `dt413.sh c tests/tsymex_r6_b6_optionregion.nim 900`:

```
r6b6_413 rc=0 ok=8 failed=0 wall=62.9s
```

Sweep: `scripts/sweep.sh -j 4`, wall 5043s; worktree verified at exactly 8165899f5be6693f3abf5ff9dd50e6cf08d106d6, clean.
