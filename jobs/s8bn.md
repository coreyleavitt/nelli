# Job: S8bn -- new slice (S8bh's remainder; all PRECISION)

Set up your own worktree under /home/corey/tmp-usage/work/wt on a new branch `rfc-0005-s8bn`, created from origin/rfc-0005-s8bh at a28c9c3. The base is S8bf, walker 208, and S8bn's provisional walker is **215**. Read WORKER-BRIEF.md and the "As landed (S8bh)" notes on that branch before you start.

Add this RFC row before the S11 row in your first commit, and flip it to `done` at the end:
```
[[slice]]
id = "S8bn"
title = "S8bh's remainder: ptr alias witnesses (parameter order, global/var-param targets), var-formal ptr declines, ptrs into heap-held containers and by-value aggregates, diverging void closures, proc fields and methods, unknown-target global havoc, `of` operator and nil literals, generic/inheritable/case-object hierarchies, run-time type tags tied to static types"
state = "pending"
```

## Scope (do all of it and defer nothing; pin each item RED first)
1. **A ptr alias witness depends on parameter order.** With `(pi: ptr int; q: Q)`, the sound sxSat replays as refuted. Make the witness builder order-independent, allocating the target before the pointer, so the witness replays roConfirmed.
2. **A ptr aimed at a global or a `var` param has no renderable witness.** Render those witnesses: set the global, or pass the var-param cell, and point the ptr at it. They must replay roConfirmed.
3. **A callee's or closure's `var` formal makes every ptr deref of a type it may hold decline**, even when the actual is a local that no pointer can reach. Refine this with reachability: a local whose address is never taken cannot be a ptr target.
4. **A ptr into a seq/table/set element held in the heap, or into a by-value aggregate global or var param, declines.** Model those targets where a finite candidate set exists. Use S8ax's element-alias identity (root, path, snapshot index).
5. **An always-raising void closure reports `ceClosureBodyDiverged`.** It should report as a raise instead. Fix the classification.
6. **A proc field in an object, and a method call, decline.** Model them:
   - A proc field is an indirect call through S8bh's proc-value path, with the target set coming from every assignment to that field.
   - A method call is dispatch over the known overrides, keyed on the run-time type tag.
   The unknown-target havoc must also reach globals the callee could touch. Today path taint covers that; make it explicit.
7. **The `of` operator is unsupported, and a general `nil` literal does not parse.** Model `of` as a test on the run-time type tag, and parse `nil` in every typed position.
8. **Generic, `{.inheritable.}` and case-object hierarchies keep per-type keying.** Extend S8bh's shared hierarchy address space to cover them.
9. **A parameter's run-time type tags are free rather than tied to its static type.** Constrain each tag to the static type's subtree.

## Integration note
S8bk, running separately on rfc-0005-batch3, fixes var/addr actuals so they take their address late, as Nim does. Its proc-variable forms need S8bh's indirect-call copy-out. If S8bk's branch has a DONE report on worker-sls2 by the time you reach item 6, also apply its late-address rule to S8bh's indirect-call path, pinned. Otherwise say so in your report.

## Verification
- **Suites:** yours, s8bh, s8bf_alias, s8bd, s8ba, s8au, s8an, s8ac, s8i, s8_scope, CR2, s7_closure, s9_vetoes, h_witness, s8ab_letaudit, s8x_vm_alias, every 163/163rev suite, and the inheritance and closure suites.
- **How:** run them on Z3 5.1 and 4.13.4, plus one cpp run.

Push the branch and report DONE in `worker-reports/s8bn.md`.
