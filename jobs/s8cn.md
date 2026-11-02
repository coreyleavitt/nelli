# Job: S8cn -- new slice (batch 8's remainder; item 1 checks a verdict-changing step)

**HELD until batch 8 lands; the coordinator will send the base sha.** The integrator's report is quoted in the scope below.

## Setup
- Branch: `rfc-0005-s8cn`, from batch 8's landed head.
- Walker number is assigned at integration; use the next free one above 241 locally, and update the CR2 pin to match.
- Read WORKER-BRIEF.md and WORKER-LOCAL.md first, then batch 8's commits ebddea8 and 6af965d in full.
- In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8cn"
title = "Batch 8's remainder: step 1d's adversarial pins, bt_limit_replace on Z3 4.13.4, the declines left on aliased mpairs views and seq elements passed with their seq"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first, against native Nim)
1. **Step 1d can turn a decline into `sxUnsat`, and has no adversarial pin.** It answers UNSAT when the query with no sequence theory, plus the facts, has no model breaking a cap. Its soundness rests on the facts being valid. Nobody ran a native check for `grow_pad_dead`.
   - Check `grow_pad_dead` natively, exhaustively over its bounded inputs.
   - Pin queries where 1d must NOT answer: a length bound one past the cap, a bound that holds on only one branch, a bound only the sequence theory gives, and a query whose real model is past the cap. Each must stay live or decline, checked natively.
   - Audit each fact `seqRangeFacts` contributes, since 1d now leans on all of them to justify an UNSAT: write down why each is valid in Nim's byte-faithful string model, and pin any you could not justify. A wrong fact is a soundness fix, stated at the top of the report.
2. **`bt_limit_replace` on Z3 4.13.4** spends the budget even at 100M units, so its pin was weakened to sat-or-decline there. A/B it against S8bp's isolation on this stack, restore the exact `sxSat` on 4.13.4 under the default budgets, and repin to exact. Other queries of the shape must gain too, so do not special-case this one.
3. **Declines on a callee holding an `mpairs` view and reaching its Table:** a non-literal key's presence, both the view and the Table written, and a holder object carrying the view. Model each. Keep any decline only with native evidence for why it must stay.
4. **A key removed while its view is live** declines where it is removed. Decide it where Nim's behaviour is defined, checked natively. Where Nim's slot walk depends on the hashes, keep the decline, and say so.
5. **A proc-value view passed with its Table,** and a global or local seq element passed together with its seq. Both are pinned as sound declines today. Model them.
6. **S8bw's RFC row is still `pending`** although the slice landed. Flip it, and check every other landed slice's row while you are there.

Not yours, because queued slices own them: PCRE limits and the regex items (S8cf), the product overflow split and `var openArray` copy (S8cg), `tsymex_configdefaults_depth` (S8ci).

## Verification
- Suites: yours, b8_integration, s8bx_*, s8bt_*, s8bp_isolation, s8bb_replace, s8bl, s8bs, CR2.
- Run on Z3 5.1 and 4.13.4, plus cpp for the new suite. All three Windows legs green.
- Report DONE to `worker-reports/s8cn.md`, with per-file Windows times.
