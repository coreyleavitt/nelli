# Job: S8bx -- new slice (S8bl's remainder)

**Setup.**
- Branch: create `rfc-0005-s8bx` from origin/rfc-0005-s8bl at 1f38a13 (base 22b67c7, walker 213).
- Provisional walker: **228**.
- Before starting, read WORKER-BRIEF.md, WORKER-LOCAL.md (per-job scratch dirs), and the "As landed (S8bl)" notes.

In your first commit, add this row before the S11 row, and flip it to `done` at the end:
```
[[slice]]
id = "S8bx"
title = "S8bl's remainder: raise from in-walk witness extraction lost on the C backend, witness-render drift for a variant-arm seq of ref-holding elements in a Table, mpairs aliasing of loop var and table, key change during Table iteration, string setLen over a symbolic string"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)
1. **SOUNDNESS: a raise from in-walk witness extraction is lost on the C backend.**
   - The walk continues and can return a false sxUnsat. S8bl removed the one trigger it found; the mechanism is still there.
   - Find why the exception is dropped on c and not on cpp. Likely suspects are a `{.raises: [].}` / `noexcept` boundary, a `try` in a callback, or the C backend's setjmp/goto exception path through a closure or FFI frame.
   - Make every such raise either propagate to the top-level handler as a named decline, or be impossible by construction.
   - Pin it with a deliberately failing extraction on both backends.
   - Audit the other in-walk callbacks for the same pattern.
2. **Crash: a variant-arm seq of ref-holding elements inside a Table fails the compile.** `isRenderableWitnessTy` and the reader disagree about it.
   - Make one predicate the source of truth for both.
   - Then render the type, or skip it consistently.
3. **mpairs aliasing.** One call receives both the loop variable and the table itself. Model this through the address-cell / `bindVarLocs` machinery, which S8bs adds and batch 6 will carry. If your base lacks it, model it locally and note the reconciliation for the integrator.
4. **A length-preserving key change while iterating a Table** currently follows the initial enumeration and is tainted `feTableIterOrder`.
   - Model Nim's real iteration semantics: walk the hash slots as the table is modified, matching native output.
   - If they are well-defined for the modelled shapes, decide them; if not, keep the taint and prove why with native runs.
5. **String `setLen` over a symbolic string.** `str.at` is undecided on both Z3 versions.
   - Re-encode it with an explicit prefix/extension: `s' = substr(s,0,n) ++ zeros(n-len(s))`, or a per-index axiom over bounded lengths.
   - Make it decide.

## Integration note
iekSeqNew/iekSeqNewZero are unified in batch 5; ignore them here.

## Verification
- Suites: yours, the s8bl suites, s8bc (3-way split), s11_surface, r6_b6_optionregion, CR2, and every Table/mpairs/setLen/witness grep hit.
- Run on Z3 5.1 and 4.13.4. Item 1 also needs runs on BOTH backends.
- Push, then report DONE to `worker-reports/s8bx.md`.
