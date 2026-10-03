# Job: S8ca -- new slice (S8bu's remainder)

## Setup
- Branch: create `rfc-0005-s8ca` from origin/rfc-0005-s8bu at 5729b1a (code 8815a81, walker 225, base S8bs e7965d0).
- Provisional walker: **233**.
- Read first: WORKER-BRIEF.md, WORKER-LOCAL.md, and the "As landed (S8bu)" notes.

In your first commit, add this row before the S11 row. Flip it to `done` at the end.
```
[[slice]]
id = "S8ca"
title = "S8bu's remainder: cpp segfault in configdefaults' maxCallDepth crash pin, structural viewFollows in-place check, addr s[i] of element-cell seqs to calls, closures over address-taken vars and heap lvalues, seq args to proc values, string as openArray[char], negative toOpenArray and resizing mitems, gps[].add through ptr-to-seq, S8bu suite compile time"
state = "pending"
```

## Scope
Do all of it and defer nothing. Pin each item RED first.

1. **CRASH (first): `tsymex_configdefaults` segfaults on cpp (rc=139)** in its round-2 `maxCallDepth` crash pin.
   - This is pre-existing: it crashes the same way at e7965d0.
   - The pin exists to prove that deep recursion hits `maxCallDepth` and declines instead of overflowing the native stack. On cpp, the native stack overflows first.
   - Find the per-frame stack cost on cpp, which is likely larger frames from cpp codegen or exception tables.
   - Then either make the depth check fire before the native stack runs out on BOTH backends, or bound recursion by measured stack use (a guard page or a stack-pointer check). The decline must be in-band.
   - Check whether the Windows legs (8 MB or 1 MB default stacks) can hit the same thing.
2. **Latent SOUNDNESS: `viewFollows`.** A whole assignment over a constant-array base, whose new data happens to be a store chain over the old data, is read as in-place. The check is structural, not semantic. Make it semantic: track identity by an explicit in-place write marker, not by the shape of the term. Pin it with a constructed SUT, even if that needs a defined-behaviour variant.
3. **`addr s[i]` of a seq with element cells, passed to a call,** declines with "in the element's own heap". Model it.
4. **Closures:**
   - Capturing an address-taken variable (S8ax capture cells against the address cell): unify them.
   - A heap lvalue `pb[].x` reached by a closure body (S8bh `touchMeetsOuter`): model it.
5. **A seq argument to a proc value** declines with `seUnsupportedCompoundSortLeaf`. This includes `var openArray` through a proc value. Model it.
6. **Strings:** a string viewed as `openArray[char]`, and a by-value string of an address-taken string. Model character writes.
7. **`toOpenArray` with a negative length,** and a `mitems` body that resizes the seq. Model what Nim does, IndexDefect or otherwise, checked against native runs.
8. **`gps[].add` through a pointer to a seq** gives `heUnsafeCast`. Model it.
9. **Compile time:** the S8bu suites took 67-108 s compile user time under load. Measure them on a quiet slot, and split any file over 60 s.

## Integration note
Two S8bu commits (d875c95, 8815a81) lack "RFC-0005 S8bu" in their subjects. Leave them; the integrator handles it.

## Verification
- Suites:
  - yours;
  - the s8bu and s8bs suites;
  - configdefaults on c AND cpp;
  - s8ax, s8bh, s8be, s7_closure, letaudit, n27, emit_roundtrip, augmented_assign, CR2;
  - every openArray, closure and `addr` grep hit.
- Run on Z3 5.1 and 4.13.4, plus cpp.
- Push, then report DONE to `worker-reports/s8ca.md`.
