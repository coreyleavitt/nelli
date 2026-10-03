# Job: S8bq -- new slice (S8bi's remainder)

## Setup
- **Branch.** Create `rfc-0005-s8bq` from origin/rfc-0005-s8bi at e5df207. Its base is S8bb, at walker 210.
- **Provisional walker:** **220**.
- **Read first:** WORKER-BRIEF.md and the "As landed (S8bi)" notes.

Add this RFC row before the S11 row in your first commit, and flip it to `done` at the end:
```
[[slice]]
id = "S8bq"
title = "S8bi's remainder: huge newSeq n modelled as succeeding, set-typed values/params and builtin incl/excl, re\"(ab\" literal raise, newSeqUninit path taint, set literals with non-constant elements"
state = "pending"
```

## Scope (do all of it; defer nothing; pin each item RED first)
1. **SOUNDNESS: a huge `n` in `newSeq` is modelled as succeeding.** Real Nim runs out of memory or aborts instead.
   - S8bc already gives `n > 2^20` a scoped decline and `n < 0` a `RangeDefect` (`iekSeqNewZero`). It is in batch 4, which you don't have.
   - Apply the same rule to S8bi's `iekSeqNew` / `newSeqUninit` path, using the same 2^20 threshold and the same decline reason.
   - Never model an allocation above the threshold as succeeding.
   - The batch-5 integrator will unify `iekSeqNew` and `iekSeqNewZero`. Name your constant so it can be shared.
2. **Set-typed values, `set[T]` params and builtin `incl`/`excl` are unclassified.**
   - Model `set[T]` for small ordinal `T` (bool, char, enum, int8/uint8 ranges up to 2^16) as a bitvector or a Z3 array/set.
   - Cover membership, `incl`, `excl`, `+`, `-`, `*`, `<=`, `<`, `==`, `card` and literals.
   - S8bl (separate) is enumerating var-param magics, including `incl`/`excl`, in a no-op guard. Your modelling supersedes a decline there. Note it for the integrator.
3. **`let r = re"(ab"` declines as `feUnsupportedExprKind nnkCallStrLit`.** Nim always raises `RegexError` there. Model the call-string-literal form as a constructor call, so an invalid pattern raises.
4. **`newSeqUninit` taints the whole path even when no element is read.** Taint only on a read of an element that hasn't been written.
5. **Set literals with non-constant elements still decline.** Model them, including ranges like `{a..b}` with symbolic bounds.

## Verification
- **Suites:** yours; s8bi; s8bb; s6b_ops; emit_roundtrip; CR2; letaudit; n27; every suite that `command grep -l 'set\[\|incl\|excl\|newSeq\|re"'` turns up.
- **Run on:** Z3 5.1 and 4.13.4, plus one cpp run.

Push, then report DONE to `worker-reports/s8bq.md`.
