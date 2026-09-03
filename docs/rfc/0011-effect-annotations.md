# RFC — discharging Nim effect annotations with symex

- **Status:** seed — composed 2026-09-03 from the post-0005 architecture
  survey. Small surface, high distinctiveness. Not yet designed.
- Category: symex
- Size: S
- Value: med
- **Depends on:**
  - RFC-0005 (branch-scoped-degrade / soundness channels) — hard. This RFC is
    built entirely on `sxUnsat` claims, and 0005 §0 establishes that UNSAT is
    trustworthy only when no path carried an under-approximation. Shipping
    `checkRaises` before 0005 means shipping a proof obligation the engine
    cannot honestly discharge.

## §0 — Thesis

Nim lets you write `{.raises: [].}` on a proc. The compiler checks it
*syntactically* — it verifies that no call in the body is declared to raise.
It cannot tell you that the `IndexDefect` on line 12 is unreachable, because
that is a semantic question about values, and the effect system does not
reason about values.

nelli has an engine that does.

```nim
checkRaises(myProc)   # sxUnsat: no input reaches a raise, up to bounds
                      # sxSat:   here is the input that does
```

There is no other way to get this in Nim, from any tool.

## §1 — Why this is the right size

Every other route to "specifications attached to the code" — `requires` /
`ensures` contracts, refinement annotations, a Dafny-shaped surface — is a
different library, and would take nelli somewhere it should not go on the
strength of one good idea.

Effect annotations are the exception, because **the specification is already
written**. Users annotate `{.raises.}`, `{.noSideEffect.}`, and `func` today,
for the compiler's benefit. This RFC does not ask them to write anything new;
it makes an annotation they already maintain into a checked claim. That is the
whole ergonomic argument, and it is why this slice is worth shipping while the
larger contracts idea is not.

## §2 — Scope

**In scope.** `checkRaises(fn)` — prove, up to the configured bounds, that no
input reaches a raise site, or produce the witness that does. Filtering by
exception type (`checkRaises(fn, IndexDefect)`). Honest reporting of the
bounds the claim holds under, and of `sxUnknown` when it does not hold at all.

**In scope if it falls out cheaply.** `{.noSideEffect.}` / `func` — the walker
already treats `func` and `proc` identically everywhere it resolves a callee,
so the machinery is present; whether the *claim* is expressible in SMT is a
design question, not an assumption.

**Out of scope.** `requires`/`ensures` contracts, auto-derived properties from
signatures, and any pragma that asks the user to write a new specification.
Named here so the RFC does not drift into them.

## §3 — Open questions for the design phase

- **What does the user do with `sxUnknown`?** A "cannot prove" verdict on a
  `{.raises: [].}` annotation is neither pass nor fail. `examples/symex_loops.nim`
  already documents three honest responses to `sxUnknown`; this needs the
  same treatment, and probably a policy setting rather than a fixed answer.
- **Where does the verdict live?** A `doAssert`-style call site, a test-suite
  assertion, a compile-time pragma check, or an entry in the RFC-0008
  assurance record. Probably more than one, and the record is the interesting
  one — *"this proc's `{.raises: [].}` was proven under bounds X"* is exactly
  the kind of evidence that decays silently when the code changes.
- **Bounds and honesty.** A proof under `maxLoopUnwind = 8` is not a proof.
  How is the bound surfaced so nobody reads it as one? This is 0005's question
  in a new front door, which is the strongest argument for the dependency.

## §4 — First slice

`checkRaises(fn)` returning `sxSat` with a witness on a proc that provably
raises, and `sxUnsat` on one that provably does not — both under explicitly
reported bounds. One function, one honest verdict, end to end through the real
entry point.

## §5 — A note on RFC-0005

0005 is currently the only unblocked item on the board and has no named
downstream consumer. This RFC is one: it is entirely a consumer of sound
`sxUnsat`, which is precisely the half of the soundness rule 0005 identifies as
missing. If 0005 needs a motivating application to design against, this is it.
