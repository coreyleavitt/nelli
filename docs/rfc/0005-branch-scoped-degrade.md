# RFC — branch-scoped classified degrade (in-band signaling)

- **Status:** draft — scoped out of RFC-0001 by Corey 2026-08-31 as its own
  round, per that RFC's own recommendation. Nothing implemented; the
  exception-based approach was prototyped under 0001 and **refuted**, and
  that refutation is the main asset this doc carries forward. Next step is
  stage-2 architect rounds, not code.
- Category: symex
- **Depends on:**
  - RFC-0001 (chapulin-hardening) — this is B7-2, deferred out of its round 6;
    the Bug #2 read-taint and B7r2 path-scope work are the direct prior art.

## §0 — Thesis

The walker's classified-degrade machinery is **whole-run**, not per-path. A
single top-level `try`/`except` in `runSymexImpl` catches every classified
degrade carrier, so an unmodeled construct on *any* branch taints the entire
query — including branches the property never reaches.

That is exactly the all-or-nothing the parent RFC's own per-prefix-scoping
doctrine forbids ("never all-or-nothing"), and it is not theoretical: it is
what keeps chapulin's `parseMode`-shaped dispatch from proving. A `case` over
scanned content with an `else: raise` poisons a **disjoint sibling branch** of
the same dispatch. Worked around in the consumer by rewriting the shape as
direct string equality; the engine limitation is untouched.

## §1 — What is already known (do not re-derive)

**The obvious fix is confirmed unsound on this toolchain.** RFC-0001's B7r2
slice prototyped the natural design — a `SymexConstructGapError` base for the
19 construct-gap carriers, caught at the `isIf`/`isWhile`/`isCall` walk
boundaries, taint-and-continue via SND-1 — and found that wrapping **even one**
of those four sites in `try`/`except` causes the underlying classified-degrade
exception to **never be raised at all**.

Not corrupted-but-visible: absent. Confirmed via an in-band print immediately
before `runSymexImpl`'s own verdict computation (`w.sawUnknown` and
`w.walkDegradeErrors` verifiably stay unset), reproduced across
`--forceBuild`/fresh-nimcache runs (ruling out a cache artifact), and isolated
by bisection — removing the same `try`/`except` reliably restores the correct
classified failure. Non-re-raising, single catch, new base type or one of the
19 concrete types directly: all four variants elide.

Toolchain: **Nim 2.2.10-patched, C backend, ORC, `--exceptions:goto`,
`--threads:on`**. The prototype was fully reverted; nothing shipped.

This is a more severe manifestation of the constraint this codebase already
recorded in **ADR-0020/CR-1c** ("a per-`walk`-frame catch/re-raise… corrupted
memory… a C-backend-only SIGSEGV") and architected around with the single
top-level catch. The constraint is therefore **stricter than previously
written**: not "don't catch at every frame" but "don't catch below the top
frame at all", at least around a `seq[Path]`-returning recursive call.

**Three degrade carriers already coexist**, each safe in a different region of
the call graph — `allocDegrade` (bare allocator), the R1 placeholder funnel
(`lower()`-internal), and `degradeStrArm` (single-proc-frame `try`/`except`).
The taxonomy is documented at `runtime.nim`'s CR-1c carrier-boundary table.
Any design here must say what happens to all three, not just add a fourth.

**Path-scoped taint already exists at field granularity.** RFC-0001's Bug #2
deposits an SND-1 taint on the specific *read* statement that touches an
unsupported field, rather than poisoning the whole proc. B7r2 then lifted the
same idea from field level to path level for allocation. The precedent is
sound; what is missing is the mechanism to carry it across a branch boundary
without an exception.

## §2 — The identified path (to be validated, not assumed)

In-band signaling threaded through `lower()`'s recursive call graph, replacing
the exception-based carriers entirely: `lower()` returns a value that can carry
a degrade rather than raising one, and branch boundaries merge those signals
per-path instead of catching.

This is the only pattern the B7r2 session identified that avoids the confirmed
elision hazard. It is also **much larger and more invasive than a rider** —
every recursive caller in `lower()` changes shape — which is why it earned its
own RFC instead of being folded into a slice.

**Open architectural questions for round 1:**

1. Does in-band signaling actually dodge the hazard, or does the elision have a
   root cause that would bite a different construct too? The mechanism was never
   root-caused — only characterized. A compiler-level explanation would change
   the design space, and may be worth filing upstream regardless.
2. What is the return-shape of `lower()`? A result type, an out-param, a
   walker-state field, or a taint accumulator threaded through the context.
3. Do the three existing carriers get migrated, or does a fourth mechanism
   coexist? Migration is more invasive but leaves one story instead of four.
4. What is the merge rule at a branch boundary — how do two sibling paths with
   different taints combine, and what does that mean for the final verdict?
5. Cost. Every `lower()` frame gaining a signal check is a constant-factor tax
   on a walker whose fork cost already regressed ~3.4x (N45, un-root-caused).
   That regression should probably be understood before this lands on top of it.

## §3 — Definition of done (provisional)

- The B7-2 repro — a `case` over scanned content with `else: raise`, sibling
  branch disjoint from the property — proves instead of degrading, on **both
  backends**.
- The pin RFC-0001 left behind flips from classified-decline to a real verdict
  (it was deliberately written to assert status *and* classification so a fix
  turns it red rather than going stale).
- No existing classified degrade becomes a crash, a silent wrong answer, or a
  whole-run taint that used to be path-scoped.
- `symexWalkerVersion` bumps; the CR2 cache-key pin tracks it.

## §4 — Non-goals

- The real-`decode` stretch goal from RFC-0001's B7. It is blocked on this, but
  proving it is not this RFC's gate.
- Root-causing N45's fork-cost regression (own work; see §2 question 5).
- Widening the modeled fragment. This RFC changes how gaps are *reported*, not
  how many gaps there are.
