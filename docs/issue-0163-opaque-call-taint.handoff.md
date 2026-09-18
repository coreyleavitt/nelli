# Issue #163 — an opaque call ahead of the target must not cost the answer

Issue-scoped handoff (not an RFC; no `docs/rfc/NNNN` number). Newest entries
at the BOTTOM.

- **Branch:** `rfc-163-opaque-call-taint`, stacked on
  `rfc-162-range-base-width` (named `rfc-*` deliberately — the three Windows
  legs trigger on `[main, 'rfc-*']`).
- **Base:** `ac507c1` (the tip of #162). The stack is incidental, not
  semantic: #163 touches the opaque-call arm and the pragma plumbing, which
  #161/#162 never went near. It is stacked only because #162 has not
  fast-forwarded to `main` yet.
- **Issue:** #163.
- **Test file:** `tests/tsymex_163_opaque_transparent.nim`.

## The defect

`walk`'s `#137` opaque-call arm (`runtime.nim`, `if stmt.opaque:`) did two
things unconditionally: set `w.sawUnknown = true` and continued every path via
`forkPathTainted`. So any target reached *after* an opaque call degraded the
whole run to `sxUnknown`.

Reproduced at `ac507c1` (`scratchpad/bench/probe_163_opaque.nim`, gitignored):

| SUT | `tRaisedExn` | `tLabel` |
|---|---|---|
| `plain` | `sxRaised` | `sxSat` |
| `withEcho` (echo *before* the branch) | `sxUnknown` | `sxUnknown` |
| `echoAfter` (echo *after* the branch) | `sxRaised` | — |
| `covered` (`{.cover.}`) | `sxUnknown` | **`sxSat`** |
| `callsCovered` (plain proc calling a `{.cover.}`'d one) | `sxUnknown` | — |

The `covered`/`tLabel` cell is the one the issue predicted as `sxUnknown` and
which measured `sxSat`. It is not a discrepancy, it is the mechanism in plain
view: `{.cover.}` injects `recordEdge` *inside each branch arm*, so the
fall-through path (no `else` arm to instrument) reaches the trailing label
untainted, while the raise path — which goes through the instrumented `if`
arm — does not. `withEcho` degrades both queries because `echo` sits ahead of
every path.

Every `sxUnknown` carried exactly one error: `weInternalWalkerFault`,
"sxUnknown produced with no classified reason". That is the Invariant-7
backstop firing, i.e. the walker reporting *its own bug* for an ordinary
unmodelled call.

## Two problems, deliberately kept separate

1. **The taint is too coarse.** Correct for an opaque call whose result is
   used or that can mutate state the SUT reads. Wrong for a void call taking
   only values — `recordEdge(id)`, `logCmp(lhs, rhs, op)`, `echo "x"`.
2. **The degrade is unclassified.** Even where the taint is right, the user
   should learn *which call* cost them the answer.

## Design decision — `{.symexTransparent.}` is a promise, not a heuristic

`{.symexOpaque.}` says "do not enter this body". It buys that with a path
taint, which is the right price for `readSensor()` and the wrong price for
`recordEdge(id)`. `{.symexTransparent.}` says the stronger and, for
instrumentation, *true* thing: the call is void, takes only values, and
touches nothing the SUT can read back — so symex deletes it.

Three judgement calls worth recording:

- **Statement position only.** The parser honours the pragma where Nim's own
  typing already guarantees there is no value to drop. A
  `{.symexTransparent.}` proc whose result *is* used reaches the expression
  arm, which gives it `{.symexOpaque.}` handling instead. An over-claimed
  pragma therefore costs precision, never soundness — and the half of the
  opaque contract it still earns (body not walked) is the half that keeps the
  G3fix `KeyError` closed.
- **Arguments are still parsed**, into the preamble; only their values are
  discarded. The pragma is a promise about the *callee*, not about the
  expressions at the call site: Nim evaluates those regardless, so dropping
  them unparsed would silently delete any effect they carry, and any honest
  degrade an unmodellable argument owes. Both instrumentation shapes parse to
  nothing but a value, so the preamble stays empty in the motivating case.
- **`recordEdge`/`logCmp` were RETAGGED, not double-tagged.** Carrying both
  pragmas would have been a hedge with no owner ("which wins?"). The G3fix
  pin (`tests/tsymex_g3fix_walkergap.nim`) is the safety net that proves no
  route regressed to walking their bodies: it still passes.

## Slice status

| # | Slice | Commit | Nature |
|---|---|---|---|
| 1 | `{.symexTransparent.}`; parser drops the call; instrumentation retagged | `b859b4a` | fix |
| 2 | pin `{.covercmp.}`, `{.cover, covercmp.}`, instrumented-callee | `4c7256d` | pins only |
| 3 | classify the remaining degrade (names the callee) | — | in progress |
| 4 | an effect-free void opaque call does not taint (`echo`) | — | planned |
| 5 | pins, version floor, CR2 cache-key, nimble registration | — | planned |

### Slice 1 — the floor

`hasSymexPragma(sym, name)` (generalised from `hasSymexOpaquePragma`) +
`hasSymexTransparentPragma`; the statement-position call arm in
`dsl_parser.nim` returns `mkBlock(@[])` — the established no-op — for a
transparent callee; `coverage.nim` declares its own private
`template symexTransparent() {.pragma.}` (it must stay a Z3-free leaf, so it
cannot import `nelli/symex`; the parser matches pragmas purely by NAME, which
is what makes the private copy sufficient); `symex.nim` exports a public
`symexTransparent*` beside `symexOpaque*`.

**No walker version bump.** This is a parse-time change: the IR itself
differs, so `canonicalize(prog)` moves the cache key on its own and no stale
verdict can be replayed.

### Slice 2 — pins, no implementation

All four passed on first run against slice 1. All four were then verified RED
against `ac507c1`'s `src/` (same test file, `git checkout ac507c1 -- src/`),
so they are sensitive pins rather than vacuous ones.

## Method note — the oracle is executed, not asserted

Inherited from #162. Every symbolic expectation in the test file is paired
with the same computation run for real in the same file: the oracle test calls
all four instrumented SUTs and checks each raises on `Magic` and only on
`Magic`. A taint bug is exactly the shape where a test can encode the engine's
own wrong model and pass.

## Surfaced, not fixed here

- The opaque arm is not the only site that sets `w.sawUnknown` bare; the
  `maxCallDepth` bail and the missing-`ProcSig` bail in the same `isCall`
  dispatch have the same shape. The missing-`ProcSig` one is classified in
  practice (`geInstantiationCapped` rides `prog.parseErrors`); the
  `maxCallDepth` one is worth an audit of its own. Not widened into #163.
- #159 (`recordEdge`'s inferred `.sideEffect` makes `{.cover.}` unusable on
  `func`/`noSideEffect` targets) is adjacent but independent — it is about
  Nim's effect system, not symex's taint.

## Resume command

```
git -C /home/corey/projects/nim/libs/proptest log --oneline -6 rfc-163-opaque-call-taint
```
