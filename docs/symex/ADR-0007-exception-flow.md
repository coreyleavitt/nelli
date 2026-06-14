# ADR-0007 — Exception control-flow model for the symex walker

> Status: accepted. Authored in Phase 15 cycle **Z4**, ahead of Cluster E
> (which implements it: E1–E8). Z4 lands only the structural prerequisite —
> `WalkCtx.found: seq[RawResult]` — so the exception cascade (E2a) is a pure
> addition. Related: ADR-0010 (logical heap), the `sxRaised` verdict (E2a),
> `cacheKeyRaised` (Z3e).

## Context

A property test SUT can `raise`. The symbolic executor must decide, for each
feasible path, whether an exception escapes the SUT (a finding) or is caught.
This is non-trivial in a path-explicit interpreter for three reasons:

1. **Multi-path raises.** A single SUT may raise from several callsites under
   different path conditions — `raise ValueError` on one branch, `raise IOError`
   on another, a `Defect` on a third. Each is a distinct finding with its own
   witness (the accumulated `pc` at the raise point).
2. **Propagation is structural, not Z3.** Whether a raised exception is caught
   depends on the *static* `try`/`except` nesting and the exception *type
   hierarchy*, neither of which is a satisfiability question. The walker must
   thread a handler stack and pattern-match types itself.
3. **Phase 14's single-finding shape.** Before Phase 15, `WalkCtx.found` was an
   `Option[RawResult]` — it could hold exactly one verdict. A walker that finds
   one SAT witness *or* one of several raised exceptions cannot be expressed by
   an `Option`: SAT and raised are not mutually exclusive across paths, and
   multiple raised types must each surface.

## Decisions

### D1. `WalkCtx.found` becomes `seq[RawResult]` (Z4)

The walker accumulates findings in a sequence rather than a single `Option`.
For Phase-14 behaviour this is a `seq` used like an `Option`-of-one (only `sxSat`
findings are appended; `sxUnknown` is tracked separately via `w.sawUnknown`,
`sxUnsat` is the empty-found fallback). The change is behaviour-preserving at
Z4; it exists so E2a can append one `sxRaised` entry per distinct raised type
without a second parallel field.

### D2. `shouldStop` halts on the first `sxSat` (and, from E2a, `sxRaised`)

```nim
proc shouldStop(w: WalkCtx): bool =
  for r in w.found:
    if r.status in {sxSat, sxRaised}: return true   # Z4: {sxSat} only; E2a adds sxRaised
  false
```

A satisfying witness halts exploration (the property is falsified — done). A
raised exception that escapes the SUT halts likewise (a defect/exception finding
is a result). An `sxUnknown`-only `found` does **not** halt: a SAT path may still
exist on another branch. An `sxUnsat` finding never enters `found`.

### D3. One `sxRaised` entry per distinct `(exnType, pathCond)` (Cluster E)

Exception flow is modelled by a stack of handler frames threaded through
`WalkCtx`. A `raise` on a feasible path emits an `sxRaised(typeId, witness)`
result rather than continuing the path. Propagation is explicit: if the handler
stack is non-empty, pop the top frame and pattern-match the raised type against
its `except` clauses (first match wins; bare `except:` matches everything). On a
match, control transfers into the handler body and the `sxRaised` is consumed —
the path continues. With no match, the result propagates up the call stack until
a matching handler is found or the SUT boundary is reached, where the top-level
verdict becomes `sxRaised`. `finally` blocks run unconditionally on both normal
and raised exit; a `finally` that itself raises replaces the in-flight exception.

### D4. Cache: one slot per raised type via `cacheKeyRaised`

Each raised type gets its own content-addressed DB slot, `":raised:" & typeId`
(`cacheKeyRaised`, Z3e). A multi-raise SUT writes several such entries;
`loadAll(sutPrefix)` reconstructs the `seq[RawResult]` by scanning every key
matching the SUT prefix. This keeps the sat/unsat/unknown slots
(`:sat`/`:unsat`/`:unknown`) untouched and lets distinct raised types coexist.

## Why this model is sound

The walker is already a path-explicit interpreter: every branch produces a
concrete `Path` annotated with a path condition. Modelling exceptions as an
explicit `sxRaised` result threaded through return continuations is a
conservative extension of that structure — no CPS transform, no implicit
control-flow edges, no change to the path-sat layer. Every `raise` carries the
`pc` under which it fires, so the witness query is just that accumulated `pc`.
Type-hierarchy matching consults a static table built at parse time (E4/E4a); it
is not a Z3 query. Every raised verdict therefore has the same explicit path
provenance the `sxSat` family already provides.

## Alternatives considered

### A1. Keep `Option[RawResult]`, add a parallel `raised: seq[RawResult]`

Rejected: two fields with different stop semantics force `shouldStop` (and every
`found`-reading site) to reason about both, and the shape diverges from the
single `seq[RawResult]` that E2a's cascade naturally produces.

### A2. Model exception flow purely axiomatically (never walk raise paths)

Rejected: soundness gap. A SUT that propagates `raise` through intermediate
procs would silently become `sxUnsat` (no witness found) rather than `sxRaised`,
hiding real defects — a direct violation of the `complete-lib-not-consumer`
standing directive.

### A3. A separate `raisedFindings` field on `WalkCtx` alongside `found`

Rejected for the same reason as A1: `shouldStop` and the result-extraction path
would need to consult two fields; the unified `seq` is simpler and is exactly
what the cascade emits.

## Consequences

- **E2a is a pure cascade addition** — no field-type change needed (Z4 did it).
- `shouldStop` has a two-condition halt: `sxSat` (witness) and `sxRaised`
  (defect/exception); `sxUnknown` alone never halts.
- Multi-raise SUTs produce multiple cache entries; deserialization reads all
  matching `":raised:"` keys.
- `WalkerStatics` (handler-static tables: `exnTable`, `userExnHierarchy`) and
  `CallFrameCtx` (`handlerStack`, `inFlightExn`) — the per-walker vs per-frame
  split introduced empty at Z4 — give the handler machinery its lifetime-correct
  homes when E1 populates them.
