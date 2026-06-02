# Extending symex

How to bring procs symex doesn't natively understand into the
walker's universe.

There are two extension surfaces, addressing different needs:

| Surface | Audience | What it gives you |
|---|---|---|
| `{.symexOpaque.}` pragma | Application developers | "Treat this proc as a black box." Zero new code; one pragma per proc. |
| The built-in registry | proptest contributors | First-class symbolic semantics for stdlib procs (`len`, `[]`, `contains`, …). Requires walker code. |

For v1, **the pragma is the supported user extension API**. Direct
edits to the built-in registry are reserved for proptest's
maintainers — see § *Extending the built-in registry* at the end.

## `{.symexOpaque.}` — the user-facing pragma

### When to reach for it

Any proc whose body the walker can't or shouldn't enter:

| Reason | Example |
|---|---|
| **FFI** — the body is in C/external library | `proc z3_solver_check(...): cint {.cdecl, importc.}` |
| **IO** — non-deterministic outcome | `proc readSensor(): int` |
| **Trusted black box** — verified elsewhere | `proc cryptographicallySecureRandom(): int` |
| **Cost** — body works but is huge | `proc bigSimulation(...): Result` |
| **Out-of-fragment** — body uses features symex doesn't model | proc using a thread, channel, closure with capture, etc. |

### Semantics

When the walker encounters a call to an opaque proc:

1. It does *not* enter the body.
2. It synthesises a fresh symbolic value of the proc's return type
   (using the same machinery as parameter-symbol allocation).
3. It marks the surviving path uncertain. The final status will
   therefore be at best `sxUnknown` — never `sxUnsat` — because
   we admitted ignorance about the proc's behaviour.

This is sound by construction: refusing to assert anything about
the proc's output means no Z3 query mentions it, so no spurious
SAT/UNSAT result follows from it.

It mirrors the standard symex literature's *uninterpreted-function
abstraction* — KLEE's `klee_make_symbolic`, CrossHair's
`SymbolicFactory`, Pex's `PexAssume.IsNotSymbolicSafe`. The Nim
ergonomic is a pragma on the proc itself; no extra registration is
needed.

### Pattern

```nim
import proptest/symex

# Real impl runs when the proc is called outside symex; the body
# is whatever you'd write normally.
proc readSensor(channel: int): int {.symexOpaque.} =
  ## Reads a hardware register. Walker treats this as a black box.
  ...

# The SUT — unchanged from how it'd be written without symex.
proc dispatch(channel: int) =
  let v = readSensor(channel)
  if v > 1000:
    symexTarget("alarm")

# Symex returns sxUnknown — honest under the opaque abstraction.
# The path condition `v > 1000` is satisfiable in the abstract
# model, but we can't prove the *concrete* run satisfies it because
# readSensor's actual output is sensor-dependent.
let r = symexFind(dispatch, tLabel("alarm"))
doAssert r.status == sxUnknown
```

### What it *doesn't* do

The pragma doesn't make `readSensor` *fast* under symex, *correct*
under symex, or eliminate the need to test it elsewhere. It just
admits the walker has nothing to say about the proc, then lets the
rest of the SUT be reasoned about cleanly.

If you want symex to *prove* something downstream of the opaque
proc — say, that *given* the alarm path is taken, the handler
behaves correctly — write a wrapper SUT that takes the opaque
proc's hypothetical output as a parameter:

```nim
proc handleAlarm(reading: int) =
  doAssert reading > 1000
  symexAssert(reading > 0)  # invariant we want to verify

let r = symexFind(handleAlarm, tAssertionViolation())
# Now r.status = sxUnsat (assuming the invariant holds) — symex
# proves the handler is sound under the precondition.
```

### Out of scope

- **Specifying the return value's range.** v1 of the pragma admits
  total ignorance. A future extension could let you write
  `{.symexOpaque(returnRange: 0..1023).}` to encode a known
  domain. Tracked as a follow-up; the pragma's empty form is the
  stable v1 contract.
- **Modelling side effects on parameters.** An opaque proc with
  `var T` parameters: v1 doesn't update the symbolic environment
  for the mutation. Use a separate explicit assignment after the
  call if you need to model the effect.
- **Pure-symbolic stubs** (KLEE-style modelling DSLs where you
  write a *symbolic body* for the proc) are a different extension
  shape, deferred to v2.

## Extending the built-in registry

For proptest's maintainers: stdlib procs the walker should
understand *symbolically* live in
`src/proptest/smt/stdlib_models.nim`:

```nim
type StdlibModelKind* = enum
  smkSeqLen
  smkSeqIndex
  smkTableIndex
  smkTableContains
  smkSetContains
  smkOpaqueEffectful
  # …

proc getStdlibModelFor*(callee: string, recvKind: IRTypeKind): StdlibModel
```

To add a new stdlib model:

1. Add a `StdlibModelKind` variant.
2. Add a dispatch case in `getStdlibModelFor` keyed on the Nim
   proc name + receiver kind.
3. Wire the parser (`src/proptest/smt/dsl_parser.nim`) to emit the
   right IR for the new kind — usually a specialised `iek*` expr
   or `is*` stmt.
4. Wire the walker (`src/proptest/smt/runtime.nim`) to interpret
   the new IR.
5. Add a test under `tests/tsymex_phase5_models.nim` (or open a
   new file) covering the symbolic behaviour.

The registry is closed-enum by design: every supported stdlib
proc has a known type signature, and the walker dispatches on the
enum. Reach for `{.symexOpaque.}` when the semantics *aren't*
worth modelling exactly.

### When to register vs. mark opaque

| Question | Register | Opaque |
|---|---|---|
| Is the proc widely used in real SUTs? | yes | maybe |
| Is the symbolic semantics simple? | yes | no |
| Does the walker have the right primitive? | yes | no |
| Would `sxUnknown` defeat your use case? | yes | no |

If you're unsure, ship as opaque first; promote to registered if
real SUTs demand soundness.
