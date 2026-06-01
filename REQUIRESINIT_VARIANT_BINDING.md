# Issue: `given` can't bind a `{.requiresInit.}` *variant* (case object) — `seq[T]`/`Option[T]` reset

> **Status: OPEN.** Follow-on to `REQUIRESINIT_DSL_FRICTION.md` (✅ resolved). That fix
> eliminated proptest's *default-construction* of the element type, which made
> **plain** `{.requiresInit.}` objects bindable. **Variant** (`case`-object)
> `requiresInit` types still fail — through a *different* mechanism (seq/Option
> `reset` instantiation, below). Discovered in the `nopal` project (binding
> `Result[T, E]` and `StateEvent`, both `{.requiresInit.}` variants).

**Type:** enhancement / Nim-interaction papercut. **Severity:** medium — blocks
`given x in strat` (and explicit examples) for any `{.requiresInit.}` *variant*
type, forcing a tuple-proxy workaround (generate a plain tuple, build the variant
in the property body). Common for defensive codebases that use `Result`/`Option`-
style variants with `{.requiresInit.}` to forbid a meaningless zero value.

**Observed on:** Nim **2.2.4** (the version `nopal` pins). The underlying Nim
behavior is a `setLen`/`reset` instantiation rule, so it is expected on the whole
2.2.x line (not bisected further here).

---

## Symptom

```nim
import proptest

type Result[T, E] {.requiresInit.} = object   # requiresInit VARIANT
  case o: bool
  of true:  v: T
  of false: e: E

proc resultStrat(): Strategy[Result[int, string]] =
  integers(0, 9).map(proc(x: int): Result[int, string] =
    Result[int, string](o: true, v: x))

suite "x":
  property "bind a requiresInit variant":
    given r in resultStrat()
    ensure r.o
```

```
.../proptest/dsl.nim(137)            forAllWithExamples
.../proptest/engine.nim(198)         reqInitSafeSeq
.../proptest/engine.nim(164)         setLen          <-- seq[T] grow instantiates setLen
.../system/seqs_v2.nim(175)          shrink          <-- setLen's shrink branch
.../system/seqs_v2.nim(133)          reset
.../system.nim(934) Error: The Result type requires the following fields to be initialized: e.
```

A **plain** `{.requiresInit.}` object (non-variant) binds fine — only variants fail.

---

## Root cause

It's a Nim limitation that proptest *triggers* by storing the element type **by
value**:

1. `reset(x)` sets `x` to its default. A `{.requiresInit.}` **variant** has *no*
   valid default (the active branch's required field can't be defaulted), so
   `reset` of such a type is a **hard compile error** — this is arguably correct
   for `reset`.
2. Nim's `seq[T]` `setLen` is a single generic handling **both** grow and shrink;
   its shrink branch calls `reset` on removed elements. So **instantiating
   `seq[T].setLen` for any reason — including a growing `add` — instantiates
   `reset(T)`**, even though shrink is never reached at runtime.
3. Therefore *any* `seq[T]`/`Option[T]` of a `{.requiresInit.}` variant fails to
   compile, regardless of how it's used.

Minimal, proptest-free reproduction (the Nim core behavior):

```nim
type R[T, E] {.requiresInit.} = object
  case o: bool
  of true:  v: T
  of false: e: E

var s = newSeqOfCap[R[int, string]](2)
s.add R[int, string](o: true, v: 1)   # add -> grow -> setLen -> shrink -> reset(R) -> ERROR
s.setLen(0)
#  Error: The R type requires the following fields to be initialized: e.
```

(A plain `R[T] {.requiresInit.} = object` `v: T` — non-variant — compiles here;
its `reset` is valid.)

### Where proptest stores `T` by value (the trigger sites)
- `engine.reqInitSafeSeq` / the pipeline `explicit: seq[T]` (explicit examples).
- `Report[T].counterexample: Option[T]` (the falsifying value) — `Option[T]`'s
  `reset` likewise instantiates `reset(T)`.
- The draw/current value threaded through `engine/phases.nim`.

The earlier `REQUIRESINIT_DSL_FRICTION.md` fix made these stop *default-
constructing* `T` (→ plain requiresInit objects work), but it does not stop the
**`reset` instantiation** that `seq[T].setLen`/`Option[T]` pull in — which is what
the variant case hits.

---

## Proposed fix: box the internal element storage (`ref T`)

`ref T` sidesteps it entirely — a `ref`'s `reset` nils the pointer and never
instantiates `reset(T)`. Verified on 2.2.4:

```nim
var s = newSeqOfCap[ref R[int, string]](2)
var r = new(R[int, string]); r[] = R[int, string](o: true, v: 1)
s.add r
s.setLen(0)    # compiles — ref reset = nil, no reset(R)
```

So: store the bound element **boxed** throughout proptest's engine internals —
`seq[T] -> seq[ref T]` (examples / pipeline) and `Option[T] -> Option[ref T]`
(`Report.counterexample`, draw/current value) — while keeping the **public API
unchanged**: the property body still receives `x: T` (deref the box at the call
boundary), and the rendered counterexample still displays `T`.

**Scope:** `engine.nim` (`reqInitSafeSeq`, `forAll*`), `engine/pipeline.nim`
(`explicit`, the run state), `engine/phases.nim` (the `Report[T]` construction +
draw handling), and the `Report[T]` type. Keep proptest's own test suite green and
confirm shrinking + counterexample rendering are unaffected. Boxing adds one heap
allocation per stored value — negligible for a test tool.

**Alternative considered:** a custom grow-only container that never instantiates
`reset`/`shrink` for `T` (raw `UncheckedArray` + manual lifetime). More code than
boxing; same goal. Boxing is the simplest Nim-idiomatic route.

**Possible upstream Nim report:** instantiating `seq[T].setLen` for a grow-only
use pulls in the shrink branch's `reset(T)`, making the *whole* `setLen` fail for
a type whose `reset` is invalid even though shrink is never reached. Splitting
grow/shrink (or not instantiating `reset` on a pure-grow path) would let
`seq[requiresInit-variant]` compile without boxing. Not relied upon here.

---

## Verification matrix (Nim 2.2.4)

| element type | `seq[T].setLen` | bindable via `given` |
|---|---|---|
| plain `{.requiresInit.}` object | ✅ compiles | ✅ (post DSL-friction fix) |
| `{.requiresInit.}` **variant** | ❌ `reset` error | ❌ (this issue) |
| `ref` (of either) | ✅ compiles | ✅ (the proposed fix) |

## Consumer impact (nopal)
Until fixed, nopal binds `requiresInit` variants (`Result`, `StateEvent`, etc.)
via a tuple-proxy: a `Strategy` over a plain tuple + a `toX` builder invoked in the
property body. Once boxing lands, those proxies can be deleted and the types bound
directly with `given x in strat`.
