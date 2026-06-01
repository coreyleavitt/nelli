# Bug: explain phase aborts with uncaught `OverflowDefect` during replay

> **ROOT CAUSE: this is a Nim regression, not a proptest logic bug.** Identical
> source, seed, and flags (`--mm:arc -d:useMalloc --panics:on --threads:on`):
>
> | Nim | Result |
> |-----|--------|
> | **2.2.0** | clean falsify, no defect ✅ |
> | **2.2.8** | `OverflowDefect` crash (5/5) ❌ |
> | **2.2.10** (latest) | `OverflowDefect` crash ❌ — still present |
>
> Introduced after 2.2.0 and **NOT fixed as of 2.2.10**. A spurious
> `OverflowDefect` is attributed to a bare `raise newException(...)` line
> (`datasource.nim:126`) that does no arithmetic — consistent with a
> codegen/runtime regression in the panics:on raise/stacktrace path under arc.
> **proptest's own arithmetic is not at fault.** What proptest *can* do is be
> defensive (below); the actual fix needs an upstream Nim bug report. The
> consumer (`nopal`) pins test builds to Nim 2.2.0 for now.

**Severity:** High — a falsified property can crash the whole test run instead
of reporting the counterexample. The falsification *is found* (shrinking
completes), but the **explain** phase then dies with an unhandled `OverflowDefect`
before the report renders, so the user sees a Nim stack trace and a nonzero exit
with **no counterexample printed**.

**Discovered:** while writing property tests for an external project
(`nopal`, FNV-1a + linear-probing mark assignment). proptest correctly
falsified a "reorder invariance" property, then crashed in `explain`.

---

## Observed stack trace (verbatim from the crashing run)

```
.../proptest/dsl.nim(137)                 t_marks
.../proptest/engine.nim(179)              forAllWithExamples
.../proptest/engine.nim(151)              runForAllPipeline
.../proptest/engine/pipeline.nim(140)     runPipeline
.../proptest/engine/phases.nim(302)       explainPhase
.../proptest/engine/targeting.nim(432)    explain
.../proptest/engine/eval.nim(74)          evalReplay
.../proptest/strategy.nim(105)            generate
   <user strategy>                        :anonymous     # lists(strings()), sampledFrom(...)
.../proptest/strategy.nim(338)            :anonymous     # lists element-loop
.../proptest/datasource.nim(146)          drawBoolean
.../proptest/datasource.nim(126)          takeReplay
/opt/nim/lib/system/fatal.nim(62)         sysFatal
Error: unhandled exception: over- or underflow [OverflowDefect]
```

- `targeting.nim:432` is `let e = evalReplay(s, prop, trial)` inside `explain`,
  replaying a **perturbed** choice sequence.
- `eval.nim:74` is `x = s.generate(ds)` — and it is wrapped in a `try` that has
  an `except Defect` arm (`eval.nim:85`). **The defect escaped that arm anyway.**

## UPDATE — the bug is `--panics:on`-dependent and invisible without it

Follow-up experiments (same seed, same source `e204908`, same machine) isolate
the trigger to **one flag**. Built from the *exact* property below importing the
*real* `assignMarks`:

| Build | Result |
|---|---|
| `--mm:arc --threads:on --panics:off --stacktrace:on` | **clean falsify**, exit 1, *no defect at all* |
| `--mm:arc --threads:on --panics:on  --stacktrace:on` | **`OverflowDefect` crash**, the trace above, exit 1 |

Reproduced **5/5 deterministically** under panics:on. So:

- **This is why a clean-room repro "falsifies cleanly."** Nim defaults to
  `--panics:off` for non-`-d:release` builds, and most proptest dev/test runs
  (including its own `nimble test`) are panics:off. Under panics:off the run
  **does not raise the defect at all** — I instrumented the `except Defect` arm
  at `eval.nim:85` and it never fired. The bug is *latent*, not absent.
- **The consumer build is panics:on.** `nopal/config.nims` sets
  `switch("panics", "on")` (alongside `mm=arc`, `-d:useMalloc`), so every nopal
  test binary inherits it. That is the peculiarity: the bug only surfaces in a
  panics:on consumer, replaying a specific perturbed sequence.
- **The vendored proptest is byte-identical to current `HEAD` (`e204908`)** —
  `diff` of `nopal/_deps/proptest/.../datasource.nim` vs the working tree is
  clean. The line numbers are **not** stale; `datasource.nim:126` /`:146` are
  current. The "since-refactored" theory is ruled out.
- **An inlined/simplified `assignMarks` does NOT reproduce**, even under
  panics:on. The crash requires the *real* function: the explain phase only
  overflows on the specific shrunk+perturbed choice sequence that the real
  collision/probing pattern produces. Reductions change that sequence and miss
  it. (This is why seed-sweeping an inlined repro finds nothing.)

### What the flag actually changes here

`Overrun` is `object of CatchableError` (`datasource.nim:23`) — so it is caught
the same way under both flags; it is *not* the culprit. There is also no
overflow-prone integer arithmetic in `takeReplay` / `drawBoolean` / the `lists`
element loop (`strategy.nim:333-344`) — only `inc ds.cursor`, small-int
comparisons, and `result.add`. Yet panics:on raises `OverflowDefect` attributed
to `datasource.nim:126` (a `raise newException(Overrun, …)` statement, which
performs no arithmetic).

That combination points away from "a plain `a+b` overflowed in proptest logic"
and toward a **panics:on × stacktrace × arc interaction in the exception/raise
machinery** during the explain-phase replay — i.e. the overflow is surfacing in
the *raise path itself* (exception setup / stack-trace recording) under
panics:on, not in arithmetic proptest wrote. The line attribution (`:126`, a
bare `raise`) is consistent with that: it's the last source line entered before
`sysFatal`, not an arithmetic site.

**Open question for the fix owner:** is the `OverflowDefect` (a) raised inside
`s.generate(ds)` and therefore *should* be caught by `eval.nim:85` but isn't,
because under panics:on `except Defect` is statically dead — in which case the
explain loop in `targeting.nim:419-436` must defend itself (e.g. skip a
perturbation that faults, since it cannot rely on `evalReplay` swallowing it
when panics:on); or (b) a genuine runtime/codegen overflow in the raise path
that exists regardless of catchability and must be fixed at the source. Both are
worth confirming; (a) is the robustness fix that makes explain safe for *any*
panics:on consumer, (b) is the root cause.

## The crux

`evalReplay` *looks* defended:

```nim
# eval.nim ~70-88
var ds = newReplaySource(candidate)
try:
  x = s.generate(ds)
except Rejection, Overrun:
  return Eval[T](kind: ekRejected)
...
except Defect as e:                       # <-- should catch OverflowDefect
  return Eval[T](kind: ekFalsified, ..., fMsg: "strategy crashed: " & ...)
```

Yet an `OverflowDefect` raised under `generate` reached top level. So one of:

1. **The defect is raised outside this `try`.** The trace bottoms out in
   `drawBoolean -> takeReplay`, which `generate` calls — that *is* inside the
   try. But if any arithmetic runs in a destructor/`=destroy`, a deferred
   finalizer, or across the `--threads:on` boundary, it won't be caught here.
   (Build used `--threads:on`.)
2. **A genuine signed over/underflow exists in the replay path** and should be
   fixed at the source rather than merely caught. `takeReplay` itself
   (`datasource.nim:120-127`) only does a bounds check + `inc ds.cursor` and
   raises `Overrun` on mismatch — no arithmetic that overflows. So the overflow
   is most likely in the **`lists` element loop** (`strategy.nim:338`) or the
   **length/size accounting** it does between `drawBoolean` calls, exercised
   only on certain perturbed sequences.
3. **`except Defect` doesn't bind here** under the compile flags in use
   (`--mm:arc`, `--threads:on`, panics off). Worth confirming `OverflowDefect`
   is actually catchable in this build configuration — if panics are on for any
   reason, `except Defect` is dead.

## Likely-relevant code

- `engine/eval.nim:65-94` — `evalReplay`, the `except Defect` arm at ~85.
- `engine/targeting.nim:378-417` — `perturbations`. Note line ~393:
  `if lo + toInt128(1) <= hi: cand.add lo + toInt128(1)` — `Int128` add that
  could overflow if any integer choice constraint has `min` at the `Int128`
  ceiling. Probably not the trigger here (these strategies use small ranges),
  but it's an unguarded `+1` on a boundary and worth hardening.
- `engine/targeting.nim:419-436` — `explain`, calls `evalReplay` per perturbation.
- `datasource.nim:120-154` — `takeReplay` / `drawBoolean` (replay path 145-147).
- `strategy.nim:~338` — the `lists` element-at-a-time generator (the `:anonymous`
  frame); prime suspect for the overflowing arithmetic.

## Reproduction

**Deterministic (5/5)** under the exact recipe below — but only with ALL of:
`--panics:on`, the **real** `assignMarks` (not an inlined copy), the full
`validMasks` set incl. `0xFFF00`, default seed `0x1234567890abcdef`, `--mm:arc`,
`--threads:on`. Drop panics:on → clean falsify, no crash. Inline/simplify
`assignMarks` → no crash. That fragility is the whole reason it's hard to repro
from a clean room.

### Exact environment that crashes

- Image: `ghcr.io/coreyleavitt/nopal-toolchain:latest` (openSUSE Tumbleweed +
  Nim 2.2). A clean `docker.io/nimlang/nim:2.2.0` may behave differently
  (glibc vs the toolchain's libc; and unless you also pass `-d:useMalloc` the
  allocator differs).
- Flags (the consumer inherits these from `nopal/config.nims`):
  `--mm:arc -d:useMalloc --panics:on` + `--threads:on` on the CLI.
- proptest at `e204908` (vendored copy is byte-identical to HEAD).

### Property skeleton — standalone, but NOTE: this inlined form FALSIFIES yet does NOT crash

The block below is the property shape, with `assignMarks` inlined so it's
self-contained. **It will print a counterexample and `[FAILED]` but will not
crash** even under panics:on — the inlined function reaches a different
shrunk/perturbed sequence than the real one. Use it to confirm the harness runs;
use the *real-import* recipe further down to actually trigger the crash.

```nim
import std/[unittest, sequtils, algorithm, tables]
import proptest

# FNV-1a + linear-probing slot assignment (order-dependent under collisions).
proc assignMarks(names: openArray[string], markMask: uint32): seq[uint32] =
  result = newSeq[uint32](names.len)
  if markMask == 0 or names.len == 0: return
  let step = markMask and (not markMask + 1)
  let maxSlots = int(markMask div step) - 1
  if maxSlots < 1: return
  var used = newSeq[bool](maxSlots + 1)
  let n = min(names.len, maxSlots)
  for i in 0 ..< n:
    var h = 2166136261'u32
    for b in names[i]:
      h = h xor uint32(b); h = h * 16777619'u32
    var slot = int(h mod uint32(maxSlots)) + 1
    var probes = 0
    while used[slot] and probes < maxSlots:
      slot = (slot mod maxSlots) + 1; inc probes
    if probes >= maxSlots: continue
    used[slot] = true
    result[i] = uint32(slot) * step

proc markMap(names: seq[string], mask: uint32): Table[string, uint32] =
  let r = assignMarks(names, mask)
  for i, n in names: result[n] = r[i]

func slotsFor(mask: uint32): int =
  let step = mask and (not mask + 1)
  int(mask div step) - 1

const masks = [0x0300'u32, 0x0700'u32, 0x0F00'u32, 0x3F00'u32, 0xFF00'u32, 0xFFF00'u32]

suite "explain-phase overflow":
  property "reorder invariance of assignMarks":
    given names0 in lists(strings()), mask in sampledFrom(masks)
    let names = names0.deduplicate
    assume names.len >= 2 and names.len <= slotsFor(mask)
    let fwd = markMap(names, mask)
    let rev = markMap(names.reversed, mask)
    ensure names.allIt(fwd[it] == rev[it])
```

### Reliable crash recipe — real `assignMarks` + panics:on

Replace the inlined `assignMarks`/`markMap` with an import of the real function
and compile with `--panics:on`. This crashes **5/5**:

```nim
import std/[unittest, sequtils, algorithm, tables]
import proptest
import ../src/nftables/marks   # the REAL FNV + linear-probing assignMarks

const validMasks = [0x0300'u32, 0x0700'u32, 0x0F00'u32, 0x3F00'u32, 0xFF00'u32, 0xFFF00'u32]
func slotsFor(mask: uint32): int =
  let step = mask and (not mask + 1)
  int(mask div step) - 1
proc markByName(names: openArray[string], mask: uint32): Table[string, uint32] =
  let r = assignMarks(names, mask)
  for i, n in names: result[n] = r[i].mark

suite "explain-phase overflow":
  property "stable across config reorder":
    given names0 in lists(strings()), mask in sampledFrom(validMasks)
    let names = names0.deduplicate
    assume names.len >= 2 and names.len <= slotsFor(mask)
    let fwd = markByName(names, mask)
    let rev = markByName(names.reversed, mask)
    ensure names.allIt(fwd[it] == rev[it])
```

```bash
# from the nopal repo (so ../src/nftables/marks resolves and config.nims
# supplies --mm:arc -d:useMalloc --panics:on); --threads:on on the CLI.
podman run --rm -v "$PWD":/src -w /src ghcr.io/coreyleavitt/nopal-toolchain:latest \
  nim c -r --threads:on --hints:off tests/treorder.nim
# -> Error: unhandled exception: over- or underflow [OverflowDefect]

# Flip just one flag to make it vanish (clean falsify, no defect):
podman run --rm -v "$PWD":/src -w /src ghcr.io/coreyleavitt/nopal-toolchain:latest \
  nim c -r --threads:on --panics:off --hints:off tests/treorder.nim
```

If you want to observe the defect *without* panics:on (so you can read its
stack at the raise site), temporarily add to the `except Defect` arm at
`eval.nim:85`:
`stderr.writeLine($e.name & ": " & e.msg & "\n" & e.getStackTrace())` — but note
that under panics:off in this case the arm **never fires**, which is itself the
diagnostic: the defect isn't raised inside the `generate` try at all under
panics:off. It only materializes under panics:on.

## Suggested fixes

1. **Make `explain`/`evalReplay` bulletproof against any defect.** A perturbation
   that yields an invalid/overflowing replay should classify as "did not pass"
   (treat like `ekRejected` / `ekFalsified`), never abort the run. Confirm the
   `except Defect` at `eval.nim:85` actually fires in the `--mm:arc
   --threads:on` build; if a finalizer/destructor path can raise outside the
   `try`, wrap the perturbation loop in `targeting.nim:explain` itself so a bad
   perturbation is skipped (`continue`) rather than propagated.
2. **Find and fix the root overflow.** Instrument the `lists` element loop
   (`strategy.nim:~338`) and any size/length accumulation in the replay path;
   reproduce with `--stacktrace:on --linetrace:on -d:nimDebugDlOpen` and a fixed
   seed. Harden the `lo + toInt128(1)` at `targeting.nim:393` to avoid the
   boundary `+1`.
3. **Regression test.** Once reduced to a deterministic seed, add it under
   `tests/` so the explain phase is covered for the "perturbation produces an
   invalid replay" case.

## Impact on the consumer

Until fixed, any falsified property whose shrunk sequence hits this path crashes
instead of reporting. Workaround in `nopal`: the offending property is parked
(commented out) so CI stays green. Re-enabling it is gated on this fix.
