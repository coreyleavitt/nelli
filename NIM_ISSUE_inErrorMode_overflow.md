### Nim Version

Linux amd64. Reproduces on devel and every release since 2.2.8; correct on 2.2.6
and earlier.

```
Nim Compiler Version 2.3.1 [Linux: amd64]    (devel, built 2026-05-31)
Nim Compiler Version 2.2.10 [Linux: amd64]   (Compiled 2026-04-24)
Nim Compiler Version 2.2.0 [Linux: amd64]    (Compiled 2024-10-02)   # correct
```

### Description

With `--exceptions:goto` and `--panics:on`, the compiler does not emit the
error-flag check after an indirect closure call whose result is passed straight
into another call, e.g. `result.add elem(src)`. With `--panics:off` the check is
emitted. Because of this, a raise inside the closure is not propagated: the loop
keeps running, and the next raise reaches `inc nimInErrorMode`. That flag is a
`bool`, so incrementing it while it is already `true` overflows, which under
`--panics:on` is a fatal `OverflowDefect`.

Minimal reproduction, stdlib only and deterministic:

```nim
type
  Overrun = object of CatchableError
  Source = object
    data: seq[bool]
    cursor: int
  ElemFn = proc(src: var Source): bool {.closure.}

proc drawBool(src: var Source): bool =
  if src.cursor >= src.data.len: raise newException(Overrun, "exhausted")
  result = src.data[src.cursor]; inc src.cursor

proc listRun(elem: ElemFn, src: var Source): seq[bool] =
  result = @[]
  while true:
    if not src.drawBool(): break
    result.add elem(src)        # closure call

let elem: ElemFn = proc(src: var Source): bool = src.drawBool()
var src = Source(data: @[true])
discard listRun(elem, src)
```

```
nim c -r --mm:arc --panics:on repro.nim
```

### Current Output

```
Error: unhandled exception: over- or underflow [OverflowDefect]
```

### Expected Output

The `Overrun` raised in the closure should propagate, as it does with
`--panics:off` and on Nim 2.2.6 and earlier:

```
Error: unhandled exception: exhausted [Overrun]
```

### Known Workarounds

Build with `--panics:off`, or use Nim 2.2.6 or earlier.

### Additional Information

Bisected (no skips) to PR #25295, "system.nim refactorings for IC". It landed on
devel as `0f7b3784` and was cherry-picked to `version-2-2` as `431e01eaf`; the
parent `a5e73ff40` is correct. #25295 touches only `lib/` (no `compiler/` files),
so the regression is in what the compiler infers from `lib/system`, not in
codegen. Applying only its `excpt.nim` changes onto the parent stays correct, so
the trigger is the `system.nim` reorganization; I could not split it further by
file because the commit moves declarations across `system.nim`,
`gc_interface.nim`, and `threadimpl.nim`.

Generated C for the `result.add elem(src)` line:

```c
// --panics:off (correct)             // --panics:on (bug)
T8_ = elem_p0.ClP_0(src_p1, ...);     T8_ = elem_p0.ClP_0(src_p1, ...);
if (NIM_UNLIKELY(*nimErr_)) goto ...; add__...(&result, T8_);   // no check emitted
add__...(&result, T8_);
```

The direct call just above it (`src.drawBool()`) keeps the check under both
settings; only the indirect closure call loses it under `--panics:on`. A plain
top-level proc in that position also works, so the closure is required.

`--mm:orc` behaves the same; threads on/off, gcc vs clang, and `-d:useMalloc`
make no difference.

| | `--panics:on` | `--panics:off` |
|---|---|---|
| devel 2.3.1, 2.2.10, 2.2.8 | crash | correct |
| 2.2.6, 2.2.4, 2.2.2, 2.2.0 | correct | correct |

Related:

- #19857 (closure raise "skipped" under goto): same failure mode. The `let v =
  fn()` repro there works now, but this `result.add elem(src)` shape does not.
- #25658 / #25660 (overflowed `*=` causing `sysFatal` under goto): same pattern
  of a skipped raise followed by a misbehaving second raise, with an integer
  trigger instead of a closure. Fixed by #25660, but this closure case still
  crashes on devel.
