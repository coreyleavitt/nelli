# UPS-01 (draft, not filed): Nim, a destructor's `try/except` swallows an in-flight exception on the C backend

Target: nim-lang/Nim. RFC-0016 section 5.6, decision D-0016-3. Drafted
2026-11-07 (W1-z). Nothing here has been filed; the issue URL goes in section
5.6 when it is.

## Title

C backend (goto exceptions): a `try/except` in a `=destroy` hook clears the
exception that is already propagating, so a `raise` that crosses the
destruction of a call's result temporary is lost

## Reproduction

One file, no dependencies (`purenim.nim`; the same text is in
`worker-reports/s8ce-purenim.nim` on `origin/worker-sls2`):

```nim
type Obj = object
  p: int

var destroyed = 0
proc mayRaise(x: int) {.raises: [ValueError].} =
  if x == 999: raise newException(ValueError, "x")

proc `=destroy`(o: Obj) {.raises: [].} =
  try:
    mayRaise(o.p)
    inc destroyed
  except CatchableError:
    discard

proc f(n: int): seq[Obj] =
  result = @[Obj(p: n)]
  if n > 0: raise newException(IOError, "boom")

proc g(n: int): seq[Obj] =
  result = @[Obj(p: 1)]
  result = f(n)          # reassignment from a call

proc h(n: int): int =
  let s = g(n)
  s.len

try:
  echo "returned normally: ", h(1), " (LOST)"
except IOError:
  echo "caught IOError (OK)"
```

```
nim c   --hints:off purenim.nim && ./purenim     # C backend
nim cpp --hints:off purenim.nim && ./purenim     # C++ backend
```

Control: with the `try/except` removed from `=destroy` the C backend is also
correct (the worker's `purenim_notry` variant, not reproduced in this draft).

## Versions

- Nim 2.2.10 (Linux amd64), default memory manager (ORC), default
  `--exceptions:goto` on the C backend.
- Observed on two builds of 2.2.10: the stock release tarball
  `nim-2.2.10-linux_x64.tar.xz` (compiler built 2026-04-24) and nelli's
  patched 2.2.10 (built 2026-08-09).
- gcc 12.2.0 (Debian 12), x86-64 Linux.
- Not tried: Nim devel, other platforms, `--mm:refc`, `--exceptions:setjmp`.

## Expected and actual

Expected: `caught IOError (OK)`. `f(1)` raises `IOError`; the exception must
reach the handler in the main module however many destructors run on the way.

Actual on the C backend: `returned normally: 1 (LOST)`. The `IOError` is gone
and `h` returns normally. The C++ backend prints `caught IOError (OK)`, so
the loss is C-only.

Mechanism, read from the generated C (nelli, nimcache of a larger program):
on the raise path of a reassigned call temporary the compiler emits
`if (NIM_UNLIKELY(*nimErr_)) { eqdestroy_(T20_); goto BeforeRet_; }`. The
destroy is entered with the error flag already set. Inside the hook the
`try` header begins with a flag check and then reaches the `except` landing
pad, which tests the *current* exception's type against `CatchableError`,
clears the flag (`*nimErr_ = NIM_FALSE`) and calls `popCurrentException()`.
That is the in-flight `IOError`, not an exception raised inside the hook.
After the destroy returns the flag is clear, so the `goto BeforeRet_` carries
no exception.

## How it was observed

- nelli RFC-0005 slice S8ce (2026-11): a Z3 value's `=destroy` held a `try`
  and any `raise` crossing a live Z3 term was lost on the C backend, giving a
  false `sxUnsat`, a false `sxSat` or a hidden `sxUnknown`. The worker's scan
  of the generated C found 50 hooks that pop an exception before the fix and
  0 after it.
- Reduced to the file above by the S8ce worker (`s8ce-work/probe/purenim.nim`).
- Re-run 2026-11-07 for this draft: the prebuilt `p_c` printed
  `returned normally: 1 (LOST)` and `p_cpp` printed `caught IOError (OK)`;
  the file was then rebuilt with the stock 2.2.10 tarball and gcc 12.2.0 and
  gave the same two results (`nim c`: LOST, `nim cpp`: OK).

Workaround in nelli: no `try` in any `=destroy`, `=copy` or `=dup` hook, and
`{.raises: [], quirky.}` on them (nim-z3 `27be0a0`, `cc5ffc9`).

Fileable as-is: yes (self-contained one-file reproduction; stock Nim 2.2.10 confirmed; the only gaps are a Nim devel check and a `--mm:refc` check, which an issue may leave to the maintainers)
