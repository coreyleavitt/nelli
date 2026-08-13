## `Opt[T]` — an optional that never instantiates `default(T)`.
##
## A faithful `std/options.Option` in surface, but backed by `ref T` (`nil`
## ⇒ empty), so the absent state is the zero value `Opt[T]()` and never
## forces `default(T)` / `reset(T)`. This lets the engine thread a *value of
## the user's element type* through every "maybe-absent" site (counterexample,
## draw, shrunk example, eval result) even when that type is a
## `{.requiresInit.}` object variant with no valid default — which `std`
## `Option` (and `seq`'s shrink branch) cannot, because their absent/removed
## slot demands `default(T)`.
##
## See `bugbusting/nim/issue-21350-…` (Trigger 2). `seq[T]` (Trigger 1) is
## handled upstream by #25859; only the `Option[T]` sites are boxed here.
##
## Constructors are deliberately `box` / `empty`, **not** `some` / `none`, so
## `Opt` coexists with `std/options` in the same module without making
## `some(x)` ambiguous. The read surface mirrors `Option`
## (`isSome`/`isNone`/`get`/`unsafeGet`/`map`/`==`/`$`/`items`) so call sites
## that consume a counterexample port verbatim.
##
## Storage is reference-backed: copying an `Opt` shares the boxed value. The
## engine only ever *writes a boxed value once and reads it*, so this is
## observationally identical to value semantics. A `=copy` hook giving true
## value semantics is achievable with no `default(T)` (`new(dst.p); dst.p[] =
## src.p[]`) — deferred until a use actually needs it.

import std/options  # for UnpackDefect, to mirror Option.get's failure mode

type
  Opt*[T] = object
    ## Optional value of `T`. The zero value (`p == nil`) is "empty".
    p: ref T

proc box*[T](x: T): Opt[T] =
  ## Wrap a present value. Allocates one box; never touches `default(T)`.
  new(result.p)
  result.p[] = x

proc empty*[T](): Opt[T] = discard
  ## The absent value — the zero value, `p == nil`. Exists so call sites can
  ## be explicit (`empty[T]()`) where a defaulted field won't do.

proc isSome*[T](o: Opt[T]): bool {.inline.} = o.p != nil
proc isNone*[T](o: Opt[T]): bool {.inline.} = o.p == nil

proc get*[T](o: Opt[T]): T =
  ## The boxed value. Raises `UnpackDefect` when empty, matching `Option.get`.
  if o.p == nil:
    raise newException(UnpackDefect, "Opt is empty")
  o.p[]

proc get*[T](o: Opt[T], fallback: T): T {.inline.} =
  ## The boxed value, or `fallback` when empty.
  if o.p != nil: o.p[] else: fallback

proc unsafeGet*[T](o: Opt[T]): T {.inline.} =
  ## The boxed value without the empty check; UB if empty. Use only after
  ## an `isSome` guard.
  o.p[]

proc map*[T, U](o: Opt[T], f: proc(x: T): U): Opt[U] =
  ## `box(f(get))` when present, else `empty`.
  if o.p != nil: box(f(o.p[])) else: empty[U]()

proc `==`*[T](a, b: Opt[T]): bool =
  ## Value equality: both empty, or both present with equal payloads.
  (a.p == nil and b.p == nil) or
  (a.p != nil and b.p != nil and a.p[] == b.p[])

proc `$`*[T](o: Opt[T]): string =
  if o.p != nil: "box(" & $o.p[] & ")" else: "empty"

iterator items*[T](o: Opt[T]): T =
  ## Yields the value when present (zero or one element), like `Option`.
  if o.p != nil: yield o.p[]

# ---------------------------------------------------------------------------
# Examples[T] — an append-only boxed list, same `default(T)`-avoidance as Opt.
# ---------------------------------------------------------------------------

type
  Examples*[T] = object
    ## An append-only list of `T` that stores each element **boxed**
    ## (`ref T`), so it never instantiates `seq[T]`'s grow/shrink path —
    ## and therefore never `reset(T)` / `default(T)`. A plain `seq[T]` of a
    ## `{.requiresInit.}` element (or any no-valid-default type) can't be
    ## grown without instantiating `setLen`'s shrink branch, whose
    ## `reset x[i]` is either a hard "no default" error or (under
    ## `--threads:on`) a strict-effects `RootEffect` error. `Examples`
    ## sidesteps both: a `ref`'s reset is a nil-assignment.
    ##
    ## It presents a `seq`-like surface (`add` / `len` / `items` / `pairs`)
    ## with the boxing fully hidden — callers only ever see `T`. The engine
    ## uses it for the explicit-examples list; the zero value is empty.
    boxes: seq[ref T]

proc add*[T](xs: var Examples[T], x: T) =
  ## Append `x` (heap-boxed). Never default-constructs or resets a `T`.
  var r: ref T
  new(r)
  r[] = x
  xs.boxes.add r

proc len*[T](xs: Examples[T]): int {.inline.} = xs.boxes.len

iterator items*[T](xs: Examples[T]): T =
  for r in xs.boxes: yield r[]

iterator pairs*[T](xs: Examples[T]): (int, T) =
  for i in 0 ..< xs.boxes.len: yield (i, xs.boxes[i][])

proc toExamples*[T](xs: openArray[T]): Examples[T] =
  ## Build an `Examples[T]` from any open array. `openArray` is a view, so
  ## this never instantiates `seq[T]` for the element type.
  for x in xs: result.add x
