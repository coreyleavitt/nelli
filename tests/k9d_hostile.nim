## RFC-0016 K9d-7b. A suite module that overloads stdlib names for the very
## types `pinFind` generates domains of, as RFC-0005 S8c does on purpose. A
## generic routine's overloaded calls are looked up again where it is
## instantiated, so before K9d-7b the generated `int` domain here was empty
## (`add` appended nothing) and a `seq[int16]` domain indexed past its core
## (`len` said 7). It also builds a `seq[seq[cuint]]` before a `seq[uint32]`
## domain is built: `system.add`'s shared instance for the two did not
## compile in C. `tsymex_0016_k9d_pinfind` calls the probes below.
import std/[sets]
import nelli/symex
import ./s8cu_helpers

proc add(s: var seq[int], x: int) = discard (s, x)
  ## appends nothing
proc len(s: seq[int16]): int = 7
  ## not the length
iterator items(s: seq[int8]): int8 = yield 99'i8
  ## one element, whatever the sequence holds
proc contains(s: HashSet[int], x: int): bool = x == 99
  ## membership is "is 99"

var cuints: seq[seq[cuint]]
cuints.add @[1.cuint]

proc sutIntNever(a, b: int) =
  if a > 5 and a < 3 and b == 0: symexTarget("hit")

proc sutI16Never(xs: seq[int16]) =
  if xs.len > 2 and xs.len < 2: symexTarget("hit")

proc sutI8Never(xs: seq[int8]) =
  if xs.len == 1 and xs[0] > 5 and xs[0] < 3: symexTarget("hit")

proc sutU32Never(xs: seq[uint32]) =
  if xs.len > 0 and xs[0] > 5'u32 and xs[0] < 3'u32: symexTarget("hit")

proc hostileInt*(): tuple[st: SymexStatusKind, n: int] =
  let d = boundaryOf(int)
  (pinFind(sutIntNever, tLabel("hit")).status, system.len(d.values))

proc hostileSeqI16*(): tuple[st: SymexStatusKind, n: int] =
  let d = boundaryOf(seq[int16])
  (pinFind(sutI16Never, tLabel("hit")).status, system.len(d.values))

proc hostileSeqI8*(): SymexStatusKind =
  pinFind(sutI8Never, tLabel("hit")).status

proc hostileSeqU32*(): SymexStatusKind =
  pinFind(sutU32Never, tLabel("hit")).status
