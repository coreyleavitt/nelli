# RFC-0016 S8ck-r: a Nim 2.2.10 ORC/ARC codegen leak, stock and patched
# (nimlang/nim:2.2.10 and ghcr.io/coreyleavitt/nim:2.2.10 both reproduce it).
#
#   nim c -r --mm:orc -d:useMalloc --passC:-fsanitize=address \
#     --passL:-fsanitize=address tests/asan/nim_firstwrite_leak.nim
#
# LeakSanitizer reports each `leaks*` proc's first buffer; `fixed` is clean.
#
# Mechanism (compiler/sempass2.nim `initVar`, injectdestructors.nim
# `genSink`). sempass2 marks an assignment `nfFirstWrite` when the variable is
# not in its definitely-initialized set and the assignment is in the loop
# level the variable was declared at. A write under a `for`/`while`/`if`
# without `else` is dropped from that set when the construct ends (the loop
# may run zero times; `trackWhile`/`nkForStmt`/`trackIf` reset `init`), and
# a mutation through a non-`out` `var` parameter (`add`) is not an
# initialization. So the first plain assignment after such a write is marked
# a first write, and genSink compiles it to a bitwise copy (nkFastAsgn) that
# never destroys the value the variable already holds. An initializer on
# the declaration is the variable's first write, and the later assignment is
# an ordinary sink again.
#
# nelli met it in pcre_select.normalize (`var nx` filled in a `for`, then
# `nx = pruned`): 1272 bytes in 9 allocations under
# tsymex_phase15_S6b_regex. Not run by any job: it is the evidence for the
# workaround there and for a toolchain fix of sempass2.

proc leaksAdd(a: seq[int]): int =
  var nx: seq[int]
  for x in a: nx.add x
  nx = @[9]          # the buffer `add` grew is never freed
  nx.len

proc leaksIf(a: seq[int]): int =
  var nx: seq[int]
  if a.len > 0: nx = @[a[0], a[1]]
  nx = @[9]          # the conditional value is never freed
  nx.len

proc fixed(a: seq[int]): int =
  var nx: seq[int] = @[]
  for x in a: nx.add x
  nx = @[9]
  nx.len

echo leaksAdd(@[1, 2, 3]) + leaksIf(@[1, 2, 3]) + fixed(@[1, 2, 3])
