# RFC-0016 S8ck-r: a Nim 2.2.10 ORC/ARC leak of an owned temporary when a
# later argument of the same call raises a Defect from an inline runtime
# check (here `div`'s zero check, `--panics:off`).
#
#   nim c -r --mm:orc -d:useMalloc --passC:-fsanitize=address \
#     --passL:-fsanitize=address tests/asan/nim_defect_temp_leak.nim
#
# LeakSanitizer reports `leaks`'s seq (24 bytes) and its one string; `fixed`
# is clean.
#
# `"s".split(",").join($(1 div z))` builds the seq `split` returns into a
# temporary, then evaluates the separator. The zero check of `div` raises
# DivByZeroDefect inline, and the seq temporary is not destroyed on the
# Defect's way out (34 bytes in 2 allocations, patched toolchain; not
# traced into the compiler further). Evaluating the raising operand first,
# into its own `let`, leaves nothing owned live at the raise.
#
# nelli met it in tests/tsymex_rfc0005_s5_str.nim's `probe` oracle (24 bytes
# direct, 10 indirect). Not run by any job: it is the evidence for the change
# there.

import std/strutils

proc leaks(z: int): int =
  try:
    discard "s".split(",").join($(1 div z))
  except DivByZeroDefect:
    result = 1

proc fixed(z: int): int =
  try:
    let sep = $(1 div z)
    discard "s".split(",").join(sep)
  except DivByZeroDefect:
    result = 1

echo leaks(0) + fixed(0)
