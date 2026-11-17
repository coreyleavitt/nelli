# RFC-0016 S8ck-r: a Nim 2.2.10 ORC/ARC leak through cursor inference, stock
# and patched (nimlang/nim:2.2.10 and ghcr.io/coreyleavitt/nim:2.2.10 both
# reproduce it).
#
#   nim c -r --mm:orc -d:useMalloc --passC:-fsanitize=address \
#     --passL:-fsanitize=address tests/asan/nim_cursor_strlit_leak.nim
#
# LeakSanitizer reports `leaks`'s string; `readAfter` is clean, and so is
# `leaks` with `--cursorInference:off`.
#
# A local string initialized from a literal, written with `s[k] = v`, and
# not read after the write is inferred to be a cursor, so no destructor is
# emitted for it. The write still runs nimPrepareStrMutationV2, which copies
# the literal to the heap, and that copy is never freed.
#
# nelli met it in tests/tsymex_rfc0005_s8ca_strings.nim's `sutCharOrder`
# (22 bytes, k = 0 and k = 1, where `raiser()` raised after the copy). Not
# run by any job: it is the evidence for the change there and for a
# toolchain fix of cursor inference.

proc plain(): char = 'z'

proc leaks(k: int): int =
  var s = "ab"
  s[k] = plain()     # the heap copy of "ab" is never freed
  0

proc readAfter(k: int): int =
  var s = "ab"
  s[k] = plain()
  s.len

echo leaks(1) + readAfter(1)
