# RFC-0016 S8ck-r: Nim 2.2.10 (stock and patched) never destroys a
# threadvar when its thread exits, under ORC/ARC, even for a thread made by
# createThread.
#
#   nim c -r --threads:on --mm:orc -d:useMalloc --passC:-fsanitize=address \
#     --passL:-fsanitize=address tests/asan/nim_threadvar_exit_leak.nim
#
# LeakSanitizer reports the seq `body` grew: once the thread is gone, its
# thread-local storage no longer roots it. nelli keeps its walker state in
# threadvars, so a symexFind run on a thread that then exits leaves that
# state behind (tsymex_rfc0005_s8cb_replay's foreign thread, about 100 KB).
# Not run by any job: it is the evidence for the entry in tests/asan/lsan.supp.

import std/typedthreads

var tv {.threadvar.}: seq[int]

proc body() {.thread.} =
  for i in 0 ..< 100: tv.add i

var th: Thread[void]
createThread(th, body)
joinThread(th)
echo "threadvar exit done"
