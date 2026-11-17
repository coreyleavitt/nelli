## S8ck-r planted defect: a heap block whose last pointer is dropped. Built
## with the K8c flags and run under the job's ASAN_OPTIONS/LSAN_OPTIONS
## (scripts/asan-slice.sh), this MUST exit non-zero with a LeakSanitizer
## report naming `leakOne`; the self-test fails if it exits 0, which is what a
## job that silently turned leak detection off (detect_leaks=0, a suppression
## that swallows everything, a lost useMalloc) would do. Not named t*.nim on
## purpose: it is a deliberately failing program, registered nowhere in
## nelli.nimble.
proc leakOne(): int {.noinline.} =
  var p = cast[ptr array[64, int]](alloc(sizeof(array[64, int])))
  p[][0] = 42
  result = p[][0]
  p = nil   # the only pointer to the block is gone

var total = 0
for i in 0 ..< 8: total += leakOne()
echo "planted leak ", total
