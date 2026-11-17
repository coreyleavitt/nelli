## K8c planted defect 1: a real heap use-after-free in plain Nim memory.
## Built with the K8c flags (scripts/asan-slice.sh) this MUST abort with an
## AddressSanitizer heap-use-after-free report; the job's self-test step fails
## if it exits 0. Not named t*.nim on purpose: it is a deliberately failing
## program, registered nowhere in nelli.nimble.
proc main() =
  let p = cast[ptr int](alloc(sizeof(int)))
  p[] = 42
  dealloc(p)
  # read through the dangling pointer
  let v = cast[ptr int](p)[]
  echo "read ", v
main()
