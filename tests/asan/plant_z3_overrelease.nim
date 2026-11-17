## K8c planted defect 2: the CRH-07 class, a reference-count error on a Z3 AST
## handle. The raw handle is released once more than it was retained, so libz3
## frees the AST while the Nim handle `s` is still live; the next use (and the
## handle's own `=destroy`) touches freed memory INSIDE libz3. Only an
## ASan-built libz3 reports that. With a stock libz3 the program either prints
## the stale string or crashes, and ASan sees nothing unless the free reaches
## free() twice.
import z3
import z3/ffi

proc main() =
  let ctx = newContext()
  let a = ctx.mkIntVar("a")
  let b = ctx.mkIntVar("b")
  let s = a + b            # fresh node, held by the wrapper (the builder keeps one more)
  # the planted over-release: two raw releases on top of the wrapper's own take
  # the count to zero, so libz3 frees the node while `s` is still live
  Z3_dec_ref(ctx.raw, s.raw)
  Z3_dec_ref(ctx.raw, s.raw)
  echo $Z3_ast_to_string(ctx.raw, s.raw)   # use after free inside libz3
main()
