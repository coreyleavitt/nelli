/* Standalone driver: parse an SMT-LIB 2 fixedpoint problem (declare-rel /
   declare-var / rule / query) and run Z3_fixedpoint_query on it.
   Build: gcc -g -o fpdrv fpdrv.c -lz3 */
#include <stdio.h>
#include <stdlib.h>
#include <z3.h>

static void on_err(Z3_context c, Z3_error_code e) {
  fprintf(stderr, "z3 error %d: %s\n", (int)e, Z3_get_error_msg(c, e));
  exit(2);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: fpdrv file.smt2 [engine]\n"); return 2; }
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx = Z3_mk_context(cfg);
  Z3_del_config(cfg);
  Z3_set_error_handler(ctx, on_err);
  Z3_fixedpoint fp = Z3_mk_fixedpoint(ctx);
  Z3_fixedpoint_inc_ref(ctx, fp);
  Z3_params p = Z3_mk_params(ctx);
  Z3_params_inc_ref(ctx, p);
  Z3_params_set_symbol(ctx, p, Z3_mk_string_symbol(ctx, "engine"),
                       Z3_mk_string_symbol(ctx, argc > 2 ? argv[2] : "spacer"));
  Z3_fixedpoint_set_params(ctx, fp, p);
  Z3_ast_vector qs = Z3_fixedpoint_from_file(ctx, fp, argv[1]);
  Z3_ast_vector_inc_ref(ctx, qs);
  unsigned n = Z3_ast_vector_size(ctx, qs);
  for (unsigned i = 0; i < n; i++) {
    Z3_lbool r = Z3_fixedpoint_query(ctx, fp, Z3_ast_vector_get(ctx, qs, i));
    printf("query %u: %s\n", i, r == Z3_L_TRUE ? "sat" : r == Z3_L_FALSE ? "unsat" : "unknown");
  }
  Z3_ast_vector_dec_ref(ctx, qs);
  Z3_params_dec_ref(ctx, p);
  Z3_fixedpoint_dec_ref(ctx, fp);
  Z3_del_context(ctx);
  return 0;
}
