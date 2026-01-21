#ifndef PROGRAM_H_
#define PROGRAM_H_

#include <stdint.h>

#include "lexer.h"
#include "parser.h"
#include "program_typecheck.h"
#include "tools.h"

typedef struct Scope {
  Variables in_scope;
} Scope;

typedef struct ScopeStack {
  DA_FIELDS(Scope);
} ScopeStack;

Variable *scope_stack_find(ScopeStack *scopes, StringView name);
Scope *scope_stack_add_new(ScopeStack *scopes);
bool scope_stack_pop(ScopeStack *scopes, Scope *to_pop);
Variable *scope_find(Scope *scope, StringView name);
void scope_add(Scope *scope, Variable var);

typedef struct Program {
  TypeDefs types;
  Exprs exprs;

  ScopeStack scope_stack;
  struct FuncSigStack {
    DA_FIELDS(FuncSignature);
  } function_definition_stack;

  SERROR_FIELDS;
} Program;

typedef struct ProgramNewOpts {
  const char *filepath;
  char *src;
  size_t src_len;
  StringView source_sv;
} ProgramNewOpts;
bool program_new_opt(Program *prog, ProgramNewOpts opts);
#define program_new(prog, ...) program_new_opt(prog, (ProgramNewOpts){__VA_ARGS__})

bool program_typecheck(Program *prog);

#endif // PROGRAM_H_

#ifdef PROGRAM_IMPL

// Bokay internal definitions

// =================== Implementation ===================

#define PROGRAM_TYPECHECK_IMPL
#include "program_typecheck.h"

void debug_scopes(ScopeStack *scopes) {
  span_for_each_reversed(Scope, scope, *scopes) {
    log(INFO, "===SCOPE %zu===", scope - scopes->data);
    span_for_each(Variable, var, scope->in_scope) { log(INFO, "var: " SV_Fmt, SV_Arg(var->name)); }
    log(INFO, "===END SCOPE %zu===", scope - scopes->data);
  }
}

Variable *scope_stack_find(ScopeStack *scopes, StringView name) {
  Variable *result = NULL;
  span_for_each_reversed(Scope, scope, *scopes) {
    result = scope_find(scope, name);
    if (result) return result;
  }
  // debug_scopes(scopes);
  return result;
}
Scope *scope_stack_add_new(ScopeStack *scopes) {
  da_push(scopes, (Scope){0});
  return &da_last(scopes);
}
bool scope_stack_pop(ScopeStack *scopes, Scope *to_pop) {
  if (&da_last(scopes) != to_pop) return false;
  span_chop_back(scopes, 1);
  return true;
}
Variable *scope_find(Scope *scope, StringView name) {
  span_for_each(Variable, var, scope->in_scope) {
    if (sv_eq(var->name, name)) return var;
  }
  return NULL;
}
void scope_add(Scope *scope, Variable var) {
  da_push(&scope->in_scope, var);
  // log(INFO, "add to scope: " SV_Fmt, SV_Arg(var.name));
}

bool program_new_opt(Program *prog, ProgramNewOpts opts) {
  memset(prog, 0, sizeof(*prog));
  if (opts.filepath) {
    StringBuilder sb = {0};
    if (!read_file(opts.filepath, &sb)) return false;
    opts.source_sv = sb2sv(sb);
  } else if (opts.src) {
    opts.source_sv = sv_new(opts.src, opts.src_len);
  }

  Lexer l = lexer_new(opts.source_sv, .filepath = opts.filepath);
  Parser p = parser_new(&l);

  // parser_diag_remaining_exprs(&p);

  Expr e = {0};
  while ((expr_reset(&e), parser_compile_top_level_expr(&p, &e))) {
    if (e.kind != EK_Error && e.kind != EK_Empty) da_push(&prog->exprs, e);
  }
  prog->types = p.type_defs;

  if (serror_exists(&p)) {
    parser_log_errors(&p);
    serror_clear(&p);
  }
  return e.kind == EK_Error || serror_exists(&p);
}

bool program_typecheck(Program *prog) {
  da_clear(&prog->scope_stack);
  da_push(&prog->scope_stack, (Scope){0});

  da_for_each(Expr, expr, prog->exprs) {
    if (!program_typecheck_expr(prog, expr)) {
      serror_causedf(prog, "Typecheck failed for expr at " LOC_Fmt ".", LOC_Arg(expr->loc));
      break;
    }
    debug_expr(&prog->types, expr, 0);
  }
  if (serror_exists(prog)) { log(ERROR, "Program typecheck errors:\n" SV_Fmt, SV_Arg(prog->error)); }

  return !serror_exists(prog);
}

#endif