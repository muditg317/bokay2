#ifndef PARSER_H_
#define PARSER_H_

#include <string.h>

#include "lexer.h"
#include "tools.h"
#include "type_parser.h"

typedef enum {
  EK_Error,
  EK_Empty, // For typedefs
  // expressions
  EK_Block,
  EK_If,
  EK_While,
  EK_Assignment,
  EK_Ternary,
  EK_BinOp,
  EK_FuncCall,
  EK_Index,
  EK_UnaryOp,
  // EK_Deref, (unary)
  // EK_Addr, (unary)
  EK_Variable,
  EK_Literal,
  // statements
  EK_Definition,
  EK_Return,
  // EK_TypeDef,

  EK_COUNT
} ExprKind;

const char *expr_kind_to_str(ExprKind ek);

typedef struct Expr Expr;
typedef struct Exprs {
  DA_FIELDS(Expr);
} Exprs;

typedef struct ExprBlock {
  Variables expectedInScope;
  Exprs exprs;
} ExprBlock;
typedef struct ExprIf {
  Expr *cond;
  Expr *then;
  Expr *else_;
} ExprIf;
typedef struct ExprWhile {
  Expr *cond;
  Expr *loop;
} ExprWhile;

typedef struct ExprAssignment {
  Expr *lhs;
  TokenKind op;
  Expr *rhs;
} ExprAssignment;
typedef struct ExprTernary {
  Expr *cond;
  Expr *iftrue;
  Expr *iffalse;
} ExprTernary;
typedef struct ExprBinOp {

} ExprBinOp;

typedef struct ExprFuncCall {
  Expr *func;
  Exprs params;
} ExprFuncCall;
typedef struct ExprIndex {
  Expr *ptr;
  Exprs indices;
} ExprIndex;
typedef struct ExprUnaryOp {
  TokenKind op;
  Expr *arg;
} ExprUnaryOp;
// typedef struct ExprDeref {

// } ExprDeref;
// typedef struct ExprAddr {

// } ExprAddr;
typedef struct ExprVariable {
  StringView name;
} ExprVariable;
typedef struct ExprLiteral {
  TokenLiteralKind kind;
  LiteralValue value;
} ExprLiteral;

typedef struct ExprDefinition {
  Variable var;
  Expr *rhs;
} ExprDefinition;
typedef struct ExprReturn {
  Expr *value;
} ExprReturn;
// typedef struct ExprTypeDef {
//   TypeRef type;
// } ExprTypeDef;

// The `Type` of an `Expr`.
typedef struct Type {
  TypeRef base;
  bool lvalue;
} Type;

// All `Expr`s must live on heap!
struct Expr {
  ExprKind kind;
  LexLoc loc;
  StringView text;
  Type type;

  union {
    ExprBlock block;
    ExprIf if_;
    ExprWhile while_;
    ExprAssignment assignment;
    ExprTernary ternary;
    ExprBinOp binop;
    ExprIndex index;
    ExprFuncCall funcall;
    ExprUnaryOp unaryop;
    // ExprDeref deref;
    // ExprAddr addr;
    ExprVariable variable;
    ExprLiteral literal;

    ExprDefinition definition;
    ExprReturn return_;
    // ExprTypeDef typedef_;
  } as;
};

void expr_reset(Expr *e);
void expr_reset_as(Expr *e);
Expr *expr_copy(Expr *e);

bool expr_is_typed(Expr *e);
void expr_remove_type(Expr *e);

typedef struct Program {
  TypeDefs types;
  // struct {
  //   DA_FIELDS(Function)
  // } funcs;
  struct {
    DA_FIELDS(Expr);
  } exprs;
} Program;

typedef struct ParserOpts {
  TypeDef *type_defs;
  size_t type_defs_count;
  bool mutable_by_default;
} ParserOpts;
typedef struct Parser {
  ParserOpts opts;
  Lexer *l;

  TypeDefs type_defs;

  SERROR_FIELDS;
} Parser;

typedef struct ParserState {
  LexerState lexer;
  size_t error_size;
} ParserState;

Parser parser_new_opt(Lexer *l, ParserOpts opts);
#define parser_new(l, ...) parser_new_opt(l, ((ParserOpts){__VA_ARGS__}))

bool parser_get_program(Parser *p, Program *prog);

bool parser_compile_top_level_expr(Parser *p, Expr *e);
bool parser_get_expression(Parser *p, Expr *e);

void parser_log_errors(Parser *p);
ParserState parser_save(Parser *p);
void parser_restore(Parser *p, ParserState state);

void parser_diag_remaining_exprs(Parser *p);
#define parser_diag_expr(level, p, e) log(level, LOC_Fmt ": [%s] ", LOC_Arg((e).loc), expr_kind_to_str((e).kind))

#endif // PARSER_H_

#ifdef PARSER_IMPL

// Bokay internal definitions
#define parser__fwd_lex_errorf(p, fmt, ...)                                                                            \
  serror_forwardf((p), (p)->l, "\n\t^ Due to lexer error: ", fmt __VA_OPT__(, ) __VA_ARGS__)

bool parser_compile_typedef(Parser *p, LexLoc typedef_loc, TypeRef *type);
bool parser_compile_expr_or_statement(Parser *p, Expr *expr);
typedef struct CompileExprOpts {
  // bool allow_statements; // untyped expressions
} CompileExprOpts;
bool parser_compile_expr_opt(Parser *p, Expr *expr, CompileExprOpts opts);
#define parser_compile_expr(p, expr, ...) parser_compile_expr_opt((p), (expr), (CompileExprOpts){__VA_ARGS__})
bool parser_compile_block(Parser *p, Expr *expr);
bool parser_compile_if(Parser *p, Expr *expr);
bool parser_compile_while(Parser *p, Expr *expr);
bool parser_compile_return(Parser *p, Expr *expr);
bool parser_compile_variable(Parser *p, Token ident, Variable *var);
bool parser_compile_assignment(Parser *p, Expr *expr);
bool parser_compile_ternary(Parser *p, LexLoc tern_loc, Expr cond, Expr *expr);
bool parser_compile_binop(Parser *p, size_t precedence, Expr *expr);
bool parser_compile_postfix_expr(Parser *p, Expr *expr);
bool parser_compile_funcall(Parser *p, Expr func, Expr *expr);
bool parser_compile_index(Parser *p, Expr ptr, Expr *expr);
bool parser_compile_primary_expr(Parser *p, Expr *expr);

// __VA_ARGS__ is optional "on_empty" expression
#define parser_compile_until(p, opt_delim, until, on_geterror, get_next, on_entry, ...)                                \
  do {                                                                                                                 \
    LexerState UNIQUE_VAR(s) = lexer_save(p->l);                                                                       \
    Token UNIQUE_VAR(t) = {0};                                                                                         \
    if (!lexer_expect_token(p->l, &UNIQUE_VAR(t))) (on_geterror);                                                      \
                                                                                                                       \
    if (token_is(UNIQUE_VAR(t), (until))) {                                                                            \
      logx(DEBUG, (.debug_label = "compile_list"), "thing is empty at " LOC_Fmt, LOC_Arg(UNIQUE_VAR(t).loc));          \
      TOOLS_MAYBE_DEFAULT(({ break; }), __VA_ARGS__);                                                                  \
    } else lexer_restore(p->l, UNIQUE_VAR(s));                                                                         \
                                                                                                                       \
    logx(DEBUG, (.debug_label = "compile_list"), "check list");                                                        \
    bool UNIQUE_VAR(done) = false;                                                                                     \
    while (!UNIQUE_VAR(done) && (get_next)) {                                                                          \
      (on_entry);                                                                                                      \
      if ((opt_delim)) { /* delim -> must have `delim` or `until` after each entry */                                  \
        if (!lexer_get_and_expect_from_array(p->l, &UNIQUE_VAR(t),                                                     \
                                             ((TokenKind[2]){*(TokenKind *)(opt_delim), (until)})))                    \
          (on_geterror);                                                                                               \
        if (token_is(UNIQUE_VAR(t), (until))) break;                                                                   \
        else continue;                                                                                                 \
      } else { /* no delim -> either see `until` or try next entry*/                                                   \
        lexer_maybe_consume_tok(p->l, (until), (UNIQUE_VAR(done) = true), (on_geterror));                              \
      }                                                                                                                \
    }                                                                                                                  \
  } while (0)

#define TYPE_PARSER_IMPL
#include "type_parser.h"

static_assert(EK_COUNT == 15, "ExprKind changed count");
const char *expr_kind_to_str(ExprKind ek) {
  switch (ek) {
  case EK_Error: return "EK_Error";
  case EK_Empty: return "EK_Empty";
  case EK_Block: return "EK_Block";
  case EK_If: return "EK_If";
  case EK_While: return "EK_While";
  case EK_Assignment: return "EK_Assignment";
  case EK_Ternary: return "EK_Ternary";
  case EK_BinOp: return "EK_BinOp";
  case EK_FuncCall: return "EK_FuncCall";
  case EK_Index: return "EK_Index";
  case EK_UnaryOp: return "EK_UnaryOp";
  // case EK_Deref: return "EK_Deref";
  // case EK_Addr: return "EK_Addr";
  case EK_Variable: return "EK_Variable";
  case EK_Literal: return "EK_Literal";
  case EK_Definition: return "EK_Definition";
  case EK_Return: return "EK_Return";
  // case EK_TypeDef: return "EK_TypeDef";
  default: UNREACHABLE("ExprKind. Got %d", ek);
  }
}

void expr_reset(Expr *e) { memset(e, 0, sizeof(*e)); }
void expr_reset_as(Expr *e) { memset(&e->as, 0, sizeof(e->as)); }
Expr *expr_copy(Expr *e) { return memdup(e); }

const Type UNTYPED = (Type){.base = BAD_TYPE_REF, .lvalue = false};
bool expr_is_typed(Expr *e) {
  return memcmp(&e->type, &UNTYPED, sizeof(e->type)) != 0;
  // bool result = memcmp(&e->type, &UNTYPED, sizeof(e->type)) != 0;
  // log(INFO, "check typed: %p = (%zu, %s) -- %s", e, e->type.base, e->type.lvalue ? "lval" : "rval",
  //     result ? "typed" : "untyped");
  // log(INFO, "untyped ref = (%zu, %s)", UNTYPED.base, UNTYPED.lvalue ? "lval" : "rval");
  // return result;
}
void expr_remove_type(Expr *e) { memcpy(&e->type, &UNTYPED, sizeof(e->type)); }

Parser parser_new_opt(Lexer *l, ParserOpts opts) {
  Parser p = {.opts = opts, .l = l};
  // da_push(&p.type_defs, ((TypeDef){.kind = Type_COUNT, .name = "ERROR"}));
  da_push_n(&p.type_defs, DEFAULT_TYPES, ARRAY_LEN(DEFAULT_TYPES));
  if (opts.type_defs) da_push_n(&p.type_defs, opts.type_defs, opts.type_defs_count);
  return p;
}

bool parser_get_program(Parser *p, Program *prog) {
  Expr e = {0};
  while ((expr_reset(&e), parser_compile_top_level_expr(p, &e))) {
    if (e.kind != EK_Error) da_push(&prog->exprs, e);
    expr_reset(&e);
  }
  prog->types = p->type_defs;

  if (serror_exists(p)) {
    parser_log_errors(p);
    serror_clear(p);
  }
  return e.kind == EK_Error || serror_exists(p);
}

bool parser_compile_top_level_expr(Parser *p, Expr *e) {
  expr_reset(e);

  Token start_tok = {0};
  LexerState s = lexer_save(p->l);

  if (!lexer_get_token(p->l, &start_tok)) goto finish_expr;
  e->loc = start_tok.loc;
  if (token_is(start_tok, TK_EOF)) goto finish_expr;

  if (token_is(start_tok, TK_Keyword_Type)) {
    e->kind = EK_Empty;
    TypeRef new_type = {0};
    parser_compile_typedef(p, start_tok.loc, &new_type);
    goto finish_expr;
  }
  lexer_restore(p->l, s); // unconsume non-`type` token

  if (!parser_compile_expr_or_statement(p, e)) goto finish_expr;

finish_expr:
  if (serror_exists(p->l)) parser__fwd_lex_errorf(p, "Failed to parse top level expr.");
  e->text = sv_new(start_tok.text.data, p->l->source.data - start_tok.text.data);
  bool result = e->kind != EK_Error && p->error.size <= s.error_size;
  logx(DEBUG, (.debug_label = "expr"), "finish top lexel expr: " SV_Fmt ". success=%s", SV_Arg(e->text),
       result ? "true" : "false");
  return result;
}

bool parser_compile_typedef(Parser *p, LexLoc typedef_loc, TypeRef *type) {
  Token tok = {0};
  if (!lexer_get_and_expect(p->l, &tok, TK_Ident)) goto bad_typedef;
  StringView alias = tok.text;
  if (!lexer_get_and_expect(p->l, &tok, TK_CHAR('='))) goto bad_typedef;
  if (!parser_compile_type(p, type)) {
    serror_locf(p, p->l->loc, "Expected type defintion for typedef of " SV_Fmt " at " LOC_Fmt ".", SV_Arg(alias),
                LOC_Arg(typedef_loc));
  }
  TypeDef *type_def = span_ptr(&p->type_defs, *type);
  type_diagx(&p->type_defs, type_def, DEBUG, (.debug_label = "typedef"), "got alias for type " SV_Fmt " -> " SB_Fmt,
             SV_Arg(alias));
  da_push(&type_def->aliases, alias);

  // consume optional semicolon
  lexer_maybe_consume_tok(p->l, TK_CHAR(';'), ({}), );
  return true;

bad_typedef:
  parser__fwd_lex_errorf(p, "Malformed typedef at " LOC_Fmt ".", LOC_Arg(typedef_loc));
  return false;
}

bool parser_compile_expr_or_statement(Parser *p, Expr *expr) {
  bool result = false;
  Token start_tok = {0};
  lexer_maybe_consume_tok_full(p->l, s, t, toks_as_array(1, TK_Keyword_Return), 1, ({
                                 start_tok = t;
                                 return_defer(parser_compile_return(p, expr));
                               }), );
  lexer_maybe_consume_tok_full(
      p->l, s, t, toks_as_array(1, TK_Ident), 1, ({
        start_tok = t;
        ParserState ps = parser_save(p);
        if (!parser_compile_variable(p, t, &expr->as.definition.var)) { // captures `: <type>`.
          parser_restore(p, ps);
          lexer_restore(p->l, s);
        } else {
          expr->kind = EK_Definition;
          expr_remove_type(expr);
          lexer_maybe_consume_tok(
              p->l, TK_CHAR('='), ({
                Expr rhs = {0};
                if (!parser_compile_expr(p, &rhs)) {
                  return_defer(
                      serror_causedf(p, "Couldn't compile initialization expression expected after `=` at " LOC_Fmt ".",
                                     LOC_Arg(t.loc)));
                }
                expr->as.definition.rhs = expr_copy(&rhs);
              }),
              ({ return_defer(false); }));
          return_defer(true);
        }
      }), );
  return_defer(parser_compile_expr(p, expr));
defer:
  if (!expr->text.data) { expr->text = sv_new(start_tok.text.data, p->l->source.data - start_tok.text.data); }
  if (result) { lexer_maybe_consume_tok(p->l, TK_CHAR(';'), (expr_remove_type(expr), expr->text.size++), ); }
  logx(DEBUG, (.debug_label = "expr"), "finished exprstmt parse: " SV_Fmt, SV_Arg(expr->text));
  return result;
}

bool parser_compile_expr_opt(Parser *p, Expr *expr, CompileExprOpts opts) {
  UNUSED(opts);
  expr_reset_as(expr);

  LexerState s = lexer_save(p->l);
  Token t = {0};
  if (!lexer_expect_token(p->l, &t)) return false;
  Token start_tok = t;
  expr->loc = t.loc;

  bool result = true;

  if (token_is(t, TK_CHAR('{'))) return_defer(parser_compile_block(p, expr));
  else if (token_is(t, TK_Keyword_If)) return_defer(parser_compile_if(p, expr));
  else if (token_is(t, TK_Keyword_While)) return_defer(parser_compile_while(p, expr));
  else if (token_is(t, TK_Keyword_Return)) return_defer(serror_locf(p, t.loc, "`return` only allowed as statement."));
  else if (token_is(t, TK_Keyword_Type)) return_defer(serror_locf(p, t.loc, "`type` only allowed at top level."));
  else if (token_is(t, TK_Ident)) { // maybe definition
    expr->type.base = EK_Definition;
    ParserState ps = parser_save(p);
    if (!parser_compile_variable(p, t, &expr->as.definition.var)) { // captures `: <type>`.
      parser_restore(p, ps);
      goto no_special_expr;
    }
    return_defer(
        serror_locf(p, t.loc, "Definition not allowed here! Only allowed in top level expressions/statements."));
  }
no_special_expr:
  lexer_restore(p->l, s);
  return_defer(parser_compile_assignment(p, expr));

defer:
  expr->text = sv_new(start_tok.text.data, p->l->source.data - start_tok.text.data);
  logx(DEBUG, (.debug_label = "expr"), "finished expr parse [%s]: " SV_Fmt "[%d]", expr_kind_to_str(expr->kind),
       SV_Arg(expr->text), expr->kind == EK_Block ? expr->as.block.exprs.size : -1);
  return result;
}

bool parser_compile_block(Parser *p, Expr *expr) {
  expr->kind = EK_Block;
  expr->type.lvalue = false;

  Expr curr_expr = {0};
  parser_compile_until(p, NULL, TK_CHAR('}'), ({ return false; }),
                       (curr_expr = ((Expr){0}), parser_compile_expr_or_statement(p, &curr_expr)),
                       ({ da_push(&expr->as.block.exprs, curr_expr); }));

  logx(DEBUG, (.debug_label = "expr_block"), "got %zu exprs", expr->as.block.exprs.size);

  return true;
}

bool parser_compile_if(Parser *p, Expr *expr) {
  expr->kind = EK_If;
  expr->type.lvalue = false;
  Expr cond = {0};
  Expr then = {0};
  Expr *else_ptr = NULL;
  if (!parser_compile_expr(p, &cond))
    return serror_causedf(p, "Failed to compile condition needed by `if` at " LOC_Fmt ".", LOC_Arg(expr->loc));
  if (!parser_compile_expr(p, &then))
    return serror_causedf(p, "Failed to compile {then block} needed by `if` at " LOC_Fmt ".", LOC_Arg(expr->loc));

  lexer_maybe_consume_tok(p->l, TK_Keyword_Else, ({
                            Expr else_ = {0};
                            if (!parser_compile_expr(p, &else_)) return false;
                            else_ptr = expr_copy(&else_);
                          }), );

  expr->as.if_.cond = expr_copy(&cond);
  expr->as.if_.then = expr_copy(&then);
  expr->as.if_.else_ = else_ptr;
  return true;
}

bool parser_compile_while(Parser *p, Expr *expr) {
  expr->kind = EK_While;
  expr->type.lvalue = false;
  Expr cond = {0};
  Expr loop = {0};
  if (!parser_compile_expr(p, &cond))
    return serror_causedf(p, "Failed to compile condition needed by `while` at " LOC_Fmt ".", LOC_Arg(expr->loc));
  if (!parser_compile_expr(p, &loop))
    return serror_causedf(p, "Failed to compile {loop block} needed by `while` at " LOC_Fmt ".", LOC_Arg(expr->loc));

  expr->as.while_.cond = expr_copy(&cond);
  expr->as.while_.loop = expr_copy(&loop);
  return true;
}

bool parser_compile_return(Parser *p, Expr *expr) {
  expr->kind = EK_Return;
  expr_remove_type(expr);
  Expr ret = {0};
  if (!parser_compile_expr(p, &ret))
    return serror_causedf(p, "Failed to compile return value needed by `return` at " LOC_Fmt ".", LOC_Arg(expr->loc));
  ;
  expr->as.return_.value = expr_copy(&ret);
  return true;
}

bool parser_compile_variable(Parser *p, Token ident, Variable *var) {
  var->name = ident.text;
  Token t = {0};
  if (!lexer_get_and_expect(p->l, &t, TK_CHAR(':'))) {
    return parser__fwd_lex_errorf(p, "Expected `:` after variable name.");
  }
  if (!parser_compile_type(p, &var->type)) {
    return serror_causedf(p, "Failed to compile type of variable defined at " LOC_Fmt ".", LOC_Arg(ident.loc));
  }
  return true;
}

bool parser_compile_assignment(Parser *p, Expr *expr) {
  if (!parser_compile_binop(p, 0, expr)) return false;
  lexer_maybe_consume_tok_full(
      p->l, s, t, TK_Punct_AnyAssign, ARRAY_LEN(TK_Punct_AnyAssign), ({
        if (!expr->type.lvalue) {
          return serror_locf(p, t.loc, "Cannot assign to non-rvalue at " LOC_Fmt ".", expr->loc);
        }
        Expr rhs = {0};
        if (!parser_compile_assignment(p, &rhs)) {
          return serror_causedf(p, "Failed to compile rhs of assignment at " LOC_Fmt ".", LOC_Arg(t.loc));
        }
        Expr *lhs = expr_copy(expr);
        expr->kind = EK_Assignment;
        sv_extend_to_endof(&expr->text, rhs.text);
        expr->as.assignment = (ExprAssignment){
            .lhs = lhs,
            .op = t.kind,
            .rhs = expr_copy(&rhs),
        };
        return true;
      }), );
  lexer_maybe_consume_tok_full(
      p->l, s, t, toks_as_array(1, TK_CHAR('?')), 1, ({
        return parser_compile_ternary(p, t.loc, *expr, expr) ||
               serror_causedf(p, "Couldn't comile ternary expression needed by `?` at " LOC_Fmt ".", LOC_Arg(t.loc));
      }), );
  return true;
}

bool parser_compile_ternary(Parser *p, LexLoc tern_loc, Expr cond, Expr *expr) {
  expr->kind = EK_Ternary;
  Expr iftrue = {0};
  if (!parser_compile_expr(p, &iftrue)) return serror_causedf(p, "Couldn't compile iftrue expression in ternary.");
  Token t = {0};
  if (!lexer_get_and_expect(p->l, &t, TK_CHAR(':')))
    return parser__fwd_lex_errorf(p, "Need matching : for `?` at " LOC_Fmt ".", LOC_Arg(tern_loc));
  Expr iffalse = {0};
  if (!parser_compile_expr(p, &iffalse)) return serror_causedf(p, "Couldn't compile iffalse expression in ternary.");

  expr->as.ternary =
      (ExprTernary){.cond = expr_copy(&cond), .iftrue = expr_copy(&iftrue), .iffalse = expr_copy(&iffalse)};
  sv_extend_to_endof(&expr->text, iffalse.text);
  return true;
}

bool parser_compile_binop(Parser *p, size_t precedence, Expr *expr) {
  if (precedence >= max_binop_precedence) return parser_compile_postfix_expr(p, expr);
  // lhs = parser_compile_binop(p, precedence + 1, expr); // capture all higher precedence binops
  // LexerState s = lexer_save(p->l);
  // get_token();
  // while (op = expect_binop(tok) && binop_precedence(op) == precedence) { // build chain at precedence
  //   rhs = parser_compile_binop(p, precedence + 1, expr);                 // capture higher
  //   precendence within chain lhs = binop(lhs, op, rhs);
  //   s = lexer_save(p->l);
  //   get_token();
  // }
  // lexer_restore(p->l, s);
  // return lhs;
  return serrorf(p, "TODO");
}

bool parser_compile_postfix_expr(Parser *p, Expr *expr) {
  // funcall(), index[]
  if (!parser_compile_primary_expr(p, expr)) return false;
  LexerState s = lexer_save(p->l);
  Token t = {0};
  if (!lexer_get_token(p->l, &t))
    return parser__fwd_lex_errorf(p, "Failed to compile postfix expr (funcall()/index[]).");
  while (token_is_oneof_array(t, toks_as_array(2, TK_CHAR('('), TK_CHAR('[')))) {
    if (token_is(t, TK_CHAR('('))) {
      if (!parser_compile_funcall(p, *expr, expr))
        return serror_causedf(p, "Couldn't compile function call expected by `(` at " LOC_Fmt ".", LOC_Arg(t.loc));
    } else if (token_is(t, TK_CHAR('['))) {
      if (!parser_compile_index(p, *expr, expr))
        return serror_causedf(p, "Couldn't compile index expected by `[` at " LOC_Fmt ".", LOC_Arg(t.loc));
    }
    s = lexer_save(p->l);
    if (!lexer_get_token(p->l, &t))
      return parser__fwd_lex_errorf(p, "Failed to compile postfix expr (funcall()/index[]).");
  }
  lexer_restore(p->l, s);
  return true;
}

bool parser_compile_funcall(Parser *p, Expr func, Expr *expr) {
  expr->kind = EK_FuncCall;
  expr->as.funcall.func = expr_copy(&func);
  Expr param = {0};
  TokenKind delim = TK_CHAR(',');
  parser_compile_until(p, &delim, TK_CHAR(')'), ({ return false; }), (parser_compile_expr(p, &param)),
                       ({ da_push(&expr->as.funcall.params, param); }), );
  return true;
}
bool parser_compile_index(Parser *p, Expr ptr, Expr *expr) {
  expr->kind = EK_FuncCall;
  expr->as.index.ptr = expr_copy(&ptr);
  Expr index = {0};
  TokenKind delim = TK_CHAR(',');
  parser_compile_until(p, &delim, TK_CHAR(']'), ({ return false; }), (parser_compile_expr(p, &index)),
                       ({ da_push(&expr->as.index.indices, index); }), );
  return true;
}

// bool parser_compile_expr_list_until(Parser *p, delim, Expr *expr) {
//   Exprs exprs;

//   LexerState s = lexer_save(p->l);
//   get_token();
//   if (tok == delim) return exprs;
//   lexer_restore(p->l, s);

//   while (expr = parser_compile_expr(p, expr)) {
//     push(exprs, expr);
//     get_and_expect(',', delim);
//     if (',') continue;
//     else break;
//   }

//   return exprs;
// }

bool parser_compile_primary_expr(Parser *p, Expr *expr) {
  Token t = {0};
  if (!lexer_get_token(p->l, &t)) return false;
  if (token_is(t, TK_CHAR('('))) {
    LexLoc open_loc = t.loc;
    if (!parser_compile_expr(p, expr)) return false;
    expr->loc = t.loc;
    if (!lexer_get_and_expect(p->l, &t, TK_CHAR((char)41))) { // ascii 41 == ')'
      return parser__fwd_lex_errorf(p, "Needed by `(` at " LOC_Fmt ".", LOC_Arg(open_loc));
    }
    sv_extend_to_endof(&expr->text, t.text);
    return true;
  } else if (token_is_oneof_array(t, TK_Punct_AnyUnary)) { // -neg, *deref, &addr, !not
    expr->kind = EK_UnaryOp;
    Expr arg;
    if (!parser_compile_expr(p, &arg))
      return serror_causedf(p, "Couldn't compile arg for unary op `%c` at " LOC_Fmt ".", t.kind.kind, LOC_Arg(t.loc));
    expr->as.unaryop.op = t.kind;
    expr->as.unaryop.arg = expr_copy(&arg);
    sv_extend_to_endof(&expr->text, arg.text);
    return true;
  } else if (token_is_oneof_array(t, TK_Literal_Any)) {
    expr->kind = EK_Literal;
    expr->as.literal.kind = t.kind.as.literal;
    expr->as.literal.value = t.lit;
    return true;
  } else if (token_is(t, TK_Ident)) {
    expr->kind = EK_Variable;
    expr->as.variable.name = t.text;
    return true;
  }
  return serror_locf(p, t.loc, "Unexpected token: %s (" SV_Fmt ").", token_kind_to_str(t.kind), SV_Arg(t.text));
}

void parser_log_errors(Parser *p) {
  if (serror_exists(p)) { log(ERROR, "Parser errors:\n" SV_Fmt, SV_Arg(p->error)); }
}

ParserState parser_save(Parser *p) { return (ParserState){.lexer = lexer_save(p->l), .error_size = p->error.size}; }
void parser_restore(Parser *p, ParserState s) {
  lexer_restore(p->l, s.lexer);
  p->error.size = s.error_size;
}

void debug_expr(TypeDefs *dict, Expr *e, size_t level) {
  StringBuilder sb = {0};
  if (expr_is_typed(e)) typedef_to_str(dict, span_ptr(dict, e->type.base), &sb);
  printf("[" LOC_Fmt "]\t%zu:%*s[%-15.*s %s]%s: ", LOC_Arg(e->loc), level, (int)level * 4, "", (int)sb.size, sb.data,
         e->type.lvalue ? "lval" : "rval", expr_kind_to_str(e->kind));
  switch (e->kind) {
  case EK_Empty: {
    printf("|" SV_Fmt "|\n", SV_Arg(e->text));
  } break;
  case EK_Block: {
    printf("%zu exprs:\n", e->as.block.exprs.size);
    span_for_each(Expr, be, e->as.block.exprs) { debug_expr(dict, be, level + 1); }
  } break;
  case EK_Definition: {
    sb_clear(&sb);
    typedef_to_str(dict, span_ptr(dict, e->as.definition.var.type), &sb);
    printf(SV_Fmt " [type=" SB_Fmt "]", SV_Arg(e->as.definition.var.name), SB_Arg(sb));
    if (e->as.definition.rhs) {
      printf(" = %s\n", expr_kind_to_str(e->as.definition.rhs->kind));
      debug_expr(dict, e->as.definition.rhs, level + 1);
    } else printf("\n");
  } break;
  default: break;
  }
}

void parser_diag_remaining_exprs(Parser *p) {
  Expr e = {0};
  while ((expr_reset(&e), parser_compile_top_level_expr(p, &e))) {
    // parser_diag_expr(INFO, p, e);
    debug_expr(&p->type_defs, &e, 0);
  }
  printf("\n");
}

#endif // PARSER_IMPL