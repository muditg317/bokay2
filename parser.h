#ifndef PARSER_H_
#define PARSER_H_

#include "lexer.h"
#include "tools.h"
#include "type_parser.h"

typedef enum {
  EK_Error,
  EK_Empty,
  EK_Literal,
  EK_UnaryOp,
  EK_BinOp,
  EK_Index,
  EK_Deref,
  EK_Addr,
  EK_Assignment,
  EK_Definition,
  EK_FuncCall,
  // EK_TypeDef,
  EK_Block,

  EK_COUNT
} ExprKind;

const char *expr_kind_to_str(ExprKind ek);

typedef struct Expr Expr;

typedef struct ExprLiteral {
  TypeRef *type;
  uint8_t value[8]; // all values will take 8 bytes
} ExprLiteral;

typedef struct ExprUnaryOp {
} ExprUnaryOp;

typedef struct ExprBinOp {

} ExprBinOp;
typedef struct ExprIndex {

} ExprIndex;
typedef struct ExprDeref {

} ExprDeref;
typedef struct ExprAddr {

} ExprAddr;
typedef struct ExprAssignment {
  Expr *lhs;
  TokenKind assignment_op;
  Expr *rhs;
} ExprAssignment;
typedef struct ExprDefinition {
  Variable var;
  Expr *rhs;
} ExprDefinition;
typedef struct ExprFuncCall {

} ExprFuncCall;
// typedef struct ExprTypeDef {
//   TypeRef type;
// } ExprTypeDef;
typedef struct ExprBlock {
  Variables expectedInScope;
} ExprBlock;

// The `Type` of an `Expr`.
typedef struct Type {
  TypeRef *base;
  bool lvalue;
} Type;

// All `Expr`s must live on heap!
struct Expr {
  ExprKind kind;
  LexLoc loc;
  StringView text;
  Type type;

  union {
    ExprLiteral literal;
    ExprUnaryOp unaryop;
    ExprBinOp binop;
    ExprIndex index;
    ExprDeref deref;
    ExprAddr addr;
    ExprAssignment assign;
    ExprDefinition definition;
    ExprFuncCall funcall;
    // ExprTypeDef typedef_;
    ExprBlock block;
  } as;
};

// typedef struct Function {
//   FuncSignature signature;
//   ExprBlock body;
// } Function;

typedef struct Program {
  TypeDefs types;
  // struct {
  //   DA_FIELDS(Function)
  // } funcs;
  struct {
    DA_FIELDS(Expr);
  } exprs;
} Program;

void expr_reset(Expr *e);

typedef struct ParserOpts {
  TypeDef *type_defs;
  size_t type_defs_count;
  bool mutable_by_default;
} ParserOpts;
typedef struct Parser {
  ParserOpts opts;
  Lexer *l;

  TypeDefs type_defs;

  StringBuilder error;
} Parser;

Parser parser_new_opt(Lexer *l, ParserOpts opts);
#define parser_new(l, ...) parser_new_opt(l, ((ParserOpts){__VA_ARGS__}))

bool parser_get_program(Parser *p, Program *prog);

bool parser_compile_top_level_expr(Parser *p, Expr *e);

bool parser_get_expression(Parser *p, Expr *e);

void parser_log_errors(Parser *p);

void parser_diag_remaining_exprs(Parser *p);
#define parser_diag_expr(level, p, e) log(level, LOC_Fmt ": [%s] ", LOC_Arg((e).loc), expr_kind_to_str((e).kind))

#endif // PARSER_H_

#ifdef PARSER_IMPL

// Bokay internal definitions
#define parser__fwd_lex_errorf(p, fmt, ...)                                                                            \
  serror_forwardf((p), (p)->l, "\n\t^ Due to lexer error: ", fmt __VA_OPT__(, ) __VA_ARGS__)

bool parser_compile_variable(Parser *p, Token ident, Variable *var);

#define TYPE_PARSER_IMPL
#include "type_parser.h"

static_assert(EK_COUNT == 12, "ExprKind changed count");
const char *expr_kind_to_str(ExprKind ek) {
  switch (ek) {
  case EK_Error: return "EK_Error";
  case EK_Empty: return "EK_Empty";
  case EK_Literal: return "EK_Literal";
  case EK_UnaryOp: return "EK_UnaryOp";
  case EK_BinOp: return "EK_BinOp";
  case EK_Index: return "EK_Index";
  case EK_Deref: return "EK_Deref";
  case EK_Addr: return "EK_Addr";
  case EK_Assignment: return "EK_Assignment";
  case EK_Definition: return "EK_Definition";
  case EK_FuncCall: return "EK_FuncCall";
  // case EK_TypeDef: return "EK_TypeDef";
  case EK_Block: return "EK_Block";
  default: UNREACHABLE("ExprKind. Got %d", ek);
  }
}

void expr_reset(Expr *e) { memset(e, 0, sizeof(*e)); }

Parser parser_new_opt(Lexer *l, ParserOpts opts) {
  Parser p = {.opts = opts, .l = l};
  // da_push(&p.type_defs, ((TypeDef){.kind = Type_COUNT, .name = "ERROR"}));
  da_push_n(&p.type_defs, DEFAULT_TYPES, ARRAY_LEN(DEFAULT_TYPES));
  if (opts.type_defs) da_push_n(&p.type_defs, opts.type_defs, opts.type_defs_count);
  return p;
}

bool parser_get_program(Parser *p, Program *prog) {
  Expr e;
  expr_reset(&e);
  while (parser_compile_top_level_expr(p, &e)) {
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

// bool parser_compile_expr_or_statement(Parser *p, Expr *expr) {
//   expr = compile_expr();
//   s = save();
//   get_token();
//   if (';') expr.type = void_;
//   else restore(s);
//   return expr;
// }

// bool parser_compile_expr(Parser *p, Expr *expr) {
//   s = save();
//   get_token();
//   if ('{') return compile_block();
//   else if (TK_Keyword_If) return compile_if();
//   else if (TK_Keyword_While) return compile_while();
//   else if (TK_Keyword_Return) return compile_return();
//   else if (TK_Ident) { // maybe definition
//     compile_variable(tok.text); // captures `: <type>`.
//     get_expect(':');
//     type = parser_compile_type();
//     s2 = save();
//     get_token();
//     if ('=') init_val = compile_expr();
//     else restore(s2);
//     return definition(type, init_val);
//   }
//   restore(s);
//   return compile_assignment();
// }

// bool parser_compile_block(Parser *p, Expr *expr) {
//   get_token();
//   while (!'}') {
//     append(compile_expr());
//     get_token();
//   }
// }

// bool parser_compile_if(Parser *p, Expr *expr) {
//   cond = compile_expr();
//   then = compile_expr();
//   s = save();
//   get_token();
//   if (TK_Keyword_Else) else_ = compile_expr;
//   else restore(s);
// }

// bool parser_compile_while(Parser *p, Expr *expr) {
//   cond = compile_expr();
//   loop = compile_expr();
//   return while_(cond, loop);
// }

// bool parser_compile_return(Parser *p, Expr *expr) { return compile_expr(); }

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

// bool parser_compile_assignment(Parser *p, Expr *expr) {
//   lhs = compile_binop(0);
//   get_token();
//   if (expect_oneof('=' || "XX=")) {
//     op = tok;
//     rhs = compile_assignment();
//     // maybe a while loop idk
//     return assignment(lhs, op, rhs);
//   } else if ('?') {
//     return compile_ternary(lhs);
//   }
//   return lhs;
// }

// bool parser_compile_ternary(Parser *p, cond, Expr *expr) {
//   iftrue = compile_expr();
//   get_and_expect(':');
//   iffalse = compile_expr();
//   return ternary(cond, iftrue, iffalse);
// }

// bool parser_compile_binop(Parser *p, precedence, Expr *expr) {
//   if (precedence >= max_binop_precedence) return compile_postfix_expr();
//   lhs = compile_binop(precedence + 1); // capture all higher precedence binops
//   s = save();
//   get_token();
//   while (op = expect_binop(tok) && binop_precedence(op) == precedence) { // build chain at precedence
//     rhs = compile_binop(precedence + 1);                                 // capture higher precendence within chain
//     lhs = binop(lhs, op, rhs);
//     s = save();
//     get_token();
//   }
//   restore(s);
//   return lhs;
// }

// bool parser_compile_postfix_expr(Parser *p, Expr *expr) {
//   // funcall(), index[]
//   expr = compile_primary_expr();
//   s = save();
//   get_token();
//   while (expect_oneof('(', '[')) {
//     if ('(') expr = compile_funcall(expr);
//     else if ('[') expr = compile_index(expr);
//     s = save();
//     get_token();
//   }
//   restore(s);
//   return expr;
// }

// bool parser_compile_funcall(Parser *p, func, Expr *expr) { return funcall(func, compile_expr_list_until(')');
// }
// bool parser_compile_index(Parser *p, ptr, Expr *expr) { return index(ptr, compile_expr_list_until(']')); }

// bool parser_compile_expr_list_until(Parser *p, delim, Expr *expr) {
//   Exprs exprs;

//   s = save();
//   get_token();
//   if (tok == delim) return exprs;
//   restore(s);

//   while (expr = compile_expr()) {
//     push(exprs, expr);
//     get_and_expect(',', delim);
//     if (',') continue;
//     else break;
//   }

//   return exprs;
// }

// bool parser_compile_primary_expr(Parser *p, Expr *expr) {
//   get_token();
//   if ('(') {
//     expr = compile_expr();
//     get_and_expect(')');
//     return expr;
//   } else if (op = expect_unary(tok)) { // -neg, *deref, &addr, !not
//     expr = compile_expr();
//     return unary(op, expr);
//   } else if (is_literal(tok)) {
//     return literal(tok);
//   } else if (TK_Ident) {
//     return variable(tok);
//   }
// }

bool parser_compile_top_level_expr(Parser *p, Expr *e) {
  expr_reset(e);

  size_t error_start = p->error.size;

  Token tok = {0};
  LexerState s = lexer_save(p->l);

  if (!lexer_get_token(p->l, &tok)) goto finish_expr;
  e->loc = tok.loc;
  if (token_is(tok, TK_EOF)) goto finish_expr;

  if (token_is(tok, TK_Keyword_Type)) {
    e->kind = EK_Empty;
    // e->type = parser__find_type(p, "void");
    // TypeDef type = {0};
    if (!lexer_get_and_expect(p->l, &tok, TK_Ident)) goto bad_typedef;
    StringView alias = tok.text;
    if (!lexer_get_and_expect(p->l, &tok, TK_CHAR('='))) goto bad_typedef;
    TypeRef type;
    if (!parser_compile_type(p, &type)) {
      serror_locf(p, p->l->loc, "Expected type defintion for typedef of " SV_Fmt " at " LOC_Fmt ".", SV_Arg(alias),
                  LOC_Arg(e->loc));
    }
    TypeDef *type_def = span_ptr(&p->type_defs, type);
    type_diagx(&p->type_defs, type_def, DEBUG, (.debug_label = "typedef"), "got alias for type " SV_Fmt " -> " SB_Fmt,
               SV_Arg(alias));
    da_push(&type_def->aliases, alias);
    // e->as.typedef_.type = type;
    goto finish_typedef;
  bad_typedef:
    parser__fwd_lex_errorf(p, "Malformed typedef at " LOC_Fmt ".", LOC_Arg(e->loc));
  finish_typedef:
    goto finish_expr;
  }
  lexer_restore(p->l, s); // unconsume non-`type` token

  // *e = compile_expr();
  // if (!parser_compile_expr(p, e)) goto finish_expr;

finish_expr:
  e->text = sv_new(s.source.data, p->l->source.data - s.source.data);
  return e->kind != EK_Error && p->error.size <= error_start;
  // if (e->kind == EK_Error || p->error.size > error_start) {
  //   lexer_restore(p->l, s);
  //   return false;
  // }
  // return true;
}

void parser_log_errors(Parser *p) {
  if (serror_exists(p)) { log(ERROR, "Parser errors:\n" SV_Fmt, SV_Arg(p->error)); }
}

void parser_diag_remaining_exprs(Parser *p) {
  Expr e;
  // StringBuilder sb = {0};
  while (parser_compile_top_level_expr(p, &e)) {
    parser_diag_expr(INFO, p, e);
    // if (e.kind == EK_Printf) {
    //   sb_clear(&sb);
    //   sb_appendf(&sb, "\tfmt=" SV_Fmt, SV_Arg(e.as.printf.fmt_text));
    //   if (e.as.printf.size) sb_append_cstr(&sb, ", args=[");
    //   da_for_each(Token, arg, e.as.printf) {
    //     if (arg != e.as.printf.data) sb_append_cstr(&sb, ", ");

    //     switch (arg->kind) {
    //     case TK_Literal_Integer: sb_appendf(&sb, "%d", arg->lit_int); break;
    //     case TK_Literal_Float: sb_appendf(&sb, "%f", arg->lit_float); break;
    //     case TK_Literal_Char: sb_appendf(&sb, "\'%c\'", arg->lit_char); break;
    //     case TK_Literal_StringSQ: // fallthrough
    //     case TK_Literal_StringDQ: sb_appendf(&sb, SB_Fmt, SB_Arg(arg->lit_string)); break;
    //     default: UNREACHABLE("TokenKind expected literal only");
    //     }
    //   }
    //   if (e.as.printf.size) sb_append_cstr(&sb, "]");
    //   log(INFO, "\t " SB_Fmt, SB_Arg(sb));
    // }
  }
}

#endif // PARSER_IMPL