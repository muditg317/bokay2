#ifndef PARSER_H_
#define PARSER_H_

#include "lexer.h"
#include "tools.h"

typedef enum TypeKind {
  Type_Void,
  Type_IntegerUnsigned,
  Type_IntegerSigned,
  Type_Float,
  Type_Ptr,
  Type_Array,
  Type_Struct,
  Type_Union,
  Type_Func,

  Type_COUNT
} TypeKind;

const char *type_kind_to_str(TypeKind tk);

typedef struct TypeDef TypeDef;
typedef struct Type {
  TypeDef *base;
  bool lvalue;
} Type;

typedef struct Variable {
  TypeDef *type;
  StringView name;
} Variable;

typedef struct Variables {
  DA_FIELDS(Variable)
} Variables;

typedef struct FuncSignature {
  TypeDef *ret;
  Variables params;
} FuncSignature;

struct TypeDef {
  TypeKind kind;
  size_t size;
  char *name;
  struct {
    DA_FIELDS(StringView)
  } aliases;

  bool mutable;

  TypeDef *ptr_to;
  struct {
    DA_FIELDS(TypeDef *)
  } fields;
  size_t array_length;

  FuncSignature signature;
};

// const TypeDef Type_void = {.kind = Type_Void, .size = 0, .name = "void"};
// const TypeDef Type_u8 = {.kind = Type_IntegerUnsigned, .size = 8, .name = "u8"};
// const TypeDef Type_u16 = {.kind = Type_IntegerUnsigned, .size = 16, .name = "u16"};
// const TypeDef Type_u32 = {.kind = Type_IntegerUnsigned, .size = 32, .name = "u32"};
// const TypeDef Type_u64 = {.kind = Type_IntegerUnsigned, .size = 64, .name = "u64"};
// const TypeDef Type_s8 = {.kind = Type_IntegerSigned, .size = 8, .name = "s8"};
// const TypeDef Type_s16 = {.kind = Type_IntegerSigned, .size = 16, .name = "s16"};
// const TypeDef Type_s32 = {.kind = Type_IntegerSigned, .size = 32, .name = "s32"};
// const TypeDef Type_s64 = {.kind = Type_IntegerSigned, .size = 64, .name = "s64"};
// const TypeDef Type_f32 = {.kind = Type_Float, .size = 32, .name = "f32"};
// const TypeDef Type_f64 = {.kind = Type_Float, .size = 64, .name = "f64"};
const TypeDef DEFAULT_TYPES[11] = {
    //     Type_void, Type_u8, Type_u16, Type_u32, Type_u64, Type_s8, Type_s16, Type_s32, Type_s64, Type_f32, Type_f64
    // };
    (TypeDef){.kind = Type_Void, .size = 0, .name = "void"},
    (TypeDef){.kind = Type_IntegerUnsigned, .size = 8, .name = "u8"},
    (TypeDef){.kind = Type_IntegerUnsigned, .size = 16, .name = "u16"},
    (TypeDef){.kind = Type_IntegerUnsigned, .size = 32, .name = "u32"},
    (TypeDef){.kind = Type_IntegerUnsigned, .size = 64, .name = "u64"},
    (TypeDef){.kind = Type_IntegerSigned, .size = 8, .name = "s8"},
    (TypeDef){.kind = Type_IntegerSigned, .size = 16, .name = "s16"},
    (TypeDef){.kind = Type_IntegerSigned, .size = 32, .name = "s32"},
    (TypeDef){.kind = Type_IntegerSigned, .size = 64, .name = "s64"},
    (TypeDef){.kind = Type_Float, .size = 32, .name = "f32"},
    (TypeDef){.kind = Type_Float, .size = 64, .name = "f64"},
};

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
  TypeDef *type;
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
  Expr lhs;
  TokenKind assignment_op; // TODO: refactor TokenKind enums
  Expr rhs;
} ExprAssignment;
typedef struct ExprDefinition {
  Variable var;
  bool has_rhs; // default to 0-init when no rhs
  Expr rhs;
} ExprDefinition;
typedef struct ExprFuncCall {

} ExprFuncCall;
// typedef struct ExprTypeDef {
//   TypeDef *type;
// } ExprTypeDef;
typedef struct ExprBlock {
  Variables expectedInScope;
} ExprBlock;

struct Expr {
  ExprKind kind;
  LexLoc loc;
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
  struct {
    DA_FIELDS(TypeDef)
  } types;
  // struct {
  //   DA_FIELDS(Function)
  // } funcs;
  struct {
    DA_FIELDS(Expr)
  } exprs;
} Program;

void expr_reset(Expr *e);

typedef struct ParserOpts {
  TypeDef *type_defs;
  size_t type_defs_count;
} ParserOpts;
typedef struct Parser {
  ParserOpts opts;
  Lexer *l;

  struct {
    DA_FIELDS(TypeDef)
  } type_defs;

  StringBuilder error;
} Parser;

Parser parser_new_opt(Lexer *l, ParserOpts opts);
#define parser_new(l, ...) parser_new_opt(l, ((ParserOpts){__VA_ARGS__}))

bool parser_get_program(Parser *p, Program *prog);

bool parser_compile_top_level_expr(Parser *p, Expr *e);

bool parser_get_expression(Parser *p, Expr *e);

void parser_log_errors(Parser *p);

void parser_diag_remaining_exprs(Parser *p);
#define parser_diag_expr(level, p, e)                                                                                  \
  log(level, LEX_LOC_Fmt ": [%s] ", LEX_LOC_Arg((e).loc), expr_kind_to_str((e).kind))

// internal defintions
TypeDef *parser__find_type(Parser *p);

#define parser__fwd_lex_errorf(p, fmt, ...)                                                                            \
  lexer_errorf((p), SB_Fmt fmt, SB_Arg((p)->l->error) __VA_OPT__(, ) __VA_ARGS__)

#endif // PARSER_H_

#ifdef PARSER_IMPLEMENTATION

static_assert(Type_COUNT == 9, "TypeKind changed count");
const char *type_kind_to_str(TypeKind tk) {
  switch (tk) {
  case Type_Void: return "Type_Void";
  case Type_IntegerUnsigned: return "Type_IntegerUnsigned";
  case Type_IntegerSigned: return "Type_IntegerSigned";
  case Type_Float: return "Type_Float";
  case Type_Ptr: return "Type_Ptr";
  case Type_Array: return "Type_Array";
  case Type_Struct: return "Type_Struct";
  case Type_Union: return "Type_Union";
  case Type_Func: return "Type_Func";
  default: UNREACHABLE("TypeKind");
  }
}

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
  default: UNREACHABLE("ExprKind");
  }
}

void expr_reset(Expr *e) { memset(e, 0, sizeof(*e)); }

Parser parser_new_opt(Lexer *l, ParserOpts opts) {
  Parser p = {.opts = opts, .l = l};
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
  if (lexer_has_error(p)) { log(ERROR, SB_Fmt, SB_Arg(p->error)); }
  return e->kind == EK_Error || lexer_has_error(p);
}

compile_type() {
  // TODO
}

compile_expr_or_statement() {
  expr = compile_expr();
  s = save();
  get_token();
  if (';') expr.type = void_;
  else restore(s);
  return expr;
}

compile_expr() {
  s = save();
  get_token();
  if ('{') return compile_block();
  else if (TK_Kw_If) return compile_if();
  else if (TK_Kw_While) return compile_while();
  else if (TK_Kw_Return) return compile_return();
  else if (TK_Ident) { // maybe
                       // definition
    get_expect(':');
    type = compile_type();
    s2 = save();
    get_token();
    if ('=') init_val = compile_expr();
    else restore(s2);
    return definition(type, init_val);
  }
  restore(s);
  return compile_assignment();
}

compile_block() {
  get_token();
  while (!'}') {
    append(compile_expr());
    get_token();
  }
}

compile_if() {
  cond = compile_expr();
  then = compile_expr();
  s = save();
  get_token();
  if (TK_Kw_Else) else_ = compile_expr;
  else restore(s);
}

compile_while() {
  cond = compile_expr();
  loop = compile_expr();
  return while_(cond, loop);
}

compile_return() { return compile_expr(); }

compile_assignment() {
  lhs = compile_binop(0);
  get_token();
  if (expect_oneof('=' || "XX=")) {
    op = tok;
    rhs = compile_assignment();
    // maybe a while loop idk
    return assignment(lhs, op, rhs);
  } else if ('?') {
    return compile_ternary(lhs);
  }
  return lhs;
}

compile_ternary(cond) {
  iftrue = compile_expr();
  get_and_expect(':');
  iffalse = compile_expr();
  return ternary(cond, iftrue, iffalse);
}

compile_binop(precedence) {
  if (precedence >= max_binop_precedence) return compile_postfix_expr();
  lhs = compile_binop(precedence + 1); // capture all higher precedence binops
  s = save();
  get_token();
  while (op = expect_binop(tok) && binop_precedence(op) == precedence) { // build chain at precedence
    rhs = compile_binop(precedence + 1);                                 // capture higher precendence within chain
    lhs = binop(lhs, op, rhs);
    s = save();
    get_token();
  }
  restore(s);
  return lhs;
}

compile_postfix_expr() {
  // funcall(), index[]
  expr = compile_primary_expr();
  s = save();
  get_token();
  while (expect_oneof('(', '[')) {
    if ('(') expr = compile_funcall(expr);
    else if ('[') expr = compile_index(expr);
    s = save();
    get_token();
  }
  restore(s);
  return expr;
}

compile_funcall(func) { return funcall(func, compile_expr_list_until(')');
}
compile_index(ptr) { return index(ptr, compile_expr_list_until(']')); }

compile_expr_list_until(delim) {
  Exprs exprs;

  s = save();
  get_token();
  if (tok == delim) return exprs;
  restore(s);

  while (expr = compile_expr()) {
    push(exprs, expr);
    get_and_expect(',', delim);
    if (',') continue;
    else break;
  }

  return exprs;
}

compile_primary_expr() {
  get_token();
  if ('(') {
    expr = compile_expr();
    get_and_expect(')');
    return expr;
  } else if (op = expect_unary(tok)) { // -neg, *deref, &addr, !not
    expr = compile_expr();
    return unary(op, expr);
  } else if (is_literal(tok)) {
    return literal(tok);
  } else if (TK_Ident) {
    return variable(tok);
  }
}

bool parser_compile_top_level_expr(Parser *p, Expr *e) {
  size_t error_start = p->error.size;

  Token tok = {0};
  LexerState s = lexer_save(p->l);

  if (!lexer_get_token(p->l, &tok)) goto finish_expr;
  e->loc = tok.loc;

  if (tok.kind == TK_Kw_Type) {
    e->kind = EK_Empty;
    // e->type = parser__find_type(p, "void");
    TypeDef type = {0};
    if (!lexer_get_and_expect(p->l, &tok, TK_Ident)) goto bad_typedef;
    da_push(&type.aliases, tok.text);
    if (!lexer_get_and_expect(p->l, &tok, '=')) goto bad_typedef;
    if (!parser_compile_type(p, &type)) {
      lexer__report_error_at_loc(p, p->l->loc, "Expected type defintion for typedef of " SV_Fmt " at " LEX_LOC_Fmt ".",
                                 SV_Arg(span_at(type.aliases, 0)), LEX_LOC_Arg(e->loc));
    }
    // e->as.typedef_.type = type;
    goto finish_typedef;
  bad_typedef:
    parser__fwd_lex_errorf(p, "\t^ Needed by typedef started at " LEX_LOC_Fmt ".", LEX_LOC_Arg(e->loc));
  finish_typedef:
    goto finish_expr;
  }

  *e = compile_expr();

finish_expr:
  return e->kind != EK_Error && p->error.size <= error_start;
  // if (e->kind == EK_Error || p->error.size > error_start) {
  //   lexer_restore(p->l, s);
  //   return false;
  // }
  // return true;
}

void parser_log_errors(Parser *p) {
  if (lexer_has_error(p)) { log(ERROR, "Parser errors:\n" SV_Fmt, SV_Arg(p->error)); }
}

void parser_diag_remaining_exprs(Parser *p) {
  Expr e;
  StringBuilder sb = {0};
  while (parser_get_expression(p, &e)) {
    parser_diag_expr(INFO, p, e);
    if (e.kind == EK_Printf) {
      sb_clear(&sb);
      sb_appendf(&sb, "\tfmt=" SV_Fmt, SV_Arg(e.as.printf.fmt_text));
      if (e.as.printf.size) sb_append_cstr(&sb, ", args=[");
      da_for_each(Token, arg, e.as.printf) {
        if (arg != e.as.printf.data) sb_append_cstr(&sb, ", ");

        switch (arg->kind) {
        case TK_Literal_Integer: sb_appendf(&sb, "%d", arg->lit_int); break;
        case TK_Literal_Float: sb_appendf(&sb, "%f", arg->lit_float); break;
        case TK_Literal_Char: sb_appendf(&sb, "\'%c\'", arg->lit_char); break;
        case TK_Literal_StringSQ: // fallthrough
        case TK_Literal_StringDQ: sb_appendf(&sb, SB_Fmt, SB_Arg(arg->lit_string)); break;
        default: UNREACHABLE("TokenKind expected literal only");
        }
      }
      if (e.as.printf.size) sb_append_cstr(&sb, "]");
      log(INFO, "\t " SB_Fmt, SB_Arg(sb));
    }
  }
}

TypeDef *parser__find_type(Parser *p) {
  da_for_each(TypeDef *, type, p->type_defs) { if (strcmp) }
}

#endif // PARSER_IMPLEMENTATION