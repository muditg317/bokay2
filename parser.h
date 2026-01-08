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

typedef struct Type Type;

typedef struct NamedParameter {
  Type *type;
  char *name;
} NamedParameter;
typedef struct FuncSignature {
  Type *ret;
  struct {
    DA_FIELDS(NamedParameter)
  } params;
} FuncSignature;

struct Type {
  TypeKind kind;
  size_t size;
  char *name;
  struct {
    DA_FIELDS(char *)
  } aliases;

  Type *ptr_to;
  struct {
    DA_FIELDS(Type *)
  } fields;
  size_t array_length;

  FuncSignature signature;
};

const Type DEFAULT_TYPES[10] = {
    (Type){.kind = Type_Void, .size = 0, .name = "void"},
    (Type){.kind = Type_IntegerUnsigned, .size = 8, .name = "u8"},
    (Type){.kind = Type_IntegerUnsigned, .size = 16, .name = "u16"},
    (Type){.kind = Type_IntegerUnsigned, .size = 32, .name = "u32"},
    (Type){.kind = Type_IntegerUnsigned, .size = 64, .name = "u64"},
    (Type){.kind = Type_IntegerSigned, .size = 8, .name = "s8"},
    (Type){.kind = Type_IntegerSigned, .size = 16, .name = "s16"},
    (Type){.kind = Type_IntegerSigned, .size = 32, .name = "s32"},
    (Type){.kind = Type_IntegerSigned, .size = 64, .name = "s64"},
    (Type){.kind = Type_Float, .size = 32, .name = "f32"},
    (Type){.kind = Type_Float, .size = 64, .name = "f64"},
};

typedef struct Variable {
  Type *type;
  char *name;
  bool l_value;
  void *data; // based on size from `type`
} Variable;

typedef struct Variables {
  DA_FIELDS(Variable);
} Variables;

typedef enum {
  Expr_Error,
  Expr_Literal,
  Expr_UnaryOp,
  Expr_BinOp,
  Expr_Index,
  Expr_Deref,
  Expr_Addr,
  Expr_Assignment,
  Expr_TypeName,
  Expr_FuncCall,
  Expr_Block,

  Expr_COUNT
} ExprKind;

const char *expr_kind_to_str(ExprKind ek);

typedef struct ExprLiteral {
  Type type;
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

} ExprAssignment;
typedef struct ExprTypeName {

} ExprTypeName;
typedef struct ExprFuncCall {

} ExprFuncCall;
typedef struct ExprBlock {
  Variables expectedInScope;
} ExprBlock;

typedef struct Expr {
  ExprKind kind;
  LexLoc loc;
  Type *type;

  union {
    ExprLiteral literal;
    ExprUnaryOp unaryop;
    ExprBinOp binop;
    ExprIndex index;
    ExprDeref deref;
    ExprAddr addr;
    ExprAssignment assign;
    ExprTypeName type_name;
    ExprFuncCall funcall;
    ExprBlock block;
  } as;

} Expr;

// typedef struct Function {
//   FuncSignature signature;
//   ExprBlock body;
// } Function;

typedef struct Program {
  // struct {
  //   DA_FIELDS(Type)
  // } types;
  // struct {
  //   DA_FIELDS(Function)
  // } funcs;
  struct {
    DA_FIELDS(Expr)
  } exprs;
} Program;

void expr_reset(Expr *e);

typedef struct ParserOpts {

} ParserOpts;
typedef struct Parser {
  ParserOpts opts;
  Lexer *l;

  StringBuilder error;
} Parser;

Parser parser_new_opt(Lexer *l, ParserOpts opts);
#define parser_new(l, ...) parser_new_opt(l, ((ParserOpts){__VA_ARGS__}))

bool parser_get_program(Parser *p, Program *prog);

bool parser_get_expression(Parser *p, Expr *e);

void parser_log_errors(Parser *p);

void parser_diag_remaining_exprs(Parser *p);
#define parser_diag_expr(level, p, e)                                                                                  \
  log(level, LEX_LOC_Fmt ": [%s] ", LEX_LOC_Arg((e).loc), expr_kind_to_str((e).kind))

#endif // PARSER_H_

#ifdef PARSER_IMPLEMENTATION

const char *type_kind_to_str(TypeKind tk) {
  switch (tk) {
  case Type_Void:
    return "Type_Void";
  case Type_IntegerUnsigned:
    return "Type_IntegerUnsigned";
  case Type_IntegerSigned:
    return "Type_IntegerSigned";
  case Type_Float:
    return "Type_Float";
  case Type_Ptr:
    return "Type_Ptr";
  case Type_Array:
    return "Type_Array";
  case Type_Struct:
    return "Type_Struct";
  case Type_Union:
    return "Type_Union";
  case Type_Func:
    return "Type_Func";
  default:
    UNREACHABLE("TypeKind");
  }
}

const char *expr_kind_to_str(ExprKind ek) {
  switch (ek) {
  case Expr_Error:
    return "Expr_Error";
  case Expr_Literal:
    return "Expr_Literal";
  case Expr_UnaryOp:
    return "Expr_UnaryOp";
  case Expr_BinOp:
    return "Expr_BinOp";
  case Expr_Index:
    return "Expr_Index";
  case Expr_Deref:
    return "Expr_Deref";
  case Expr_Addr:
    return "Expr_Addr";
  case Expr_Assignment:
    return "Expr_Assignment";
  case Expr_TypeName:
    return "Expr_TypeName";
  case Expr_FuncCall:
    return "Expr_FuncCall";
  case Expr_Block:
    return "Expr_Block";
  default:
    UNREACHABLE("ExprKind");
  }
}

void expr_reset(Expr *e) { memset(e, 0, sizeof(*e)); }

Parser parser_new_opt(Lexer *l, ParserOpts opts) { return (Parser){.opts = opts, .l = l}; }

bool parser_get_program(Parser *p, Program *prog) {
  Expr e;
  while (parser_get_expression(p, &e)) {
    da_push(&prog->exprs, e);
  }
  if (lexer_has_error(p)) {
    log(ERROR, SB_Fmt, SB_Arg(p->error));
  }
  return e->kind == Expr_Error || lexer_has_error(p);
}

bool parser_get_expression(Parser *p, Expr *e) {
  expr_reset(e);

  size_t error_start = p->error.size;

  Token t = {0};
  LexerState s = lexer_save(p->l);

  if (!lexer_get_token(p->l, &t))
    return false;

  e->loc = t.loc;

  // if (token_is_oneof_array(t, TK_Literal_Any)) {
  //   e->kind = Expr_Literal;
  //   e->as.literal = (ExprLiteral){

  //   };
  //   goto finish_expr;
  // }

  // if (!lexer_expect(p->l, t, TK_Kw_Printf))
  //   goto finish_expr;
  // if (!lexer_get_and_expect(p->l, &t, '(')))
  //   goto finish_expr;
  // if (!lexer_get_and_expect_oneof(p->l, &t, TK_Literal_AnyString, ARRAY_LEN(TK_Literal_AnyString)))
  //   goto finish_expr;
  // e->kind = Expr_Printf;
  // e->as.printf.fmt_text = t.text;
  // e->as.printf.fmt = sb_to_cstr(t.string_value);
  // if (!lexer_get_and_expect_from_array(p->l, &t, ((const TokenKind[2]){',', ')'}))) {
  //   lexer__start_error(p, e->loc, "ill-formed printf call: ");
  //   lexer__finish_error(p, SB_Fmt, SB_Arg(p->l->error));
  //   goto finish_expr;
  // }
  // while (t.kind == ',') {
  //   Expr arg;
  //   if (parser_get_expression(p, &arg)) {
  //     if (arg.kind != Expr_Literal) {
  //       lexer_errorf(p, LEX_LOC_Fmt ": printf only supports literals. Got %s\n", LEX_LOC_Arg(arg.loc),
  //                    expr_kind_to_str(arg.kind));
  //       goto finish_expr;
  //     }
  //     da_push(&e->as.printf, arg.as.literal);
  //   } else {
  //     lexer_errorf(p, LEX_LOC_Fmt ": printf expected arg. Got <not an expr>\n", LEX_LOC_Arg(p->l->loc));
  //     goto finish_expr;
  //   }
  //   if (!lexer_get_token(p->l, &t)) {
  //     lexer_errorf(p, SB_Fmt, SB_Arg(p->l->error));
  //     goto finish_expr;
  //   }
  // }
  // if (!lexer_expect(p->l, t, ')')) {
  //   lexer__report_error_at_loc(p, t.loc, "printf args list must end with ). Got %s", token_kind_to_str(t.kind));
  //   goto finish_expr;
  // }

finish_expr:
  // if (e->kind == Expr_Error) {
  //   if (lexer_has_error(p->l)) {
  //     lexer_errorf(p, SB_Fmt, SB_Arg(p->l->error));
  //   }
  // }
  if (e->kind == Expr_Error || p->error.size > error_start) {
    lexer_restore(p->l, s);
    return false;
  }
  return true;
}

void parser_log_errors(Parser *p) {
  if (lexer_has_error(p)) {
    log(ERROR, "Parser errors:\n" SV_Fmt, SV_Arg(p->error));
  }
}

void parser_diag_remaining_exprs(Parser *p) {
  Expr e;
  StringBuilder sb = {0};
  while (parser_get_expression(p, &e)) {
    parser_diag_expr(INFO, p, e);
    if (e.kind == Expr_Printf) {
      sb_clear(&sb);
      sb_appendf(&sb, "\tfmt=" SV_Fmt, SV_Arg(e.as.printf.fmt_text));
      if (e.as.printf.size)
        sb_append_cstr(&sb, ", args=[");
      da_for_each(Token, arg, e.as.printf) {
        if (arg != e.as.printf.data)
          sb_append_cstr(&sb, ", ");

        switch (arg->kind) {
        case TK_Literal_Integer:
          sb_appendf(&sb, "%d", arg->int_value);
          break;
        case TK_Literal_Float:
          sb_appendf(&sb, "%f", arg->float_value);
          break;
        case TK_Literal_Char:
          sb_appendf(&sb, "\'%c\'", arg->char_value);
          break;
        case TK_Literal_StringSQ: // fallthrough
        case TK_Literal_StringDQ:
          sb_appendf(&sb, SB_Fmt, SB_Arg(arg->string_value));
          break;
        default:
          UNREACHABLE("TokenKind expected literal only");
        }
      }
      if (e.as.printf.size)
        sb_append_cstr(&sb, "]");
      log(INFO, "\t " SB_Fmt, SB_Arg(sb));
    }
  }
}

#endif // PARSER_IMPLEMENTATION