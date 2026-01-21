#ifndef PROGRAM_TYPECHECK_H_
#define PROGRAM_TYPECHECK_H_

#include <stdint.h>

#include "lexer.h"
#include "parser.h"
#include "tools.h"

#endif // PROGRAM_TYPECHECK_H_

#ifdef PROGRAM_TYPECHECK_IMPL

// =================== Definitions ===================

typedef struct TypeCheckOpt {
  bool has_expected;
  TypeRef expected;
  Type *same_as;
  bool require_assignable;
  bool require_unassignable;
  bool require_boolish;
} TypeCheckOpt;
bool program_typecheck_expr_opt(Program *prog, Expr *expr, TypeCheckOpt opt);
#define program_typecheck_expr(prog, expr, ...) program_typecheck_expr_opt((prog), (expr), (TypeCheckOpt){__VA_ARGS__})

// Bokay internal
bool program_typecheck_verify_assignable(Program *prog, TypeRef receiver, TypeRef value);
bool program_typecheck_verify_binop(Program *prog, TypeRef a, Token op, TypeRef b, TypeRef *result);
bool program_typecheck_verify_unaryop(Program *prog, Token op, TypeRef a, TypeRef *result);

// =================== Implementation ===================

static_assert(EK_COUNT == 16, "ExprKind for typecheck_expr");
bool program_typecheck_expr_opt(Program *prog, Expr *expr, TypeCheckOpt opt) {

  bool result = true;

  // UNUSED(prog);
  switch (expr->kind) {
  case EK_Error: // fallthrough
  case EK_Empty: {
    return_defer(
        serror_locf(prog, expr->loc, "Should have no `%s` expressions in program!", expr_kind_to_str(expr->kind)));
  } break;
  // expressions
  case EK_Block: {
    Type type = {
        .base = typedefs_find_by_name(&prog->types, sv_from_cstr("void")),
        .not_assignable = true,
    };
    da_for_each(Expr, e, expr->as.block.exprs) {
      program_typecheck_expr(prog, e);
      type = e->type;
    }
    expr_copy_type_if_typed(expr, &type);
    return_defer(true);
  } break;
  case EK_If: {
    if (!program_typecheck_expr(prog, expr->as.if_.cond,
                                .expected = typedefs_find_by_name(&prog->types, sv_from_cstr("bool")),
                                .has_expected = true))
      return_defer(serror_causedf(prog, "If condition must have type bool."));
    if (!program_typecheck_expr(prog, expr->as.if_.then))
      return_defer(serror_causedf(prog, "Failed typecheck on if {then} block."));
    if (expr->as.if_.else_ && !program_typecheck_expr(prog, expr->as.if_.else_, .same_as = &expr->as.if_.then->type))
      return_defer(serror_causedf(prog, "Failed typecheck on if {else} block (must match {then} block)."));
    expr_copy_type_if_typed(expr, &expr->as.if_.then->type);
    return_defer(true);
  } break;
  case EK_While: {
    if (!program_typecheck_expr(prog, expr->as.while_.cond,
                                .expected = typedefs_find_by_name(&prog->types, sv_from_cstr("bool")),
                                .has_expected = true))
      return_defer(serror_causedf(prog, "While condition must have type bool."));
    if (!program_typecheck_expr(prog, expr->as.while_.loop))
      return_defer(serror_causedf(prog, "Failed typecheck on while {loop} block."));
    expr_copy_type_if_typed(expr, &expr->as.while_.loop->type);
    return_defer(true);
  } break;
  case EK_Assignment: {
    if (!program_typecheck_expr(prog, expr->as.assignment.lhs, .require_assignable = true))
      return_defer(serror_causedf(prog, "Failed typecheck on assignment lhs."));
    if (!program_typecheck_expr(prog, expr->as.assignment.rhs))
      return_defer(serror_causedf(prog, "Failed typecheck on assignment rhs (must match lhs)."));
    TypeRef out = expr->as.assignment.rhs->type.base;
    // operational assign
    if (!token_is(expr->as.assignment.op, TK_CHAR('=')) &&
        (!program_typecheck_verify_binop(prog, expr->as.assignment.lhs->type.base, expr->as.assignment.op,
                                         expr->as.assignment.rhs->type.base, &out))) {
      static StringBuilder sb = {0};
      sb_clear(&sb);
      sb_appendf(&sb, "Cannot apply binop[%s] to types: {", token_kind_to_str(expr->as.assignment.op.kind));
      typedef_to_str_from_ref(&prog->types, expr->as.assignment.lhs->type.base, &sb);
      sb_appendf(&sb, "} %s {", token_kind_to_str(expr->as.assignment.op.kind));
      typedef_to_str_from_ref(&prog->types, expr->as.assignment.rhs->type.base, &sb);
      sb_append_cstr(&sb, "}.");
      return_defer(serror_locf(prog, expr->as.assignment.op.loc, SB_Fmt, SB_Arg(sb)));
    }
    // asm("int3");
    if (!program_typecheck_verify_assignable(prog, expr->as.assignment.lhs->type.base, out)) {
      static StringBuilder sb = {0};
      sb_clear(&sb);
      sb_appendf(&sb, "Cannot assign rhs to lhs. {lhs=");
      typedef_to_str_from_ref(&prog->types, expr->as.assignment.lhs->type.base, &sb);
      sb_appendf(&sb, "} %s {rhs=", token_kind_to_str(expr->as.assignment.op.kind));
      typedef_to_str_from_ref(&prog->types, expr->as.assignment.rhs->type.base, &sb);
      sb_append_cstr(&sb, "}.");
      return_defer(serror_locf(prog, expr->as.assignment.op.loc, SB_Fmt, SB_Arg(sb)));
    }
    expr_copy_type_if_typed(expr, &expr->as.assignment.lhs->type);
    return_defer(true);
  } break;
  case EK_Ternary: {
    if (!program_typecheck_expr(prog, expr->as.ternary.cond,
                                .expected = typedefs_find_by_name(&prog->types, sv_from_cstr("bool")),
                                .has_expected = true))
      return_defer(serror_causedf(prog, "If condition must have type bool."));
    if (!program_typecheck_expr(prog, expr->as.ternary.iftrue))
      return_defer(serror_causedf(prog, "Failed typecheck on ternary {iftrue} expr."));
    if (!program_typecheck_expr(prog, expr->as.ternary.iffalse, .same_as = &expr->as.ternary.iftrue->type))
      return_defer(serror_causedf(prog, "Failed typecheck on ternary {iffalse} expr (must match {iftrue} expr)."));
    expr_copy_type_if_typed(expr, &expr->as.ternary.iftrue->type);
    return_defer(true);
  } break;
  case EK_BinOp: {
    if (!program_typecheck_expr(prog, expr->as.binop.lhs))
      return_defer(serror_causedf(prog, "Failed typecheck on binop lhs."));
    if (!program_typecheck_expr(prog, expr->as.binop.rhs))
      return_defer(serror_causedf(prog, "Failed typecheck on binop rhs."));
    TypeRef out = {0};
    if (!program_typecheck_verify_binop(prog, expr->as.binop.lhs->type.base, expr->as.binop.op,
                                        expr->as.binop.rhs->type.base, &out)) {
      static StringBuilder sb = {0};
      sb_clear(&sb);
      sb_appendf(&sb, "Cannot apply binop[%s] to types: {", token_kind_to_str(expr->as.binop.op.kind));
      typedef_to_str_from_ref(&prog->types, expr->as.binop.lhs->type.base, &sb);
      sb_appendf(&sb, "} %s {", token_kind_to_str(expr->as.binop.op.kind));
      typedef_to_str_from_ref(&prog->types, expr->as.binop.rhs->type.base, &sb);
      sb_append_cstr(&sb, "}.");
      return_defer(serror_locf(prog, expr->as.binop.op.loc, SB_Fmt, SB_Arg(sb)));
    }
    expr->type.base = out;
    // TODO: assignable
    return_defer(true);
  } break;
  case EK_FuncCall: {

  } break;
  case EK_Index: {

  } break;
  case EK_UnaryOp: {
    if (!program_typecheck_expr(prog, expr->as.unaryop.arg))
      return_defer(serror_causedf(prog, "Failed typecheck on unary op arg."));
    TypeRef out = {0};
    if (!program_typecheck_verify_unaryop(prog, expr->as.unaryop.op, expr->as.unaryop.arg->type.base, &out)) {
      static StringBuilder sb = {0};
      sb_clear(&sb);
      sb_appendf(&sb, "Cannot apply unaryop[%s] to type: {", token_kind_to_str(expr->as.unaryop.op.kind));
      typedef_to_str_from_ref(&prog->types, expr->as.unaryop.arg->type.base, &sb);
      sb_append_cstr(&sb, "}.");
      return_defer(serror_locf(prog, expr->as.unaryop.op.loc, SB_Fmt, SB_Arg(sb)));
    }
    expr->type.base = out;
    // TODO: assignable
    return_defer(true);
  } break;
  case EK_Variable: {
    Variable *existing = scope_stack_find(&prog->scope_stack, expr->as.variable.name);
    if (!existing)
      return_defer(
          serror_locf(prog, expr->loc, "Useof undeclared variable `" SV_Fmt "`.", SV_Arg(expr->as.variable.name)));
    Type t = {
        .base = existing->type,
        .not_assignable = !span_at(&prog->types, existing->type).mutable,
    };
    expr_copy_type_if_typed(expr, &t);
    return_defer(true);
  } break;
  case EK_Literal: {
    Type type = {.not_assignable = true};
    switch (expr->as.literal.kind) {
    case Literal_Bool: {
      type.base = typedefs_find_by_name(&prog->types, sv_from_cstr("bool"));
    } break;
    case Literal_Integer: {
      size_t size = 8;
      while (expr->as.literal.value.int_ >= 1 << size) size <<= 1;
      static char *size_to_type[65] = {
          [8] = "u8",
          [16] = "u16",
          [32] = "u32",
          [64] = "u64",
      };
      type.base = typedefs_find_by_name(&prog->types, sv_from_cstr(size_to_type[size]));
    } break;
    case Literal_Float: {
      type.base = typedefs_find_by_name(&prog->types, sv_from_cstr("f32"));
    } break;
    case Literal_Char: {
      type.base = typedefs_find_by_name(&prog->types, sv_from_cstr("u8"));
    } break;
    case Literal_StringSQ: // fallthrough
    case Literal_StringDQ: {
      type.base = typedefs_find_by_name(&prog->types, sv_from_cstr("string"));
    } break;
    default:
      return_defer(
          serror_locf(prog, expr->loc, "Failed typecheck for literal: unknown kind (%d).", expr->as.literal.kind));
    }
    expr_copy_type_if_typed(expr, &type);
    return_defer(true);
  } break;
  case EK_FunctionLiteral: {
    Scope *new_scope = scope_stack_add_new(&prog->scope_stack);
    TypeDef *signature = span_ptr(&prog->types, expr->as.function_literal.signature);
    da_push(&prog->function_definition_stack, signature->as.func_signature);
    da_for_each(Variable, var, signature->as.func_signature.params) { scope_add(new_scope, *var); }
    Type type = {
        .base = typedefs_find_by_name(&prog->types, sv_from_cstr("void")),
        .not_assignable = true,
    };
    da_for_each(Expr, e, expr->as.function_literal.body.exprs) {
      program_typecheck_expr(prog, e);
      type = e->type;
    }
    Expr *last = &da_last(&expr->as.function_literal.body.exprs);
    if (last->kind == EK_Return && last->as.return_.value) type = last->as.return_.value->type;
    if (!program_typecheck_verify_assignable(prog, signature->as.func_signature.ret, type.base)) {
      static StringBuilder sb = {0};
      sb_clear(&sb);
      sb_appendf(&sb, "Failed typecheck: function body has incorrect type (got=");
      typedef_to_str_from_ref(&prog->types, type.base, &sb);
      sb_appendf(&sb, ", want=");
      typedef_to_str_from_ref(&prog->types, signature->as.func_signature.ret, &sb);
      sb_appendf(&sb, ").");
      return serror_locf(prog, expr->loc, SB_Fmt, SB_Arg(sb));
    }
    if (!scope_stack_pop(&prog->scope_stack, new_scope)) return serrorf(prog, "Bad scope stack!");
    Type func_type = {
        .base = expr->as.function_literal.signature,
        .not_assignable = true,
    };
    expr_copy_type_if_typed(expr, &func_type);
    return_defer(true);
  } break;
  // statements
  case EK_Definition: {
    // asm("int3");
    if (expr->as.definition.rhs) {
      if (!program_typecheck_expr(prog, expr->as.definition.rhs))
        return serror_causedf(prog, "Failed typecheck for rhs of defintion.");
      if (!program_typecheck_verify_assignable(prog, expr->as.definition.var.type,
                                               expr->as.definition.rhs->type.base)) {
        static StringBuilder sb = {0};
        sb_clear(&sb);
        sb_appendf(&sb, "Cannot initialize lhs with rhs. {lhs=");
        typedef_to_str_from_ref(&prog->types, expr->as.definition.var.type, &sb);
        sb_appendf(&sb, "} = {rhs=");
        typedef_to_str_from_ref(&prog->types, expr->as.definition.rhs->type.base, &sb);
        sb_append_cstr(&sb, "}.");
        return_defer(serror_locf(prog, expr->as.definition.rhs->loc, SB_Fmt, SB_Arg(sb)));
      }
    }
    Scope *curr_scope = &da_last(&prog->scope_stack);
    Variable *existing = scope_find(curr_scope, expr->as.definition.var.name);
    if (existing)
      return serror_locf(prog, expr->loc, "Redefinition of " SV_Fmt " within same scope.",
                         SV_Arg(expr->as.definition.var.name));
    scope_add(curr_scope, expr->as.definition.var);
    return_defer(true);
  } break;
  case EK_Return: {
    if (prog->function_definition_stack.size == 0)
      return_defer(serror_locf(prog, expr->loc, "`return` expression must exist within function definition."));
    FuncSignature sig = span_last(&prog->function_definition_stack);
    if (expr->as.return_.value &&
        !program_typecheck_expr(prog, expr->as.return_.value, .expected = sig.ret, .has_expected = true))
      return_defer(serror_causedf(prog, "Failed typecheck for `return` value"));
    return_defer(true);
  } break;
  default: UNREACHABLE("ExprKind in typecheck_expr: %d", expr->kind);
  }

defer:
  if (!result) return result; // passthrough pre-existing failures

  static StringBuilder errors = {0};
  StringBuilder *sb = &errors;
  sb_clear(sb);
  // CHECK: expr->type matches `same_as`
  if (opt.same_as) {
    opt.has_expected = true;
    opt.expected = opt.same_as->base;
    opt.require_assignable = !opt.same_as->not_assignable;
    opt.require_unassignable = opt.same_as->not_assignable;
  }
  // CHECK: expr->type.base matches `expected`
  if (opt.has_expected && expr->type.base != opt.expected) {
    sb_appendf(sb, "Expression has incorrect type. (got=");
    typedef_to_str_from_ref(&prog->types, expr->type.base, sb);
    sb_appendf(sb, ", want=");
    typedef_to_str_from_ref(&prog->types, opt.expected, sb);
    sb_appendf(sb, "). ");
  }
  // CHECK: assignability
  if (opt.require_assignable && expr->type.not_assignable) sb_appendf(sb, "Expression must be assignable.");
  if (opt.require_unassignable && !expr->type.not_assignable) sb_appendf(sb, "Expression must not be assignable.");
  // CHECK: boolish
  if (opt.require_boolish) TODO("require_boolish");

  if (errors.size) serror_locf(prog, expr->loc, SB_Fmt "\n", SB_Arg(errors));
  return result && !serror_exists(prog);
}

bool program_typecheck_verify_assignable(Program *prog, TypeRef receiver, TypeRef value) {
  UNUSED(prog);
  // asm("int3");
  if (value == BAD_TYPE_REF) return false;
  // if (a != b) return false; // allow auto casting
  TypeDef receiver_type = span_at(&prog->types, receiver);
  TypeDef value_type = span_at(&prog->types, value);
  if (receiver != value) {
    // asm("int3");
    if (receiver_type.kind != value_type.kind) return false;
    if (receiver_type.size < value_type.size) return false;
    if (!typedef_as_eq(&prog->types, receiver_type.kind, &receiver_type.as, &value_type.as)) return false;
    // return receiver_type.mutable;
    return true;

    // StringBuilder sb = {0};
    // typedef_to_str(&prog->types, &receiver_type, &sb);
    // log(INFO, "check receiver %zu: " SB_Fmt, receiver, SB_Arg(sb));
    // sb_clear(&sb);
    // typedef_to_str(&prog->types, &value_type, &sb);
    // log(INFO, "check value %zu: " SB_Fmt, value, SB_Arg(sb));
    // sb_free(&sb);
    // return false;
  }
  return true;
}

bool program_typecheck_verify_binop(Program *prog, TypeRef a, Token op, TypeRef b, TypeRef *result) {
  if (a != b) return false; // allow auto casting
  TypeDef *type = span_ptr(&prog->types, a);
  switch (type->kind) {
  case Type_Void:   // fallthrough
  case Type_Array:  // fallthrough
  case Type_Struct: // fallthrough
  case Type_Union:  // fallthrough
  case Type_Func: return false;
  default: break;
  }

  TypeRef bool_type = typedefs_find_by_name(&prog->types, sv_from_cstr("bool"));
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_Punct_NEq, TK_Punct_EqEq))) {
    // equality
    *result = bool_type;
    return true;
  }
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_Punct_EqEqEq))) {
    // ptr equal
    *result = bool_type;
    return true;
  }

  bool is_numeric = false;
  bool is_bitwise = false;
  bool is_bool = false;
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_CHAR('+'), TK_CHAR('-'), TK_Punct_PlusEq, TK_Punct_MinusEq))) {
    // add/sub
    is_numeric = true;
    *result = a;
  }
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_CHAR('*'), TK_CHAR('/'), TK_CHAR('%'), TK_Punct_MulEq,
                                        TK_Punct_DivEq, TK_Punct_ModEq))) {
    // mul/div/mod
    is_numeric = true;
    *result = a;
  }
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_Punct_Shl, TK_Punct_Shr, TK_Punct_ShlEq, TK_Punct_ShrEq))) {
    // shift
    is_bitwise = true;
    *result = a;
  }
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_CHAR('&'), TK_CHAR('|'), TK_CHAR('^'), TK_Punct_AndEq,
                                        TK_Punct_OrEq, TK_Punct_XorEq))) {
    // bit
    is_bitwise = true;
    *result = a;
  }
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_Punct_AndAnd, TK_Punct_OrOr, TK_CHAR('^'), TK_Punct_AndAndEq,
                                        TK_Punct_OrOrEq, TK_Punct_XorEq))) {
    // bool
    is_bool = true;
    *result = a;
  }
  if (token_is_oneof_array(op, AS_ARRAY(TokenKind, TK_CHAR('<'), TK_CHAR('>'), TK_Punct_LEq, TK_Punct_GEq))) {
    // num comparison
    is_numeric = true;
    *result = bool_type;
  }

  switch (type->kind) {
  case Type_Value: {
    if (type->as.value == Type_String) return false; // strings can only be equality compared
    return is_bool ? type->as.value == Type_Bool : (is_bitwise ? type->as.value != Type_Float : is_numeric);
  } break;
  case Type_Ptr: {
    return is_numeric;
  } break;
  default: UNREACHABLE("type->kind second stage in binop verify");
  }
}
bool program_typecheck_verify_unaryop(Program *prog, Token op, TypeRef arg, TypeRef *result) {
  UNUSED(prog);

  bool is_numeric = false;
  bool is_memory = false;
  bool is_negation = false;
  if (token_is(op, TK_CHAR('-'))) {
    *result = arg;
    is_numeric = true;
  } else if (token_is(op, TK_CHAR('*'))) {
    *result = arg;
    is_memory = true;
  } else if (token_is(op, TK_CHAR('&'))) {
    *result = arg;
    is_memory = true;
  } else if (token_is(op, TK_CHAR('!'))) {
    *result = arg;
    is_negation = true;
  }
  TypeDef *type = span_ptr(&prog->types, arg);
  if (is_numeric) {
    // asm("int3");
    if (type->kind != Type_Value) return false;
    if (type->as.value != Type_IntegerUnsigned && type->as.value != Type_IntegerSigned && type->as.value != Type_Float)
      return false;
    if (type->as.value == Type_IntegerUnsigned) {
      TypeDef new = *type;
      new.as.value = Type_IntegerSigned;
      new.name = NULL;
      *result = typedefs_find_or_register_new(&prog->types, new);
    }
    return true;
  }
  if (is_memory) {
    if (token_is(op, TK_CHAR('*'))) {
      if (type->kind != Type_Ptr) return false;
      *result = type->as.ptr_to;
      return true;
    } else if (token_is(op, TK_CHAR('&'))) {
      *result = typedefs_register_modded_type(&prog->types, arg, .make_ptr = true);
    }
  }
  if (is_negation) { return type->kind == Type_Value && type->as.value == Type_Bool; }
  return false;
}

#endif