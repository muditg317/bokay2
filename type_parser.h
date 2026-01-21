#ifndef TYPE_PARSER_H_
#define TYPE_PARSER_H_

#include <string.h>

#include "lexer.h"
#include "parser.h"
#include "tools.h"

typedef enum TypeKind {
  Type_Void,
  Type_Value,
  Type_Ptr,
  Type_Array,
  Type_Struct,
  Type_Union,
  Type_Func,

  Type_COUNT
} TypeKind;

typedef enum ValueKind {
  Type_Bool,
  Type_IntegerUnsigned,
  Type_IntegerSigned,
  Type_Float,
  Type_String,
} ValueKind;

typedef struct TypeDef TypeDef;
typedef size_t TypeRef;
const TypeRef BAD_TYPE_REF = -1;
typedef struct TypeRefs {
  DA_FIELDS(TypeRef);
} TypeRefs;
typedef struct TypeDefs {
  DA_FIELDS(TypeDef);
} TypeDefs;

typedef struct Variable {
  TypeRef type;
  StringView name;
} Variable;

typedef struct Variables {
  DA_FIELDS(Variable);
} Variables;

typedef struct FuncSignature {
  TypeRef ret;
  Variables params;
} FuncSignature;

typedef struct ArrayDims {
  DA_FIELDS(size_t);
} ArrayDims;

struct TypeDef {
  TypeKind kind;
  size_t size;
  char *name;
  struct Aliases {
    DA_FIELDS(StringView);
  } aliases;

  bool mutable;

  union TypeDefAs {
    ValueKind value;
    TypeRef ptr_to;
    struct Array {
      TypeRef of;
      ArrayDims dims;
    } array;
    TypeRefs compound_fields;
    FuncSignature func_signature;
  } as;
};

const size_t POINTER_SIZE = __SIZEOF_POINTER__ * 8;

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
const TypeDef DEFAULT_TYPES[13] = {
    //    Type_void, Type_u8, Type_u16, Type_u32, Type_u64, Type_s8, Type_s16, Type_s32, Type_s64, Type_f32, Type_f64
    // //};
    (TypeDef){.kind = Type_Void, .size = 0, .name = "void"},
    (TypeDef){.kind = Type_Value, .as.value = Type_Bool, .size = 1, .name = "bool"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerUnsigned, .size = 8, .name = "u8"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerUnsigned, .size = 16, .name = "u16"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerUnsigned, .size = 32, .name = "u32"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerUnsigned, .size = 64, .name = "u64"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerSigned, .size = 8, .name = "s8"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerSigned, .size = 16, .name = "s16"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerSigned, .size = 32, .name = "s32"},
    (TypeDef){.kind = Type_Value, .as.value = Type_IntegerSigned, .size = 64, .name = "s64"},
    (TypeDef){.kind = Type_Value, .as.value = Type_Float, .size = 32, .name = "f32"},
    (TypeDef){.kind = Type_Value, .as.value = Type_Float, .size = 64, .name = "f64"},
    (TypeDef){
        .kind = Type_Value, .as.value = Type_String, .size = 128, .name = "string"}, // string stored as fat pointer
};

const char *type_kind_to_str(TypeKind tk);

void typedef_to_str(TypeDefs *dictionary, TypeDef *type, StringBuilder *sb);
#define typedef_to_str_from_ref(dict, ref, sb) typedef_to_str((dict), span_ptr((dict), (ref)), (sb))
bool typedef_eq(TypeDefs *dictionary, TypeDef *a, TypeDef *b);

#define type_diagx(dict, t, ...)                                                                                       \
  do {                                                                                                                 \
    StringBuilder UNIQUE_VAR(sb) = {0};                                                                                \
    typedef_to_str((dict), (t), &UNIQUE_VAR(sb));                                                                      \
    logx(__VA_ARGS__, SB_Arg(UNIQUE_VAR(sb)));                                                                         \
  } while (0)

void diag_types(TypeDefs *dictionary);

#endif // TYPE_PARSER_H_

#ifdef TYPE_PARSER_IMPL

// =================== Definitions ===================

bool parser_compile_type(Parser *p, TypeRef *type);

// Bokay internal
typedef struct CompileTypeOpts {
  bool no_mods;
  bool allow_funcs;
} CompileTypeOpts;
bool type_parser_compile_type_opt(Parser *p, TypeRef *type, CompileTypeOpts opts);
#define type_parser_compile_type(p, type, ...) type_parser_compile_type_opt((p), (type), (CompileTypeOpts){__VA_ARGS__})

bool type_parser_compile_array_dims(Parser *p, ArrayDims *dims);
bool type_parser_compile_func_type(Parser *p, TypeRef *type);

TypeRef typedefs_find_by_name(TypeDefs *dictionary, StringView typename);
#define parser_type(p, cstr) typedefs_find_by_name(&(p)->type_defs, sv_from_cstr_lit(cstr))
TypeRef typedefs_find_or_register_new(TypeDefs *dictionary, TypeDef type);

typedef struct TypeDefModOpts {
  bool mutable_by_default;
  bool make_mutable;
  bool make_constant;
  bool make_ptr;
  ArrayDims *make_array;
} TypeDefModOpts;
TypeRef typedefs_register_modded_type_opt(TypeDefs *dictionary, TypeRef base_ref, TypeDefModOpts opts);
#define typedefs_register_modded_type(dict, base, ...)                                                                 \
  typedefs_register_modded_type_opt((dict), (base), (TypeDefModOpts){__VA_ARGS__});

// =================== Implementation ===================

static_assert(Type_COUNT == 7, "TypeKind changed count");
const char *type_kind_to_str(TypeKind tk) {
  switch (tk) {
  case Type_Void: return "Type_Void";
  // case Type_Bool: return "Type_Bool";
  // case Type_IntegerUnsigned: return "Type_IntegerUnsigned";
  // case Type_IntegerSigned: return "Type_IntegerSigned";
  // case Type_Float: return "Type_Float";
  // case Type_String: return "Type_String";
  case Type_Value: return "Type_Value";
  case Type_Ptr: return "Type_Ptr";
  case Type_Array: return "Type_Array";
  case Type_Struct: return "Type_Struct";
  case Type_Union: return "Type_Union";
  case Type_Func: return "Type_Func";
  default: UNREACHABLE("TypeKind");
  }
}

static_assert(Type_COUNT == 7, "Update typedef_to_str");
void typedef_to_str(TypeDefs *dictionary, TypeDef *type, StringBuilder *sb) {
  if (type->kind != Type_Void) sb_append_cstr(sb, type->mutable ? "mutable " : "const ");
  switch (type->kind) {
  case Type_Void: {
    sb_append_cstr(sb, "void");
  } break;
  case Type_Value: {
    switch (type->as.value) {
    case Type_Bool: {
      sb_append_cstr(sb, "bool");
    } break;
    case Type_IntegerUnsigned: {
      sb_appendf(sb, "u%zu", type->size);
    } break;
    case Type_IntegerSigned: {
      sb_appendf(sb, "s%zu", type->size);
    } break;
    case Type_Float: {
      sb_appendf(sb, "f%zu", type->size);
    } break;
    case Type_String: {
      sb_appendf(sb, "string", type->size);
    } break;
    }
  } break;
  case Type_Ptr: {
    sb_append_cstr(sb, "*(");
    typedef_to_str_from_ref(dictionary, type->as.ptr_to, sb);
    sb_append(sb, ')');
  } break;
  case Type_Array: {
    sb_append(sb, '(');
    typedef_to_str_from_ref(dictionary, type->as.array.of, sb);
    sb_append_cstr(sb, ")[");
    da_for_each(size_t, dim, type->as.array.dims) {
      if (dim != &span_at(&type->as.array.dims, 0)) sb_append_cstr(sb, ", ");
      sb_appendf(sb, "%zu", *dim);
    }
    sb_append(sb, ']');
  } break;
  case Type_Struct: {

  } break;
  case Type_Union: {

  } break;
  case Type_Func: {
    sb_append_cstr(sb, "(func(");
    da_for_each(Variable, param, type->as.func_signature.params) {
      if (param != span_ptr(&type->as.func_signature.params, 0)) sb_append_cstr(sb, ", ");
      sb_appendf(sb, SV_Fmt ": ", SV_Arg(param->name));
      typedef_to_str_from_ref(dictionary, param->type, sb);
    }
    sb_append_cstr(sb, ") => ");
    typedef_to_str_from_ref(dictionary, type->as.func_signature.ret, sb);
    sb_append(sb, ')');
  } break;
  default: UNREACHABLE("TypeKind for typedef to str");
  }
}

bool typedef_eq(TypeDefs *dictionary, TypeDef *a, TypeDef *b) {
  if (a->name && b->name && strcmp(a->name, b->name) == 0) return true;

  if (a->kind != b->kind) return false;
  if (a->size != b->size) return false;
  if (a->mutable != b->mutable) return false;

  switch (b->kind) {
  case Type_Value: return a->as.value == b->as.value;
  case Type_Ptr: return a->as.ptr_to == b->as.ptr_to;
  case Type_Array:
    return typedef_eq(dictionary, span_ptr(dictionary, a->as.array.of), span_ptr(dictionary, b->as.array.of)) &&
           da_eq(a->as.array.dims, b->as.array.dims);
  case Type_Struct: // fallthrough
  case Type_Union: return da_eq(a->as.compound_fields, b->as.compound_fields);
  case Type_Func:
    if (a->as.func_signature.ret != b->as.func_signature.ret ||
        a->as.func_signature.params.size != b->as.func_signature.params.size)
      return false;
    for (size_t i = 0; i < a->as.func_signature.params.size; i++) {
      if (!typedef_eq(dictionary, span_ptr(dictionary, a->as.func_signature.params.data[i].type),
                      span_ptr(dictionary, b->as.func_signature.params.data[i].type)))
        return false;
    }
    return true;
  default: return true;
  }
}

bool parser_compile_type(Parser *p, TypeRef *type) { return type_parser_compile_type(p, type, .allow_funcs = true); }

bool type_parser_compile_type_opt(Parser *p, TypeRef *type, CompileTypeOpts opts) {
  LexerState s = lexer_save(p->l);
  Token t = {0};
  if (!lexer_expect_token(p->l, &t)) { return parser__fwd_lex_errorf(p, "Expected type expression."); }
  if (token_is_oneof_array(t, TK_Keyword_AnyTypeModifier)) {
    // asm("int3");
    // log(INFO, "got a modifier! " LOC_Fmt, LOC_Arg(t.loc));
    if (opts.no_mods) {
      return serror_locf(p, t.loc, "`" SV_Fmt "` not allowed here (cannot follow another type modifier).",
                         SV_Arg(t.text));
    }
    if (!type_parser_compile_type(p, type, .no_mods = true, .allow_funcs = opts.allow_funcs)) {
      return serror_causedf(p, "Failed to compile type expression with `" SV_Fmt "` modifier.", SV_Arg(t.text));
    }
    *type = typedefs_register_modded_type(&p->type_defs, *type, .make_mutable = t.kind.as.kw == Keyword_Mutable,
                                          .make_constant = t.kind.as.kw == Keyword_Constant);
    return true;
  }
  if (token_is(t, TK_Keyword_Func)) {
    if (!opts.allow_funcs) {
      return serror_locf(p, t.loc,
                         "`func` not allowed here (must be root of type expression or wrapped in parentheses).");
    }
    return type_parser_compile_func_type(p, type);
  }
  if (token_is(t, TK_CHAR('*'))) {
    if (!type_parser_compile_type(p, type)) {
      return serror_causedf(p, "Failed to compile pointee type at " LOC_Fmt ".", LOC_Arg(t.loc));
    }
    *type = typedefs_register_modded_type(&p->type_defs, *type, .make_ptr = true);
    return true;
  }
  if (token_is(t, TK_CHAR('('))) {
    LexLoc start = t.loc;
    if (!parser_compile_type(p, type)) {
      return serror_causedf(p, "Failed to compile type expression (started at " LOC_Fmt ").", LOC_Arg(start));
    }
    if (!lexer_get_and_expect(p->l, &t, TK_CHAR(')'))) {
      return parser__fwd_lex_errorf(p, "Unterminated `(` in type expression. Started at " LOC_Fmt, LOC_Arg(start));
    }
    return true;
  }
  if (token_is(t, TK_Ident)) {
    *type = typedefs_find_by_name(&p->type_defs, t.text);
    // asm("int3");
    type_diagx(&p->type_defs, span_ptr(&p->type_defs, *type), DEBUG, (.debug_label = "typedef"),
               "found type for name " SV_Fmt ": " SB_Fmt, SV_Arg(t.text));
    if (*type == BAD_TYPE_REF) { return serror_locf(p, t.loc, "Unknown type name `" SV_Fmt "`", SV_Arg(t.text)); }
    s = lexer_save(p->l);
    if (lexer_get_and_expect(p->l, &t, TK_CHAR('['))) {
      do {
        LexLoc start = t.loc;
        ArrayDims dims = {0};
        if (!type_parser_compile_array_dims(p, &dims)) {
          return serror_causedf(p, "Failed to compile array dimensions (started at " LOC_Fmt ").", LOC_Arg(start));
        }
        logx(DEBUG, (.omit_newline = true), "got array dims: %zu: [", dims.size);
        da_for_each(size_t, dim, dims) { logx(DEBUG, (.omit_prefix = true, .omit_newline = true), "%zu ", *dim); }
        logx(DEBUG, (.omit_prefix = true), "]");
        *type = typedefs_register_modded_type(&p->type_defs, *type, .make_array = &dims);
        s = lexer_save(p->l);
      } while (lexer_get_and_expect(p->l, &t, TK_CHAR('[')));
      lexer_restore(p->l, s);
      return true;
    }
    lexer_restore(p->l, s);
    return true;
  }
  return serror_locf(
      p, t.loc, "Could not parse type expression. Expected one of {mut, const, func, '*', '(', <typename>}. Got %s.",
      token_kind_to_str(t.kind));
}

bool type_parser_compile_array_dims(Parser *p, ArrayDims *dims) {
  Token t = {0};
  while (lexer_get_and_expect(p->l, &t, TK_Literal_Integer)) {
    da_push(dims, t.lit.int_);
    if (!lexer_get_and_expect_from_cstr(p->l, &t, ",]"))
      return parser__fwd_lex_errorf(p, "Array dimensions must be bracket-enclosed, comma-separated integer list.");
    if (token_is(t, TK_CHAR(']'))) return true;
  }
  if (dims->size == 0) return parser__fwd_lex_errorf(p, "Expected at least 1 array dimension.");
  return true;
}

bool type_parser_compile_func_type(Parser *p, TypeRef *type) {
  LexLoc start = p->l->loc;
  TypeDef func_type = {0};
  func_type.kind = Type_Func;
  func_type.size = POINTER_SIZE;
  Variables *params = &func_type.as.func_signature.params;
  TypeRef *ret = &func_type.as.func_signature.ret;

  Token t = {0};

  // Begin parameter list
  if (!lexer_get_and_expect(p->l, &t, TK_CHAR('('))) {
    return parser__fwd_lex_errorf(p, "Function Signature requires parameter list.");
  }
  LexerState s = lexer_save(p->l);
  if (!lexer_expect_token(p->l, &t)) {
    return parser__fwd_lex_errorf(p, "Incomplete function signature. Expected parameter list.");
  }

  // Empty parameter list
  if (token_is(t, TK_CHAR(')'))) goto parse_ret;
  else lexer_restore(p->l, s);

  // Consume parameter list
  while (lexer_get_and_expect(p->l, &t, TK_Ident)) {
    Variable next = {0};
    if (!parser_compile_variable(p, t, &next)) { return serror_causedf(p, "Malformed parameter."); }
    da_push(params, next);
    if (!lexer_get_and_expect_from_cstr(p->l, &t, ",)")) break;
    if (token_is(t, TK_CHAR(')'))) break;
  }
  if (serror_exists(p->l)) {
    return parser__fwd_lex_errorf(p, "Malformed parameter list. Started at " LOC_Fmt ".", LOC_Arg(start));
  }

parse_ret:
  if (!lexer_get_and_expect(p->l, &t, TK_Punct_WideArrow)) {
    return parser__fwd_lex_errorf(p, "Function signature expected `=>` after parameter list.");
  }

  if (!parser_compile_type(p, ret)) {
    return serror_causedf(p, "Failed to parse function return type. Signature started at " LOC_Fmt ".", LOC_Arg(start));
  }

  *type = typedefs_find_or_register_new(&p->type_defs, func_type);
  return true;
}

TypeRef typedefs_find_by_name(TypeDefs *dictionary, StringView typename) {
  TypeRef ref = {0};
  da_for_each(TypeDef, type, *dictionary) {
    ref = type - dictionary->data;
    if (type->name) {
      type_diagx(dictionary, span_ptr(dictionary, ref), TRACE, (.debug_label = "find_typedef"),
                 "check if " SV_Fmt " == %s (" SB_Fmt ")", SV_Arg(typename), type->name);
      if (sv_eq_cstr(typename, type->name)) return ref;
    }
    da_for_each(StringView, alias, type->aliases) {
      type_diagx(dictionary, span_ptr(dictionary, ref), TRACE, (.debug_label = "find_typedef"),
                 "check if " SV_Fmt " == " SV_Fmt " (" SB_Fmt ")", SV_Arg(typename), SV_Arg(*alias));
      if (sv_eq(*alias, typename)) return ref;
    }
  }
  return BAD_TYPE_REF;
}

TypeRef typedefs_find_or_register_new(TypeDefs *dictionary, TypeDef new_type) {
  type_diagx(dictionary, &new_type, DEBUG, (.debug_label = "typedef"), "Check if " SB_Fmt " exists.");
  if (dictionary->size == 23) {
    StringBuilder sb = {0};
    typedef_to_str(dictionary, &new_type, &sb);
    log(INFO, "add 23rd type: " SB_Fmt, SB_Arg(sb));
    // asm("int3");
  }
  TypeRef ref = {0};
  da_for_each(TypeDef, existing, *dictionary) {
    ref = existing - dictionary->data;
    if (typedef_eq(dictionary, existing, &new_type)) return ref;
  }
  da_push(dictionary, new_type);
  return dictionary->size - 1;
}

TypeRef typedefs_register_modded_type_opt(TypeDefs *dictionary, TypeRef base_ref, TypeDefModOpts opts) {
  TypeDef type = {0};
  TypeDef *base = span_ptr(dictionary, base_ref);
  type.kind = base->kind;
  type.size = base->size;
  type.mutable = base->mutable;

  if (opts.make_mutable) {
    type.mutable = true;
    type.as = base->as;
  } else if (opts.make_constant) {
    type.mutable = false;
    type.as = base->as;
  }
  if (opts.make_ptr) {
    type.kind = Type_Ptr;
    type.size = POINTER_SIZE;
    type.mutable = opts.mutable_by_default;
    type.as.ptr_to = base_ref;
  }
  if (opts.make_array) {
    type.kind = Type_Array;
    type.as.array.of = base_ref;
    type.size = base->size;
    da_for_each(size_t, dim, *opts.make_array) { type.size *= *dim; }
    type.mutable = opts.mutable_by_default;
    da_clear(&type.as.array.dims);
    da_concat(&type.as.array.dims, opts.make_array);
  }
  return typedefs_find_or_register_new(dictionary, type);
}

void diag_types(TypeDefs *dictionary) {
  StringBuilder sb = {0};
  da_for_each(TypeDef, type, *dictionary) {
    sb_clear(&sb);
    if (type->name) { sb_appendf(&sb, "%s: ", type->name); }
    if (type->aliases.size) {
      sb_append(&sb, '[');
      da_for_each(StringView, alias, type->aliases) {
        if (alias != type->aliases.data) sb_append_cstr(&sb, ", ");
        sb_append_sv(&sb, *alias);
      }
      sb_append_cstr(&sb, "]: ");
    }
    typedef_to_str(dictionary, type, &sb);
    log(INFO, SB_Fmt, SB_Arg(sb));
  }
}

#endif // TYPE_PARSER_IMPL