#ifndef BOKAY_H_
#define BOKAY_H_

#include <stdint.h>

#include "lexer.h"
#include "parser.h"
#include "tools.h"

// typedef enum ValueKind { VK_Void, VK_Integer, VK_Float, VK_Char, VK_String, VK_COUNT } ValueKind;

// typedef struct ExprValue {
//   ValueKind kind;

//   bool lit_bool;
//   size_t lit_int;
//   double lit_float;
//   char lit_char;
//   StringView lit_string;
// } Value;

// ValueKind literal_kind_to_value_kind[TK_COUNT] = {
//     [TK_Literal_Integer] = VK_Integer, [TK_Literal_Float] = VK_Float,     [TK_Literal_Char] = VK_Char,
//     [TK_Literal_StringSQ] = VK_String, [TK_Literal_StringDQ] = VK_String,
// };

typedef struct BokayEngine {
  Lexer l;
  Parser p;
} BokayEngine;

typedef struct BokayNewOpts {
  const char *filepath;
  char *src;
  size_t src_len;
  StringView source_sv;
} BokayNewOpts;
bool bokay_new_opt(BokayEngine *b, BokayNewOpts opts);
#define bokay_new(b, ...) bokay_new_opt(b, (BokayNewOpts){__VA_ARGS__})

bool bokay_interpret(BokayEngine *b);

// bool bokay__eval_expr(Expr e, Value *v);
// bool bokay__eval_printf(ExprPrintf ex_printf);

#endif // BOKAY_H_

#ifdef BOKAY_IMPL

bool bokay_new_opt(BokayEngine *b, BokayNewOpts opts) {
  memset(b, 0, sizeof(*b));
  if (opts.filepath) {
    StringBuilder sb = {0};
    if (!read_file(opts.filepath, &sb)) return false;
    opts.source_sv = sb2sv(sb);
  } else if (opts.src) {
    opts.source_sv = sv_new(opts.src, opts.src_len);
  }
  b->l = lexer_new(opts.source_sv, .filepath = opts.filepath);
  b->p = parser_new(&b->l);
  return true;
}

// bool bokay__eval_expr(Expr e, Value *v) {
//   v->kind = VK_Void;
//   switch (e.kind) {
//   case EK_Error: return false;
//   case EK_Literal:
//     v->kind = literal_kind_to_value_kind[e.as.literal.type->kind];
//     switch (v->kind) {
//     case VK_Integer: v->lit_int = e.as.literal.lit_int; break;
//     case VK_Float: v->lit_float = e.as.literal.lit_float; break;
//     case VK_Char: v->lit_char = e.as.literal.lit_char; break;
//     case VK_String: v->lit_string = sb2sv(e.as.literal.lit_string); break;
//     default: UNREACHABLE("ValueKind should only be literal here");
//     }
//     return true;
//     // case EK_Printf: return bokay__eval_printf(e.as.printf);
//   }
//   // return true;
// }

// typedef int (*pf_t)(const char *__restrict __fmt, ...);

// bool bokay__eval_printf(ExprPrintf ex_printf) {
//   static struct { uint32_t args[1024]; } argPack = {0};
//   memset(argPack.args, 0, sizeof(argPack.args));

//   size_t pack_idx = 0;
//   da_for_each(Token, arg, ex_printf) {
//     if (pack_idx >= 1024) {
//       log(ERROR, "too many printf args");
//       return false;
//     }
//     size_t value, lower, upper;
//     switch (arg->kind) {
//     case TK_Literal_Integer:
//       value = arg->lit_int;
//       lower = (value & (~0UL >> 32));
//       upper = (value >> 32);
//       argPack.args[pack_idx++] = *(uint32_t *)(&lower);
//       argPack.args[pack_idx++] = *(uint32_t *)(&upper);
//       break;
//     case TK_Literal_Float:
//       value = *(size_t *)&arg->lit_float;
//       lower = (value & (~0UL >> 32));
//       upper = (value >> 32);
//       argPack.args[pack_idx++] = *(uint32_t *)(&lower);
//       argPack.args[pack_idx++] = *(uint32_t *)(&upper);
//       break;
//     case TK_Literal_Char:
//       // sb_appendf(&sb, "\'%c\'", arg->lit_char);
//       argPack.args[pack_idx++] = *(uint32_t *)(&arg->lit_char);
//       argPack.args[pack_idx++] = 0;
//       break;
//     case TK_Literal_StringSQ: // fallthrough
//     case TK_Literal_StringDQ:
//       value = *(size_t *)&arg->lit_string.data;
//       lower = (value & (~0UL >> 32));
//       upper = (value >> 32);
//       argPack.args[pack_idx++] = *(uint32_t *)(&lower);
//       argPack.args[pack_idx++] = *(uint32_t *)(&upper);
//       break;
//     default: UNREACHABLE("TokenKind expected literal only");
//     }
//   }
//   if (ex_printf.size) {

//     for (int i = 0; i < 16; i++) {
//       printf("%02x ", ((uint8_t *)argPack.args)[i]);
//       if (i % 8 == 7) {
//         printf("\t");
//       }
//     }
//     printf("\n");
//     // printf("Hello from c! %u\n", 5);
//     pf_t pf = printf;
//     pf("Hello from c! %zu %c %f\n", *(uint64_t *)&argPack);
//     printf("fmt=" SV_Fmt "\n", SV_Arg(ex_printf.fmt_text));
//   }
//   printf(ex_printf.fmt, *(uint64_t *)&argPack);
//   return true;
// }

bool bokay_interpret(BokayEngine *b) {
  bool result = true;
  // Program prog;
  // parser_get_program(&b->p, &prog);
  // diag_types(&prog.types);
  // Expr e;
  // Value v;
  // while (parser_compile_top_level_expr(&b->p, &e)) {
  //   parser_diag_expr(INFO, p, e);
  //   if (!bokay__eval_expr(e, &v)) {
  //     log(ERROR, LOC_Fmt ": Failed to evaluate expression %s", LOC_Arg(e.loc), expr_kind_to_str(e.kind));
  //     return_defer(false);
  //   }
  // }

  // defer:
  parser_log_errors(&b->p);
  serror_clear(&b->p);
  parser_diag_remaining_exprs(&b->p);
  parser_log_errors(&b->p);
  // diag_types(&b->p.type_defs);
  return result;
}

#endif