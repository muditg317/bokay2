#include <stdio.h>

// #define TOOLS_IMPLEMENTATION
#include "tools.h"

#include "lexer.c"

int main(int argc, char **argv) {
  const char *program_name = shift(argv, argc);
  if (argc < 1) {
    log(ERROR, "Usage: %s <source-file>", program_name);
    return 1;
  }
  const char *filepath = shift(argv, argc);
  StringBuilder sb = {0};
  if (!read_file(filepath, &sb))
    return 1;

  StringView sv = sv_new(sb.data, sb.size);

  Lexer l = lexer_new(sv, .filepath = filepath);
  Token t = {0};
  //   while (lexer_get_token(&l, &t)) {
  //     lexer_diag_tok(TOOLS_INFO, &l, &t);
  //     // Process token t
  //     if (t.kind == TK_EOF) {
  //       break;
  //     }
  //   }
  if (!lexer_get_and_expect(&l, &t, TK_Ident)) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, TK_Ident)) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, '(')) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, ')')) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, '{')) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, TK_Kw_Printf)) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, '(')) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, TK_Literal_StringDQ)) {
    goto finish;
  }
  printf(SV_Fmt, SV_Arg(t.string_value));
  if (!lexer_get_and_expect(&l, &t, ')')) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, ';')) {
    goto finish;
  }
  if (!lexer_get_and_expect(&l, &t, '}')) {
    goto finish;
  }
  //   while (lexer_get_token(&l, &t)) {
  //     lexer_diag_tok(INFO, &l, t);
  //     // log(INFO, LEX_LOC_Fmt ": [%s] " SV_Fmt, LEX_LOC_Arg(filepath, t.loc), token_kind_to_str(t.kind),
  //     SV_Arg(t.text));
  //     // Process token t
  //     if (t.kind == TK_EOF) {
  //       break;
  //     }
  //   }

finish:
  if (lexer_has_error(&l)) {
    log(ERROR, "Lexer errors:\n" SV_Fmt, SV_Arg(l.error));
    return 1;
  }

  return 0;
}

#define TOOLS_IMPLEMENTATION
#include "tools.h"