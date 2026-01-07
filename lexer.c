#include "tools.h"

#define LEXER_LOG_PREFIX "bokay.lexer"

typedef enum {
  TK_Error = -1,
  // 0-255 reserved for single-character tokens
  TK_EOF = 256,
  TK_Identifier,
  TK_Literal_Integer,
  TK_Literal_Float,
  TK_Literal_Char,
  TK_Literal_StringSQ, // Single-quoted string
  TK_Literal_StringDQ, // Double-quoted string
  TK_Punct_PlusPlus,   // ++
  TK_Punct_MinusMinus, // --
  TK_Punct_Shl,        // <<
  TK_Punct_Shr,        // >>
  TK_Punct_AndAnd,     // &&
  TK_Punct_OrOr,       // ||
  TK_Punct_PlusEq,     // +=
  TK_Punct_MinusEq,    // -=
  TK_Punct_MulEq,      // *=
  TK_Punct_DivEq,      // /=
  TK_Punct_ModEq,      // %=
  TK_Punct_ShlEq,      // <<=
  TK_Punct_ShrEq,      // >>=
  TK_Punct_EqualEq,    // ==
  TK_Punct_NEq,        // !=
  TK_Punct_LEq,        // <=
  TK_Punct_GEq,        // >=
  TK_Punct_AndEq,      // &=
  TK_Punct_XorEq,      // ^=
  TK_Punct_OrEq,       // |=
  TK_Punct_AndAndEq,   // &&=
  TK_Punct_OrOrEq,     // ||=
  TK_Punct_Arrow,      // ->
  TK_Punct_WideArrow,  // =>
  TK_Punct_ColonColon, // ::

  TK_Count
} TokenKind;

static_assert(TK_Count == 255 + 33, "TokenKind enum changed");
const char *token_kind_to_str(TokenKind kind) {
  if (kind >= 0 && kind <= 255) {
    static char buf[4] = {'\'', 0, '\'', 0};
    buf[1] = (char)kind;
    return buf;
  }
  switch (kind) {
  case TK_Error:
    return "TK_Error";
  case TK_EOF:
    return "TK_EOF";
  case TK_Identifier:
    return "TK_Identifier";
  case TK_Literal_Integer:
    return "TK_Literal_Integer";
  case TK_Literal_Float:
    return "TK_Literal_Float";
  case TK_Literal_Char:
    return "TK_Literal_Char";
  case TK_Literal_StringSQ:
    return "TK_Literal_StringSQ";
  case TK_Literal_StringDQ:
    return "TK_Literal_StringDQ";
  case TK_Punct_PlusPlus:
    return "TK_Punct_PlusPlus";
  case TK_Punct_MinusMinus:
    return "TK_Punct_MinusMinus";
  case TK_Punct_Shl:
    return "TK_Punct_Shl";
  case TK_Punct_Shr:
    return "TK_Punct_Shr";
  case TK_Punct_AndAnd:
    return "TK_Punct_AndAnd";
  case TK_Punct_OrOr:
    return "TK_Punct_OrOr";
  case TK_Punct_PlusEq:
    return "TK_Punct_PlusEq";
  case TK_Punct_MinusEq:
    return "TK_Punct_MinusEq";
  case TK_Punct_MulEq:
    return "TK_Punct_MulEq";
  case TK_Punct_DivEq:
    return "TK_Punct_DivEq";
  case TK_Punct_ModEq:
    return "TK_Punct_ModEq";
  case TK_Punct_ShlEq:
    return "TK_Punct_ShlEq";
  case TK_Punct_ShrEq:
    return "TK_Punct_ShrEq";
  case TK_Punct_EqualEq:
    return "TK_Punct_EqualEq";
  case TK_Punct_NEq:
    return "TK_Punct_NEq";
  case TK_Punct_LEq:
    return "TK_Punct_LEq";
  case TK_Punct_GEq:
    return "TK_Punct_GEq";
  case TK_Punct_AndEq:
    return "TK_Punct_AndEq";
  case TK_Punct_XorEq:
    return "TK_Punct_XorEq";
  case TK_Punct_OrEq:
    return "TK_Punct_OrEq";
  case TK_Punct_AndAndEq:
    return "TK_Punct_AndAndEq";
  case TK_Punct_OrOrEq:
    return "TK_Punct_OrOrEq";
  case TK_Punct_Arrow:
    return "TK_Punct_Arrow";
  case TK_Punct_WideArrow:
    return "TK_Punct_WideArrow";
  case TK_Punct_ColonColon:
    return "TK_Punct_ColonColon";
  default:
    TOOLS_UNREACHABLE("Unknown token kind");
    ;
  }
}

typedef struct {
  size_t line;
  size_t column;
} LexLoc;
#define LEX_LOC_Fmt "%s:%zu:%-4zu"
#define LEX_LOC_Arg(filepath, loc) (filepath), (loc).line, (loc).column

#define lexer_advance_loc(loc, n) ((LexLoc){.line = (loc).line, .column = (loc).column + (n)})

typedef struct {
  TokenKind kind;
  LexLoc loc;
  StringView text;

  size_t int_value;
  double float_value;
  char char_value;
} Token;

typedef struct {
  StringView source;
  LexLoc loc;
} LexerState;

typedef struct LexerOpts {
  const char *filepath;
  bool keep_comments;
  bool no_float_literals;
} LexerOpts;
typedef struct {
  LexerOpts opts;
  StringView source;
  LexLoc lex_loc;

  StringBuilder error;
} Lexer;

// Lexer API
Lexer lexer_new_opt(StringView source, LexerOpts opts);
#define lexer_new(source, ...) lexer_new_opt((source), (LexerOpts){__VA_ARGS__})

bool lexer_get_token(Lexer *l, Token *t);
bool lexer_expect_token_kind(Lexer *l, Token t, TokenKind tk);
bool lexer_expect_one_of_token_kinds(Lexer *l, Token t, TokenKind *tks, size_t tk_count);
#define lexer_loc(l) ((l)->lex_loc)
#define lexer_has_error(l) ((l)->error.size > 0)
#define lexer_clear_error(l) sb_clear(&(l)->error)
LexerState lexer_save(Lexer *l);
void lexer_restore(Lexer *l, LexerState state);

// internal definitions
#define lexer__start_error(l, loc, fmt, ...)                                                                           \
  sb_appendf(&(l)->error, LEX_LOC_Fmt ": " fmt, LEX_LOC_Arg((l)->opts.filepath, loc) __VA_OPT__(, ) __VA_ARGS__)
#define lexer__continue_error(l, fmt, ...) sb_appendf(&(l)->error, fmt __VA_OPT__(, ) __VA_ARGS__)
#define lexer__finish_error(l, fmt, ...) sb_appendf(&(l)->error, fmt "\n" __VA_OPT__(, ) __VA_ARGS__)
#define lexer__report_error(l, offset, fmt, ...)                                                                       \
  (lexer__start_error((l), lexer_advance_loc((l)->lex_loc, (offset)), fmt __VA_OPT__(, ) __VA_ARGS__),                 \
   lexer__finish_error((l), ""))

bool lexer__skip_whitespace(Lexer *l);
bool lexer__skip_comment(Lexer *l);

bool lexer__is_ident_start(char c) { return isalpha(c) || c == '_'; }
bool lexer__is_ident(char c) { return isalnum(c) || c == '_'; }

// IMPLEMENTATIONS

Lexer lexer_new_opt(StringView source, LexerOpts opts) {
  if (!opts.filepath) {
    opts.filepath = "unknown_file";
  }
  return (Lexer){
      .opts = opts,
      .source = source,
      .lex_loc = {.line = 1, .column = 1},
      .error = (StringBuilder){0},
  };
}

bool lexer__skip_whitespace(Lexer *l) {
  if (l->source.size <= 0) {
    return false;
  }
  StringView whitespace = sv_trim_left(l->source);
  sv_for_each(it, whitespace) {
    if (*it == '\n') {
      l->lex_loc.line++;
      l->lex_loc.column = 1;
    } else {
      l->lex_loc.column++;
    }
  }
  sv_chop_front_ignore(&l->source, whitespace.size);
  return whitespace.size > 0;
}

bool lexer__skip_comment(Lexer *l) {
  if (l->opts.keep_comments) {
    return false;
  }
  if (l->source.size <= 1) { // Comments need at least 2 chars // or /**/
    return false;
  }
  char buf[2] = {sv_at(l->source, 0), sv_at(l->source, 1)};
  if (buf[0] != '/') {
    return false;
  }
  if (buf[1] != '/' && buf[1] != '*') {
    return false;
  }
  sv_chop_front_ignore(&l->source, 1);
  if (buf[1] == '/') { // Single-line comment
    sv_chop_by_delim(&l->source, '\n');
    l->lex_loc.line++;
    l->lex_loc.column = 1;
    return true;
  }
  // Multi-line comment /* ... */
  sv_chop_front_ignore(&l->source, 1); // chop the '*'
  while (l->source.size >= 2) {
    char c0 = sv_at(l->source, 0);
    char c1 = sv_at(l->source, 1);
    if (c0 == '*' && c1 == '/') {
      sv_chop_front_ignore(&l->source, 2); // chop the '*/'
      l->lex_loc.column += 2;
      return true;
    }
    if (c0 == '\n') {
      l->lex_loc.line++;
      l->lex_loc.column = 1;
    } else {
      l->lex_loc.column++;
    }
    sv_chop_front_ignore(&l->source, 1);
  }
  // Unterminated comment
  return true;
}

// False on error
bool lexer_get_token(Lexer *l, Token *t) {
  memset(t, 0, sizeof(*t)); // Initialize token

  size_t error_start = l->error.size;
  while (lexer__skip_whitespace(l) || lexer__skip_comment(l)) {
  }

  t->kind = TK_EOF;
  t->loc = l->lex_loc;
  size_t tok_len = 0;

  if (l->source.size <= 0) {
    goto finish_token;
  }

  char c = l->source.data[0];
  t->kind = c; // Default to single-character token
  tok_len = 1;

  if (lexer__is_ident_start(c)) {
    t->kind = TK_Identifier;
    // Consume identifier characters
    while (tok_len < l->source.size) {
      char nc = l->source.data[tok_len];
      if (lexer__is_ident(nc)) {
        tok_len++;
      } else {
        break;
      }
    }
    goto finish_token;
  }
  if (isdigit(c)) {
    t->kind = TK_Literal_Integer;
    // Consume numeric literal characters
    while (tok_len < l->source.size) {
      char nc = l->source.data[tok_len];
      if (isdigit(nc)) {
        tok_len++;
      } else if (!l->opts.no_float_literals) { // Handle float literals
        if (nc == '.') {
          if (t->kind == TK_Literal_Float) {
            lexer__report_error(l, (tok_len + 1), "Float literal cannot have two decimal points (got %.*s)",
                                (int)(tok_len + 1), l->source.data);
            goto finish_token;
          }
          t->kind = TK_Literal_Float;
          tok_len++;
        } else {
          break;
        }
      } else {
        break;
      }
    }
  }

finish_token:
  if (tok_len > 0) {
    t->text = sv_chop_front(&l->source, tok_len);
    l->lex_loc.column += tok_len;
  }
  return l->error.size <= error_start;
}

bool lexer_expect_token_kind(Lexer *l, Token t, TokenKind tk) { return lexer_expect_one_of_token_kinds(l, t, &tk, 1); }

bool lexer_expect_one_of_token_kinds(Lexer *l, Token t, TokenKind *tks, size_t tk_count) {
  for (TokenKind *tk = tks; tk < tks + tk_count; ++tk) {
    if (t.kind == *tk) {
      return true;
    }
  }

  lexer__start_error(l, t.loc, "Expected ");
  for (TokenKind *tk = tks; tk < tks + tk_count; ++tk) {
    lexer__continue_error(l, "%s", token_kind_to_str(*tk));
    if (tk + 1 < tks + tk_count)
      lexer__continue_error(l, " or ");
  }
  lexer__finish_error(l, ", but got %s", token_kind_to_str(t.kind));
  return false;
}
