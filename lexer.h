#ifndef LEXER_H_
#define LEXER_H_

#include "tools.h"

#define LEXER_LOG_PREFIX "bokay.lexer"

typedef enum TokenKind {
  TK_Error = -1,
  // 0-255 reserved for single-character tokens
  TK_EOF = 256,
  TK_Ident,

  TK_LITERAL_MIN,
  TK_Literal_Bool = TK_LITERAL_MIN,
  TK_Literal_Integer,
  TK_Literal_Float,
  TK_Literal_Char,
  TK_Literal_StringSQ, // Single-quoted string
  TK_Literal_StringDQ, // Double-quoted string
  TK_LITERAL_MAX = TK_Literal_StringDQ,

  TK_PUNCT_MIN,
  TK_Punct_PlusPlus = TK_PUNCT_MIN, // ++
  TK_Punct_MinusMinus,              // --
  TK_Punct_Shl,                     // <<
  TK_Punct_Shr,                     // >>
  TK_Punct_AndAnd,                  // &&
  TK_Punct_OrOr,                    // ||
  TK_Punct_PlusEq,                  // +=
  TK_Punct_MinusEq,                 // -=
  TK_Punct_MulEq,                   // *=
  TK_Punct_DivEq,                   // /=
  TK_Punct_ModEq,                   // %=
  TK_Punct_ShlEq,                   // <<=
  TK_Punct_ShrEq,                   // >>=
  TK_Punct_EqualEq,                 // ==
  TK_Punct_NEq,                     // !=
  TK_Punct_LEq,                     // <=
  TK_Punct_GEq,                     // >=
  TK_Punct_AndEq,                   // &=
  TK_Punct_XorEq,                   // ^=
  TK_Punct_OrEq,                    // |=
  TK_Punct_AndAndEq,                // &&=
  TK_Punct_OrOrEq,                  // ||=
  TK_Punct_Arrow,                   // ->
  TK_Punct_WideArrow,               // =>
  TK_Punct_ColonColon,              // ::
  TK_PUNCT_MAX = TK_Punct_ColonColon,

  TK_KEYWORD_MIN,
  TK_Kw_Return = TK_KEYWORD_MIN,
  TK_Kw_Type,
  TK_Kw_Mutable,
  TK_Kw_Constant,
  TK_Kw_Func,
  TK_KEYWORD_MAX = TK_Kw_Func,

  TK_COUNT
} TokenKind;

const TokenKind TK_Literal_AnyString[2] = {
  TK_Literal_StringSQ, TK_Literal_StringDQ
};
const TokenKind TK_Literal_Any[TK_LITERAL_MAX-TK_LITERAL_MIN+1] = {
  [-TK_LITERAL_MIN+TK_Literal_Bool] = TK_Literal_Bool,
  [-TK_LITERAL_MIN+TK_Literal_Integer] = TK_Literal_Integer,
  [-TK_LITERAL_MIN+TK_Literal_Float] = TK_Literal_Float,
  [-TK_LITERAL_MIN+TK_Literal_Char] = TK_Literal_Char,
  [-TK_LITERAL_MIN+TK_Literal_StringSQ] = TK_Literal_StringSQ,
  [-TK_LITERAL_MIN+TK_Literal_StringDQ] = TK_Literal_StringDQ,
};

const char *puncts[TK_PUNCT_MAX - TK_PUNCT_MIN + 1] = {
    [-TK_PUNCT_MIN + TK_Punct_PlusPlus] = "++",  [-TK_PUNCT_MIN + TK_Punct_MinusMinus] = "--",
    [-TK_PUNCT_MIN + TK_Punct_Shl] = "<<",       [-TK_PUNCT_MIN + TK_Punct_Shr] = ">>",
    [-TK_PUNCT_MIN + TK_Punct_AndAnd] = "&&",    [-TK_PUNCT_MIN + TK_Punct_OrOr] = "||",
    [-TK_PUNCT_MIN + TK_Punct_PlusEq] = "+=",    [-TK_PUNCT_MIN + TK_Punct_MinusEq] = "-=",
    [-TK_PUNCT_MIN + TK_Punct_MulEq] = "*=",     [-TK_PUNCT_MIN + TK_Punct_DivEq] = "/=",
    [-TK_PUNCT_MIN + TK_Punct_ModEq] = "%=",     [-TK_PUNCT_MIN + TK_Punct_ShlEq] = "<<=",
    [-TK_PUNCT_MIN + TK_Punct_ShrEq] = ">>=",    [-TK_PUNCT_MIN + TK_Punct_EqualEq] = "==",
    [-TK_PUNCT_MIN + TK_Punct_NEq] = "!=",       [-TK_PUNCT_MIN + TK_Punct_LEq] = "<=",
    [-TK_PUNCT_MIN + TK_Punct_GEq] = ">=",       [-TK_PUNCT_MIN + TK_Punct_AndEq] = "&=",
    [-TK_PUNCT_MIN + TK_Punct_XorEq] = "^=",     [-TK_PUNCT_MIN + TK_Punct_OrEq] = "|=",
    [-TK_PUNCT_MIN + TK_Punct_AndAndEq] = "&&=", [-TK_PUNCT_MIN + TK_Punct_OrOrEq] = "||=",
    [-TK_PUNCT_MIN + TK_Punct_Arrow] = "->",     [-TK_PUNCT_MIN + TK_Punct_WideArrow] = "=>",
    [-TK_PUNCT_MIN + TK_Punct_ColonColon] = "::"};

const char *keywords[TK_KEYWORD_MAX - TK_KEYWORD_MIN + 1] = {
    [-TK_KEYWORD_MIN + TK_Kw_Return] = "return",
    [-TK_KEYWORD_MIN + TK_Kw_Type] = "type",
    [-TK_KEYWORD_MIN + TK_Kw_Mutable] = "mut",
    [-TK_KEYWORD_MIN + TK_Kw_Constant] = "const",
    [-TK_KEYWORD_MIN + TK_Kw_Func] = "func",
};

static_assert(TK_COUNT == 255 + 39, "TokenKind enum changed");
const char *token_kind_to_str(TokenKind kind) {
  if (kind >= 0 && kind <= 255) {
    static char buf[4] = {'\'', 0, '\'', 0};
    buf[1] = (char)kind;
    return buf;
  }
  if (kind >= TK_LITERAL_MIN && kind <= TK_LITERAL_MAX) {
    switch (kind) {
    case TK_Literal_Bool:
      return "TK_Literal_Bool";
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
    default:
      TOOLS_UNREACHABLE("Unknown literal token kind");
    }
  }
  if (kind >= TK_PUNCT_MIN && kind <= TK_PUNCT_MAX) {
    return puncts[(size_t)(kind - TK_PUNCT_MIN)];
  }
  if (kind >= TK_KEYWORD_MIN && kind <= TK_KEYWORD_MAX) {
    return keywords[(size_t)(kind - TK_KEYWORD_MIN)];
  }
  switch (kind) {
  case TK_Error:
    return "TK_Error";
  case TK_EOF:
    return "TK_EOF";
  case TK_Ident:
    return "TK_Ident";
  default:
    TOOLS_UNREACHABLE("Unknown token kind");
  }
}

typedef struct LexLoc {
  const char *filepath;
  size_t line;
  size_t column;
} LexLoc;
#define LEX_LOC_Fmt "%s:%zu:%-4zu"
#define LEX_LOC_Arg(loc) (loc).filepath, (loc).line, (loc).column

#define lexer_advance_loc(loc, n) ((LexLoc){.filepath = (loc).filepath, .line = (loc).line, .column = (loc).column + (n)})

typedef struct Token {
  TokenKind kind;
  LexLoc loc;
  StringView text;

  bool lit_bool;
  size_t lit_int;
  double lit_float;
  char lit_char;
  StringBuilder lit_string;
} Token;

void token_reset(Token *t);
bool token_is(Token t, TokenKind tk);
bool token_is_oneof(Token t, const TokenKind *tks, size_t tk_count);
#define token_is_oneof_array(t, tks) (token_is_oneof((t), (tks), ARRAY_LEN((tks))))

typedef struct LexerState {
  StringView source;
  LexLoc loc;
} LexerState;

typedef struct LexerOpts {
  const char *filepath;
  bool keep_comments;
  bool no_float_literals;
} LexerOpts;
typedef struct Lexer {
  LexerOpts opts;
  StringView source;
  LexLoc loc;

  StringBuilder error;
} Lexer;

// Lexer API
Lexer lexer_new_opt(StringView source, LexerOpts opts);
#define lexer_new(source, ...) lexer_new_opt((source), (LexerOpts){__VA_ARGS__})


bool lexer_get_token(Lexer *l, Token *t);
bool lexer_expect(Lexer *l, Token t, TokenKind tk);
bool lexer_expect_oneof(Lexer *l, Token t, const TokenKind *tks, size_t tk_count);
#define lexer_expect_from_cstr(l, t, cstr) lexer_expect_oneof((l), (t), (const TokenKind *)(cstr), strlen((cstr))-1)
#define lexer_expect_from_array(l, t, arr) lexer_expect_oneof((l), (t), (arr), ARRAY_LEN((arr)))
bool lexer_get_and_expect(Lexer *l, Token *t, TokenKind tk);
bool lexer_get_and_expect_oneof(Lexer *l, Token *t, const TokenKind *tks, size_t tk_count);
#define lexer_get_and_expect_from_cstr(l, t, cstr) lexer_get_and_expect_oneof((l), (t), (const TokenKind *)(cstr), strlen((cstr))-1)
#define lexer_get_and_expect_from_array(l, t, arr) lexer_get_and_expect_oneof((l), (t), (arr), ARRAY_LEN((arr)))
#define lexer_loc(l) ((l)->loc)
#define lexer_has_error(l) ((l)->error.size > 0)
#define lexer_clear_error(l) sb_clear(&(l)->error)
void lexer_log_errors(Lexer *l);
LexerState lexer_save(Lexer *l);
void lexer_restore(Lexer *l, LexerState state);

void lexer_diag_remaining_tokens(Lexer *l);
#define lexer_diag_tok(level, l, t)                                                                                    \
  log(level, LEX_LOC_Fmt ": [%s] " SV_Fmt, LEX_LOC_Arg((t).loc), token_kind_to_str((t).kind),      \
      SV_Arg((t).text))

// internal definitions
#define lexer_errorf(l, fmt, ...) sb_appendf(&(l)->error, fmt __VA_OPT__(,) __VA_ARGS__)
#define lexer__start_error(l, loc, fmt, ...)                                                                           \
  lexer_errorf((l), LEX_LOC_Fmt ": " fmt, LEX_LOC_Arg((loc)) __VA_OPT__(, ) __VA_ARGS__)
#define lexer__continue_error(l, fmt, ...) lexer_errorf((l), fmt __VA_OPT__(, ) __VA_ARGS__)
#define lexer__finish_error(l, fmt, ...) lexer_errorf((l), fmt "\n" __VA_OPT__(, ) __VA_ARGS__)
#define lexer__report_error_at_loc(l, loc, fmt, ...)                                                                   \
  (lexer__start_error((l), (loc), fmt __VA_OPT__(, ) __VA_ARGS__), lexer__finish_error((l), ""))
#define lexer__report_error(l, offset, fmt, ...)                                                                       \
  lexer__report_error_at_loc((l), lexer_advance_loc((l)->loc, (offset)), fmt __VA_OPT__(, ) __VA_ARGS__)

bool lexer__skip_whitespace(Lexer *l);
bool lexer__skip_comment(Lexer *l);

bool lexer__is_ident_start(char c) { return isalpha(c) || c == '_'; }
bool lexer__is_ident(char c) { return isalnum(c) || c == '_'; }


#endif // LEXER_H_

#ifdef LEXER_IMPLEMENTATION

void token_reset(Token *t) { sb_free(&t->lit_string); memset(t, 0, sizeof(*t)); }
bool token_is(Token t, TokenKind tk) { return token_is_oneof(t, &tk, 1); }
bool token_is_oneof(Token t, const TokenKind *tks, size_t tk_count) {
  for (const TokenKind *tk = tks; tk < tks + tk_count; ++tk) {
    if (t.kind == *tk) return true;
  }
  return false;
}

Lexer lexer_new_opt(StringView source, LexerOpts opts) {
  if (!opts.filepath) opts.filepath = "unknown_file";

  return (Lexer){
      .opts = opts,
      .source = source,
      .loc = {.filepath = opts.filepath, .line = 1, .column = 1},
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
      l->loc.line++;
      l->loc.column = 1;
    } else {
      l->loc.column++;
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
    l->loc.line++;
    l->loc.column = 1;
    return true;
  }
  // Multi-line comment /* ... */
  sv_chop_front_ignore(&l->source, 1); // chop the '*'
  while (l->source.size >= 2) {
    char c0 = sv_at(l->source, 0);
    char c1 = sv_at(l->source, 1);
    if (c0 == '*' && c1 == '/') {
      sv_chop_front_ignore(&l->source, 2); // chop the '*/'
      l->loc.column += 2;
      return true;
    }
    if (c0 == '\n') {
      l->loc.line++;
      l->loc.column = 1;
    } else {
      l->loc.column++;
    }
    sv_chop_front_ignore(&l->source, 1);
  }
  // Unterminated comment
  return true;
}

// False on error
bool lexer_get_token(Lexer *l, Token *t) {
  token_reset(t);

  size_t error_start = l->error.size;
  while (lexer__skip_whitespace(l) || lexer__skip_comment(l)) {
  }

  if (l->source.size <= 0) {
    return false;
  }

  t->kind = TK_EOF;
  t->loc = l->loc;
  size_t tok_len = 0;


  char c = l->source.data[0];
  t->kind = c; // Default to single-character token
  tok_len = 1;

  // Check for multi-character punctuators
  for (size_t tk_punct = 0; tk_punct < TK_PUNCT_MAX - TK_PUNCT_MIN; ++tk_punct) {
    const char *punct = puncts[tk_punct];
    if (sv_starts_with(l->source, punct)) {
      t->kind = (TokenKind)(TK_PUNCT_MIN + tk_punct);
      tok_len = strlen(punct);
      goto finish_token;
    }
  }

  // Numeric literals
  if (isdigit(c)) {
    t->kind = TK_Literal_Integer;
    t->lit_int = c-'0';
    size_t mantissa = 0;
    size_t mantisa_div = 1;
    // Consume numeric literal characters
    while (tok_len < l->source.size) {
      char nc = l->source.data[tok_len];
      if (isdigit(nc)) {
        tok_len++;
        if (t->kind == TK_Literal_Integer) {
          t->lit_int = t->lit_int*10 + nc-'0';
        } else {
          mantissa = mantissa*10 + nc-'0';
          mantisa_div *= 10;
        }
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
    if (t->kind == TK_Literal_Float) {
      t->lit_float = t->lit_int + (double)mantissa/mantisa_div;
      t->lit_int = 0;
    }
  }

  // Identifiers (and keywords?)
  if (lexer__is_ident_start(c)) {
    t->kind = TK_Ident;
    // Consume identifier characters
    while (tok_len < l->source.size) {
      char nc = l->source.data[tok_len];
      if (lexer__is_ident(nc)) {
        tok_len++;
      } else {
        break;
      }
    }
    // Check for true/false literals
    if (sv_eq_cstr(sv_prefix(l->source, tok_len), "true")) {
      t->kind = TK_Literal_Bool;
      t->lit_bool = true;
      goto finish_token;
    }
    if (sv_eq_cstr(sv_prefix(l->source, tok_len), "false")) {
      t->kind = TK_Literal_Bool;
      t->lit_bool = false;
      goto finish_token;
    }
    // Check if identifier is a keyword
    for (size_t tk_keyword = 0; tk_keyword < TK_KEYWORD_MAX - TK_KEYWORD_MIN + 1; ++tk_keyword) {
      if (sv_eq_cstr(sv_prefix(l->source, tok_len), keywords[tk_keyword])) {
        t->kind = (TokenKind)(TK_KEYWORD_MIN + tk_keyword);
        break;
      }
    }
    goto finish_token;
  }

  if (c == '\'' || c == '"') {
    // Character or string literal
    char quote_char = c;
    bool is_char_literal =
        sv_len(l->source) >= 3 && (c == '\'') && sv_at(l->source, 1) != '\\' && sv_at(l->source, 2) == '\'';
    if (is_char_literal) {
      t->kind = TK_Literal_Char;
      tok_len = 3; // 'c'
      t->lit_char = sv_at(l->source, 1);
      goto finish_token;
    }
    t->kind = quote_char == '"' ? TK_Literal_StringDQ : TK_Literal_StringSQ;
    tok_len = 1; // Start after opening quote
    bool closed = false;
    LexLoc endLoc = l->loc;
    while (tok_len < l->source.size) {
      char nc = l->source.data[tok_len];
      if (nc == '\\') {
        // Escape sequence, skip next character
        tok_len += 2;
        endLoc.column += 2;
        switch (sv_at(l->source, tok_len - 1)) {
        case 'n':
          sb_append(&t->lit_string, '\n');
          break;
        case 't':
          sb_append(&t->lit_string, '\t');
          break;
        case 'r':
          sb_append(&t->lit_string, '\r');
          break;
        case '\\':
          sb_append(&t->lit_string, '\\');
          break;
        case '\'':
          sb_append(&t->lit_string, '\'');
          break;
        case '"':
          sb_append(&t->lit_string, '"');
          break;
        default:
          sb_append(&t->lit_string, sv_at(l->source, tok_len - 1));
          break;
        }
      } else if (nc == quote_char) {
        closed = true;
        tok_len++; // Include closing quote
        endLoc.column++;
        break;
      } else {
        if (nc == '\n') {
          // Newline in string literal
          endLoc.line++;
          endLoc.column = 1;
        }
        sb_append(&t->lit_string, nc);
        tok_len++;
      }
    }
    if (!closed) {
      lexer__report_error_at_loc(l, endLoc, "Unterminated %s. Started at " LEX_LOC_Fmt, token_kind_to_str(t->kind),
                                 LEX_LOC_Arg(l->loc));
    }
    goto finish_token;
  }

finish_token:
  if (tok_len > 0) {
    t->text = sv_chop_front(&l->source, tok_len);
    l->loc.column += tok_len;
  }
  if (l->error.size <= error_start) t->kind = TK_Error;
  return l->error.size <= error_start;
}

bool lexer_expect(Lexer *l, Token t, TokenKind tk) { return lexer_expect_oneof(l, t, &tk, 1); }

bool lexer_expect_oneof(Lexer *l, Token t, const TokenKind *tks, size_t tk_count) {
  if (token_is_oneof(t, tks, tk_count)) return true;

  lexer__start_error(l, t.loc, "Expected one of {");
  for (const TokenKind *tk = tks; tk < tks + tk_count; ++tk) {
    lexer__continue_error(l, "%s", token_kind_to_str(*tk));
    if (tk + 1 < tks + tk_count)
      lexer__continue_error(l, " or ");
  }
  lexer__finish_error(l, "}, but got %s", token_kind_to_str(t.kind));
  return false;
}

bool lexer_get_and_expect(Lexer *l, Token *t, TokenKind tk) {
  if (!lexer_get_token(l, t)) {
    return false;
  }
  return lexer_expect(l, *t, tk);
}

bool lexer_get_and_expect_oneof(Lexer *l, Token *t, const TokenKind *tks, size_t tk_count) {
  if (!lexer_get_token(l, t)) {
    return false;
  }
  return lexer_expect_oneof(l, *t, tks, tk_count);
}

void lexer_log_errors(Lexer *l) {
  if (lexer_has_error(l)) {
    log(ERROR, "Lexer errors:\n" SV_Fmt, SV_Arg(l->error));
  }
}

LexerState lexer_save(Lexer *l) {
  return (LexerState){
    .source=l->source,
    .loc=l->loc
  };
}

void lexer_restore(Lexer *l, LexerState s) {
  l->source = s.source;
  l->loc = s.loc;
}

void lexer_diag_remaining_tokens(Lexer *l) {
  Token t;
  while (lexer_get_token(l, &t)) {
    lexer_diag_tok(INFO, l, t);
    // if (t.kind == TK_EOF) {
    //   break;
    // }
  }
}

#endif // LEXER_IMPLEMENTATION
