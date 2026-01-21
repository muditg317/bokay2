#ifndef LEXER_H_
#define LEXER_H_

#include "tools.h"

#define LEXER_LOG_PREFIX "bokay.lexer"

typedef enum TokenBaseKind {
  Token_Error = -1,
  // 0-255 reserved for single-character tokens
  Token_EOF = 256,
  Token_Ident,

  Token_Literal,

  Token_Punct,

  Token_Keyword,

  Token_COUNT,
} TokenBaseKind;

typedef enum TokenLiteralKind {
  Literal_Bool,
  Literal_Integer,
  Literal_Float,
  Literal_Char,
  Literal_StringSQ, // Single-quoted string
  Literal_StringDQ, // Double-quoted string

  LITERAL_COUNT,
} TokenLiteralKind;

typedef enum TokenPunctKind {
  Punct_PlusEq,   // +=
  Punct_MinusEq,  // -=
  Punct_MulEq,    // *=
  Punct_DivEq,    // /=
  Punct_ModEq,    // %=
  Punct_ShlEq,    // <<=
  Punct_ShrEq,    // >>=
  Punct_AndEq,    // &=
  Punct_XorEq,    // ^=
  Punct_OrEq,     // |=
  Punct_AndAndEq, // &&=
  Punct_OrOrEq,   // ||=
  Punct_LAST_ASSIGN = Punct_OrOrEq,
  Punct_EqEqEq,     // ===
  Punct_EqEq,       // ==
  Punct_NEq,        // !=
  Punct_LEq,        // <=
  Punct_GEq,        // >=
  Punct_PlusPlus,   // ++
  Punct_MinusMinus, // --
  Punct_Shl,        // <<
  Punct_Shr,        // >>
  Punct_AndAnd,     // &&
  Punct_OrOr,       // ||
  Punct_Arrow,      // ->
  Punct_WideArrow,  // =>
  Punct_ColonColon, // ::

  PUNCT_COUNT,
} TokenPunctKind;

typedef enum TokenKeywordKind {
  Keyword_If,
  Keyword_Else,
  Keyword_While,
  Keyword_Return,
  Keyword_Type,
  Keyword_Mutable,
  Keyword_Constant,
  Keyword_Func,

  KEYWORD_COUNT,
} TokenKeywordKind;

typedef struct TokenKind {
  TokenBaseKind kind;
  union {
    TokenLiteralKind literal;
    TokenPunctKind punct;
    TokenKeywordKind kw;
  } as;
} TokenKind;
#define TK_CHAR(tk) ((TokenKind){.kind = (TokenBaseKind)(tk)})
#define TK_LITERAL(tk) ((TokenKind){.kind = Token_Literal, .as = {.literal = (tk)}})
#define TK_PUNCT(tk) ((TokenKind){.kind = Token_Punct, .as = {.punct = (tk)}})
#define TK_KEYWORD(tk) ((TokenKind){.kind = Token_Keyword, .as = {.kw = (tk)}})
#define toks_as_array(n, ...) AS_ARRAY(TokenKind __VA_OPT__(, ) __VA_ARGS__)

const TokenKind TK_Error = ((TokenKind){.kind = Token_Error});
const TokenKind TK_EOF = ((TokenKind){.kind = Token_EOF});
const TokenKind TK_Ident = ((TokenKind){.kind = Token_Ident});
const TokenKind TK_Literal_Bool = TK_LITERAL(Literal_Bool);
const TokenKind TK_Literal_Integer = TK_LITERAL(Literal_Integer);
const TokenKind TK_Literal_Float = TK_LITERAL(Literal_Float);
const TokenKind TK_Literal_Char = TK_LITERAL(Literal_Char);
const TokenKind TK_Literal_StringSQ = TK_LITERAL(Literal_StringSQ);
const TokenKind TK_Literal_StringDQ = TK_LITERAL(Literal_StringDQ);
const TokenKind TK_Punct_PlusEq = TK_PUNCT(Punct_PlusEq);
const TokenKind TK_Punct_MinusEq = TK_PUNCT(Punct_MinusEq);
const TokenKind TK_Punct_MulEq = TK_PUNCT(Punct_MulEq);
const TokenKind TK_Punct_DivEq = TK_PUNCT(Punct_DivEq);
const TokenKind TK_Punct_ModEq = TK_PUNCT(Punct_ModEq);
const TokenKind TK_Punct_ShlEq = TK_PUNCT(Punct_ShlEq);
const TokenKind TK_Punct_ShrEq = TK_PUNCT(Punct_ShrEq);
const TokenKind TK_Punct_EqEqEq = TK_PUNCT(Punct_EqEqEq);
const TokenKind TK_Punct_EqEq = TK_PUNCT(Punct_EqEq);
const TokenKind TK_Punct_NEq = TK_PUNCT(Punct_NEq);
const TokenKind TK_Punct_LEq = TK_PUNCT(Punct_LEq);
const TokenKind TK_Punct_GEq = TK_PUNCT(Punct_GEq);
const TokenKind TK_Punct_AndEq = TK_PUNCT(Punct_AndEq);
const TokenKind TK_Punct_XorEq = TK_PUNCT(Punct_XorEq);
const TokenKind TK_Punct_OrEq = TK_PUNCT(Punct_OrEq);
const TokenKind TK_Punct_AndAndEq = TK_PUNCT(Punct_AndAndEq);
const TokenKind TK_Punct_OrOrEq = TK_PUNCT(Punct_OrOrEq);
const TokenKind TK_Punct_PlusPlus = TK_PUNCT(Punct_PlusPlus);
const TokenKind TK_Punct_MinusMinus = TK_PUNCT(Punct_MinusMinus);
const TokenKind TK_Punct_Shl = TK_PUNCT(Punct_Shl);
const TokenKind TK_Punct_Shr = TK_PUNCT(Punct_Shr);
const TokenKind TK_Punct_AndAnd = TK_PUNCT(Punct_AndAnd);
const TokenKind TK_Punct_OrOr = TK_PUNCT(Punct_OrOr);
const TokenKind TK_Punct_Arrow = TK_PUNCT(Punct_Arrow);
const TokenKind TK_Punct_WideArrow = TK_PUNCT(Punct_WideArrow);
const TokenKind TK_Punct_ColonColon = TK_PUNCT(Punct_ColonColon);
const TokenKind TK_Keyword_If = TK_KEYWORD(Keyword_If);
const TokenKind TK_Keyword_Else = TK_KEYWORD(Keyword_Else);
const TokenKind TK_Keyword_While = TK_KEYWORD(Keyword_While);
const TokenKind TK_Keyword_Return = TK_KEYWORD(Keyword_Return);
const TokenKind TK_Keyword_Type = TK_KEYWORD(Keyword_Type);
const TokenKind TK_Keyword_Mutable = TK_KEYWORD(Keyword_Mutable);
const TokenKind TK_Keyword_Constant = TK_KEYWORD(Keyword_Constant);
const TokenKind TK_Keyword_Func = TK_KEYWORD(Keyword_Func);

const TokenKind TK_Literal_AnyString[2] = {TK_LITERAL(Literal_StringSQ), TK_LITERAL(Literal_StringDQ)};
static_assert(LITERAL_COUNT == 6, "token literal count changed");
const TokenKind TK_Literal_Any[LITERAL_COUNT] = {
    [Literal_Bool] = TK_LITERAL(Literal_Bool),         [Literal_Integer] = TK_LITERAL(Literal_Integer),
    [Literal_Float] = TK_LITERAL(Literal_Float),       [Literal_Char] = TK_LITERAL(Literal_Char),
    [Literal_StringSQ] = TK_LITERAL(Literal_StringSQ), [Literal_StringDQ] = TK_LITERAL(Literal_StringDQ),
};

const TokenKind TK_Punct_AnyAssign[Punct_LAST_ASSIGN + 1 + 1] = {
    [Punct_PlusEq] = TK_PUNCT(Punct_PlusEq),
    [Punct_MinusEq] = TK_PUNCT(Punct_MinusEq),
    [Punct_MulEq] = TK_PUNCT(Punct_MulEq),
    [Punct_DivEq] = TK_PUNCT(Punct_DivEq),
    [Punct_ModEq] = TK_PUNCT(Punct_ModEq),
    [Punct_ShlEq] = TK_PUNCT(Punct_ShlEq),
    [Punct_ShrEq] = TK_PUNCT(Punct_ShrEq),
    [Punct_AndEq] = TK_PUNCT(Punct_AndEq),
    [Punct_XorEq] = TK_PUNCT(Punct_XorEq),
    [Punct_OrEq] = TK_PUNCT(Punct_OrEq),
    [Punct_AndAndEq] = TK_PUNCT(Punct_AndAndEq),
    [Punct_OrOrEq] = TK_PUNCT(Punct_OrOrEq),
    TK_CHAR('='),
};

const TokenKind TK_Punct_AnyUnary[4] = {
    TK_CHAR('-'),
    TK_CHAR('*'),
    TK_CHAR('&'),
    TK_CHAR('!'),
};

const TokenKind TK_Binop_Any[17] = {
    // 0
    TK_PUNCT(Punct_AndAnd),
    TK_PUNCT(Punct_OrOr),
    // 1
    TK_PUNCT(Punct_EqEqEq),
    TK_PUNCT(Punct_EqEq),
    TK_PUNCT(Punct_NEq),
    TK_PUNCT(Punct_LEq),
    TK_PUNCT(Punct_GEq),
    TK_CHAR('<'),
    TK_CHAR('>'),
    // 1.5
    TK_PUNCT(Punct_Shl),
    TK_PUNCT(Punct_Shr),
    // 2
    TK_CHAR('+'),
    TK_CHAR('-'),
    // 3
    TK_CHAR('*'),
    TK_CHAR('/'),
    TK_CHAR('%'),
    // 4
    TK_CHAR('^'),
};

const TokenKind TK_Keyword_AnyTypeModifier[2] = {TK_KEYWORD(Keyword_Mutable), TK_KEYWORD(Keyword_Constant)};

static_assert(PUNCT_COUNT == 26, "token punct count changed");
const char *puncts[PUNCT_COUNT] = {
    [Punct_PlusPlus] = "++",  [Punct_MinusMinus] = "--", [Punct_Shl] = "<<",     [Punct_Shr] = ">>",
    [Punct_AndAnd] = "&&",    [Punct_OrOr] = "||",       [Punct_PlusEq] = "+=",  [Punct_MinusEq] = "-=",
    [Punct_MulEq] = "*=",     [Punct_DivEq] = "/=",      [Punct_ModEq] = "%=",   [Punct_ShlEq] = "<<=",
    [Punct_ShrEq] = ">>=",    [Punct_EqEqEq] = "===",    [Punct_EqEq] = "==",    [Punct_NEq] = "!=",
    [Punct_LEq] = "<=",       [Punct_GEq] = ">=",        [Punct_AndEq] = "&=",   [Punct_XorEq] = "^=",
    [Punct_OrEq] = "|=",      [Punct_AndAndEq] = "&&=",  [Punct_OrOrEq] = "||=", [Punct_Arrow] = "->",
    [Punct_WideArrow] = "=>", [Punct_ColonColon] = "::"};

static_assert(KEYWORD_COUNT == 8, "token keyword count changed");
const char *keywords[KEYWORD_COUNT] = {
    [Keyword_If] = "if",     [Keyword_Else] = "else",   [Keyword_While] = "while",    [Keyword_Return] = "return",
    [Keyword_Type] = "type", [Keyword_Mutable] = "mut", [Keyword_Constant] = "const", [Keyword_Func] = "func",
};

const char *token_kind_to_str(TokenKind kind);
bool token_kind_eq(TokenKind a, TokenKind b);

typedef struct LexLoc {
  const char *filepath;
  size_t line;
  size_t column;
} LexLoc;
#define LOC_Fmt "%s:%zu:%-4zu"
#define LOC_Arg(loc) (loc).filepath, (loc).line, (loc).column

#define lexer_advance_loc(loc, n)                                                                                      \
  ((LexLoc){.filepath = (loc).filepath, .line = (loc).line, .column = (loc).column + (n)})

typedef struct LiteralValue {
  bool bool_;
  size_t int_;
  double float_;
  char char_;
  StringBuilder string_;
} LiteralValue;

typedef struct Token {
  TokenKind kind;
  LexLoc loc;
  StringView text;

  LiteralValue lit;
} Token;

void token_reset(Token *t);
bool token_is(Token t, TokenKind tk);
bool token_is_oneof(Token t, const TokenKind *tks, size_t tk_count);
#define token_is_oneof_array(t, tks) (token_is_oneof((t), (tks), ARRAY_LEN((tks))))

typedef struct LexerOpts {
  const char *filepath;
  bool keep_comments;
  bool no_float_literals;
} LexerOpts;
typedef struct Lexer {
  LexerOpts opts;
  StringView source;
  LexLoc loc;

  SERROR_FIELDS;
} Lexer;

typedef struct LexerState {
  StringView source;
  LexLoc loc;
  size_t error_size;
} LexerState;

// Lexer API
Lexer lexer_new_opt(StringView source, LexerOpts opts);
#define lexer_new(source, ...) lexer_new_opt((source), (LexerOpts){__VA_ARGS__})

bool lexer_get_token(Lexer *l, Token *t);
bool lexer_expect_token(Lexer *l, Token *t); // Disallows EOF
bool lexer_expect(Lexer *l, Token t, TokenKind tk);
bool lexer_expect_oneof(Lexer *l, Token t, const TokenKind *tks, size_t tk_count);
#define lexer_expect_from_cstr(l, t, cstr) lexer_expect_oneof((l), (t), (const TokenKind *)(cstr), strlen((cstr)) - 1)
#define lexer_expect_from_array(l, t, arr) lexer_expect_oneof((l), (t), (arr), ARRAY_LEN((arr)))
bool lexer_get_and_expect(Lexer *l, Token *t, TokenKind tk);
bool lexer_get_and_expect_oneof(Lexer *l, Token *t, const TokenKind *tks, size_t tk_count);
bool lexer_get_and_expect_from_cstr(Lexer *l, Token *t, const char *cstr);
#define lexer_get_and_expect_from_array(l, t, arr) lexer_get_and_expect_oneof((l), (t), (arr), ARRAY_LEN((arr)))
#define lexer_get_and_expect_any(l, t, n, ...) lexer_get_and_expect_from_array((l), (t), toks_as_array(n, __VA_ARGS__))

// __VA_ARGS__ is optional "on_geterror" boolean if return false expression
#define lexer_maybe_consume_tok_full(l, s_, t_, toks, toks_count, ifpresent, ...)                                      \
  do {                                                                                                                 \
    LexerState s_ = lexer_save((l));                                                                                   \
    Token t_ = {0};                                                                                                    \
    if (!lexer_get_token((l), &t_)) TOOLS_MAYBE_DEFAULT(({ return false; }), __VA_ARGS__);                             \
    if (token_is_oneof(t_, (toks), (toks_count))) {                                                                    \
      (ifpresent);                                                                                                     \
    } else lexer_restore((l), s_);                                                                                     \
  } while (0)

// __VA_ARGS__ is optional "on_geterror" boolean if return false expression
#define lexer_maybe_consume_tok(l, tok, ifpresent, ...)                                                                \
  lexer_maybe_consume_tok_full((l), UNIQUE_VAR(s), UNIQUE_VAR(t), (toks_as_array(1, tok)), 1, (ifpresent), __VA_ARGS__)

#define lexer_loc(l) ((l)->loc)
void lexer_log_errors(Lexer *l);
LexerState lexer_save(Lexer *l);
void lexer_restore(Lexer *l, LexerState state);

void lexer_diag_remaining_tokens(Lexer *l);
#define lexer_diag_tok(level, l, t)                                                                                    \
  log(level, LOC_Fmt ": [%s] " SV_Fmt, LOC_Arg((t).loc), token_kind_to_str((t).kind), SV_Arg((t).text))

// internal definitions
#define serror_locf_start(s, loc, fmt, ...)                                                                            \
  serrorf((s), LOC_Fmt "[%s:%-4d]: " fmt, LOC_Arg((loc)), __FILE__, __LINE__ __VA_OPT__(, ) __VA_ARGS__)
#define serror_locf_finish(s, fmt, ...) serrorf((s), fmt "\n" __VA_OPT__(, ) __VA_ARGS__)
#define serror_locf(s, loc, fmt, ...)                                                                                  \
  (serror_locf_start((s), (loc), fmt __VA_OPT__(, ) __VA_ARGS__), serror_locf_finish((s), ""))

bool lexer__skip_whitespace(Lexer *l);
bool lexer__skip_comment(Lexer *l);

bool lexer__is_ident_start(char c) { return isalpha(c) || c == '_'; }
bool lexer__is_ident(char c) { return isalnum(c) || c == '_'; }

#endif // LEXER_H_

#ifdef LEXER_IMPL

static_assert(Token_COUNT == 255 + 6, "TokenKind enum changed");
const char *token_kind_to_str(TokenKind kind) {
  TokenBaseKind base = kind.kind;
  if (base >= 0 && base <= 255) {
    static char buf[4] = {'\'', 0, '\'', 0};
    buf[1] = (char)base;
    return buf;
  }
  if (base == Token_Literal) {
    switch (kind.as.literal) {
    case Literal_Bool: return "Literal_Bool";
    case Literal_Integer: return "Literal_Integer";
    case Literal_Float: return "Literal_Float";
    case Literal_Char: return "Literal_Char";
    case Literal_StringSQ: return "Literal_StringSQ";
    case Literal_StringDQ: return "Literal_StringDQ";
    default: TOOLS_UNREACHABLE("Unknown literal token kind");
    }
  }
  if (base == Token_Punct) { return puncts[kind.as.punct]; }
  if (base == Token_Keyword) { return keywords[kind.as.kw]; }
  switch (base) {
  case Token_Error: return "Token_Error";
  case Token_EOF: return "Token_EOF";
  case Token_Ident: return "Token_Ident";
  default: TOOLS_UNREACHABLE("Unknown token kind");
  }
}

bool token_kind_eq(TokenKind a, TokenKind b) {
  if (a.kind != b.kind) return false;
  switch (a.kind) {
  case Token_Literal: return a.as.literal == b.as.literal;
  case Token_Punct: return a.as.punct == b.as.punct;
  case Token_Keyword: return a.as.kw == b.as.kw;
  default: return true;
  }
}

void token_reset(Token *t) {
  sb_free(&t->lit.string_);
  memset(t, 0, sizeof(*t));
}
bool token_is(Token t, TokenKind tk) { return token_is_oneof(t, &tk, 1); }
bool token_is_oneof(Token t, const TokenKind *tks, size_t tk_count) {
  for (const TokenKind *tk = tks; tk < tks + tk_count; ++tk) {
    if (token_kind_eq(t.kind, *tk)) return true;
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
  if (l->source.size <= 0) { return false; }
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
  if (l->opts.keep_comments) { return false; }
  if (l->source.size <= 1) { // Comments need at least 2 chars // or /**/
    return false;
  }
  char buf[2] = {sv_at(l->source, 0), sv_at(l->source, 1)};
  if (buf[0] != '/') { return false; }
  if (buf[1] != '/' && buf[1] != '*') { return false; }
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
  while (lexer__skip_whitespace(l) || lexer__skip_comment(l)) {}

  t->kind = TK_EOF;
  t->loc = l->loc;
  if (l->source.size <= 0) { return true; } // EOF is valid token

  char c = l->source.data[0];
  t->kind = TK_CHAR(c); // Default to single-character token
  size_t tok_len = 1;

  // Check for multi-character punctuators
  for (size_t tk_punct = 0; tk_punct < PUNCT_COUNT; ++tk_punct) {
    const char *punct = puncts[tk_punct];
    if (sv_starts_with(l->source, punct)) {
      t->kind = TK_PUNCT(tk_punct);
      tok_len = strlen(punct);
      goto finish_token;
    }
  }

  // Numeric literals
  if (isdigit(c)) {
    t->kind = TK_Literal_Integer;
    t->lit.int_ = c - '0';
    size_t mantissa = 0;
    size_t mantisa_div = 1;
    // Consume numeric literal characters
    while (tok_len < l->source.size) {
      char nc = l->source.data[tok_len];
      if (isdigit(nc)) {
        tok_len++;
        if (token_is(*t, TK_Literal_Integer)) {
          t->lit.int_ = t->lit.int_ * 10 + nc - '0';
        } else {
          mantissa = mantissa * 10 + nc - '0';
          mantisa_div *= 10;
        }
      } else if (!l->opts.no_float_literals) { // Handle float literals
        if (nc == '.') {
          if (token_is(*t, TK_Literal_Float)) {
            serror_locf(l, lexer_advance_loc(l->loc, tok_len + 1),
                        "Float literal cannot have two decimal points (got %.*s)", (int)(tok_len + 1), l->source.data);
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
    if (token_is(*t, TK_Literal_Float)) {
      t->lit.float_ = t->lit.int_ + (double)mantissa / mantisa_div;
      t->lit.int_ = 0;
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
      t->lit.bool_ = true;
      goto finish_token;
    }
    if (sv_eq_cstr(sv_prefix(l->source, tok_len), "false")) {
      t->kind = TK_Literal_Bool;
      t->lit.bool_ = false;
      goto finish_token;
    }
    // Check if identifier is a keyword
    logx(DEBUG, (.debug_label = "keywords"), "check if kw: " SV_Fmt, SV_Arg(sv_prefix(l->source, tok_len)));
    for (size_t tk_keyword = 0; tk_keyword < KEYWORD_COUNT; ++tk_keyword) {
      logx(TRACE, (.debug_label = "keywords"), "check kw %s", keywords[tk_keyword]);
      if (sv_eq_cstr(sv_prefix(l->source, tok_len), keywords[tk_keyword])) {
        t->kind = TK_KEYWORD(tk_keyword);
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
      t->lit.char_ = sv_at(l->source, 1);
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
        case 'n': sb_append(&t->lit.string_, '\n'); break;
        case 't': sb_append(&t->lit.string_, '\t'); break;
        case 'r': sb_append(&t->lit.string_, '\r'); break;
        case '\\': sb_append(&t->lit.string_, '\\'); break;
        case '\'': sb_append(&t->lit.string_, '\''); break;
        case '"': sb_append(&t->lit.string_, '"'); break;
        default: sb_append(&t->lit.string_, sv_at(l->source, tok_len - 1)); break;
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
        sb_append(&t->lit.string_, nc);
        tok_len++;
      }
    }
    if (!closed) {
      serror_locf(l, endLoc, "Unterminated %s. Started at " LOC_Fmt, token_kind_to_str(t->kind), LOC_Arg(l->loc));
    }
    goto finish_token;
  }

finish_token:
  if (tok_len > 0) {
    t->text = sv_chop_front(&l->source, tok_len);
    l->loc.column += tok_len;
  }
  if (l->error.size > error_start) t->kind = TK_Error;
  logx(DEBUG, (.debug_label = "token"), "Got token: %s = `" SV_Fmt "`", token_kind_to_str(t->kind), SV_Arg(t->text));
  return l->error.size <= error_start;
}

bool lexer_expect_token(Lexer *l, Token *t) {
  if (!lexer_get_token(l, t)) return false;
  if (token_is(*t, TK_EOF)) {
    // asm("int3");
    serror_locf(l, t->loc, "Unexpected EOF. Expected token");
    return false;
  }
  return true;
}

bool lexer_expect(Lexer *l, Token t, TokenKind tk) { return lexer_expect_oneof(l, t, &tk, 1); }

bool lexer_expect_oneof(Lexer *l, Token t, const TokenKind *tks, size_t tk_count) {
  if (token_is_oneof(t, tks, tk_count)) return true;

  serror_locf_start(l, t.loc, "Expected one of {");
  for (const TokenKind *tk = tks; tk < tks + tk_count; ++tk) {
    serrorf(l, "%s", token_kind_to_str(*tk));
    if (tk + 1 < tks + tk_count) serrorf(l, " or ");
  }
  serror_locf_finish(l, "}, but got %s", token_kind_to_str(t.kind));
  return false;
}

bool lexer_get_and_expect(Lexer *l, Token *t, TokenKind tk) {
  if (!lexer_get_token(l, t)) { return false; }
  return lexer_expect(l, *t, tk);
}

bool lexer_get_and_expect_oneof(Lexer *l, Token *t, const TokenKind *tks, size_t tk_count) {
  if (!lexer_get_token(l, t)) { return false; }
  return lexer_expect_oneof(l, *t, tks, tk_count);
}

bool lexer_get_and_expect_from_cstr(Lexer *l, Token *t, const char *cstr) {
  if (!lexer_get_token(l, t)) { return false; }
  for (const char *c = cstr; *c != '\0'; c++) {
    if (token_is(*t, TK_CHAR(*c))) return true;
  }
  return false;
}

void lexer_log_errors(Lexer *l) {
  if (serror_exists(l)) { log(ERROR, "Lexer errors:\n" SV_Fmt, SV_Arg(l->error)); }
}

LexerState lexer_save(Lexer *l) {
  return (LexerState){.source = l->source, .loc = l->loc, .error_size = l->error.size};
}

void lexer_restore(Lexer *l, LexerState s) {
  l->source = s.source;
  l->loc = s.loc;
  l->error.size = s.error_size;
}

void lexer_diag_remaining_tokens(Lexer *l) {
  Token t;
  while (lexer_expect_token(l, &t)) { lexer_diag_tok(INFO, l, t); }
}

#endif // LEXER_IMPL
