#include "tools.h"

enum TokenKind {
    TK_Unknown = -1,
    // 0-255 reserved for single-character tokens
    TK_Identifier = 256,
    TK_Literal,
};

const char *token_kind_to_str(enum TokenKind kind) {
    if (kind >= 0 && kind <= 255) {
        static char buf[4] = {'\'', 0, '\'', 0};
        buf[1] = (char)kind;
        return buf;
    }
    switch (kind) {
        case TK_Unknown: return "Unknown";
        case TK_Identifier: return "Identifier";
        case TK_Literal: return "Literal";
        default: TOOLS_UNREACHABLE("Unknown token kind");;
    }
}

typedef struct {
    size_t line;
    size_t column;
} TokenLoc;
#define TOK_LOC_Fmt "%s:%zu:%zu"
#define TOK_LOC_Arg(filepath, loc) (filepath), (loc).line, (loc).column

typedef struct {
    enum TokenKind kind;
    TokenLoc loc;
    StringView text;
} Token;

typedef struct {
    StringView source;
    TokenLoc lex_loc;
    Token token;
} Lexer;

void lexer_init(Lexer *l, StringView source) {
    l->source = source;
    l->lex_loc.line = 1;
    l->lex_loc.column = 1;
}

bool lexer_next_token(Lexer *l) {
    // Skip whitespace
    StringView whitespace = sv_trim_left(l->source);
    sv_for_each(it, whitespace) {
        if (*it == '\n') {
            l->lex_loc.line++;
            l->lex_loc.column = 1;
        } else {
            l->lex_loc.column++;
        }
    }
    sv_chop_front(&l->source, whitespace.size);

    if (l->source.size <= 0) {
        return false; // End of source
    }

    char c = l->source.data[0];
    Token *token = &l->token;
    token->kind = c; // Default to single-character token
    token->loc = l->lex_loc;
    size_t tok_len = 1;

    if (isalpha(c) || c == '_') {
        token->kind = TK_Identifier;
        // Consume identifier characters
        while (tok_len < l->source.size) {
            char nc = l->source.data[tok_len];
            if (isalnum(nc) || nc == '_') {
                tok_len++;
            } else {
                break;
            }
        }
    } else if (isdigit(c)) {
        token->kind = TK_Literal;
        // Consume numeric literal characters
        while (tok_len < l->source.size) {
            char nc = l->source.data[tok_len];
            if (isdigit(nc)) {
                tok_len++;
            } else {
                break;
            }
        }
    }

    token->text = sv_chop_front(&l->source, tok_len);
    l->lex_loc.column += tok_len;
    return true;
}