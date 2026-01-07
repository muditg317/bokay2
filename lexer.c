#include "tools.h"

enum TokenKind {
    TK_Unknown,
    TK_Identifier,
    TK_Literal,
    TK_OParen,
    TK_CParen,
    TK_OBracket,
    TK_CBracket,
    TK_OCurly,
    TK_CCurly,
    TK_Semicolon,
    TK_Comma,
    TK_Dot,
    TK_Plus,
    TK_Minus,
    TK_Asterisk,
    TK_Slash,
};

const char *token_kind_to_str(enum TokenKind kind) {
    switch (kind) {
        case TK_Unknown: return "Unknown";
        case TK_Identifier: return "Identifier";
        case TK_Literal: return "Literal";
        case TK_OParen: return "OParen";
        case TK_CParen: return "CParen";
        case TK_OBracket: return "OBracket";
        case TK_CBracket: return "CBracket";
        case TK_OCurly: return "OCurly";
        case TK_CCurly: return "CCurly";
        case TK_Semicolon: return "Semicolon";
        case TK_Comma: return "Comma";
        case TK_Dot: return "Dot";
        case TK_Plus: return "Plus";
        case TK_Minus: return "Minus";
        case TK_Asterisk: return "Asterisk";
        case TK_Slash: return "Slash";
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
    size_t tok_len = 1;
    Token *token = &l->token;
    token->kind = TK_Unknown;
    token->loc = l->lex_loc;

    // Simple single-character tokens
    switch (c) {
        case '(': token->kind = TK_OParen; break;
        case ')': token->kind = TK_CParen; break;
        case '[': token->kind = TK_OBracket; break;
        case ']': token->kind = TK_CBracket; break;
        case '{': token->kind = TK_OCurly; break;
        case '}': token->kind = TK_CCurly; break;
        case ';': token->kind = TK_Semicolon; break;
        case ',': token->kind = TK_Comma; break;
        case '.': token->kind = TK_Dot; break;
        case '+': token->kind = TK_Plus; break;
        case '-': token->kind = TK_Minus; break;
        case '*': token->kind = TK_Asterisk; break;
        case '/': token->kind = TK_Slash; break;
        default:
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
            break;
    }

    token->text = sv_chop_front(&l->source, tok_len);
    l->lex_loc.column += tok_len;
    return true;
}