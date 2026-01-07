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
    log(INFO, "Starting lexer");
    const char *filepath = shift(argv, argc);
    StringBuilder sb = {0};
    if (!read_file(filepath, &sb)) return 1;

    StringView sv = sv_new(sb.data, sb.size);

    Lexer l;
    lexer_init(&l, sv);
    Token t;
    while (lexer_next_token(&l)) {
        t = l.token;
        log(INFO, TOK_LOC_Fmt": [%s] "SV_Fmt, TOK_LOC_Arg(filepath, t.loc), token_kind_to_str(t.kind), SV_Arg(t.text));
        // Process token t
    }

    return 0;
}

#define TOOLS_IMPLEMENTATION
#include "tools.h"