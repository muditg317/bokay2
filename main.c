#include "bokay.h"
#include "tools.h"

int main(int argc, char **argv) {
  const char *program_name = shift(argv, argc);
  if (argc < 1) {
    log(ERROR, "Usage: %s <source-file>", program_name);
    return 1;
  }
  const char *filepath = shift(argv, argc);

  BokayEngine b;
  if (!bokay_new(&b, .filepath = filepath))
    return 1;

  if (!bokay_interpret(&b)) {
    parser_log_errors(&b.p);
    return 1;
  }

  return 0;
}

#define TOOLS_IMPLEMENTATION
#include "tools.h"
#undef TOOLS_IMPLEMENTATION

#define LEXER_IMPLEMENTATION
#include "lexer.h"
#undef LEXER_IMPLEMENTATION

#define PARSER_IMPLEMENTATION
#include "parser.h"
#undef PARSER_IMPLEMENTATION

#define BOKAY_IMPLEMENTATION
#include "bokay.h"
#undef BOKAY_IMPLEMENTATION