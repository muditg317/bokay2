#include <stdio.h>

#define TOOLS_IMPL
#include "tools.h"

typedef struct {
  SERROR_FIELDS;
} test;

int main() {
  test t = {0};
  bool thing = serror_causedf(&t, "foo");
  printf("%d\n", thing);
}