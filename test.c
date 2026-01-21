#include <stdio.h>

#define TOOLS_IMPL
#include "tools.h"

typedef struct {
  int a;
} test;

int main() {
  test t = {.a = 5, .a = 4};
  printf("%d\n", t.a);
}