#include <stdio.h>
int main() {
  fprintf(stderr, "%ld\n", ftell(stdin));
  return 0;
}

