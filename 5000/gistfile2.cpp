#include "unistream.h"

int main()
{
  ounistream out(stdout);

  out << UnicodeString("Hello, world!\n");
}
