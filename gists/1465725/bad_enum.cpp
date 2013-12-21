#include <iostream>
#include <climits>
#include <cassert>
#include <cstdlib>

enum ShouldBeTiny { min, a, b, c, d, e, f, max };

class foo {
  ShouldBeTiny flag1;
  ShouldBeTiny flag2;
  ShouldBeTiny flag3;
  ShouldBeTiny flag4;
  ShouldBeTiny flag5;
  ShouldBeTiny flag6;
};

enum System { Mac, Linux, Unix, Windows };

enum IntValues { MinInt = 0x00000000,
                 MaxInt = 0xFFFFFFFF };

int main(int argc, char *[])
{
  foo tiny_object;
  assert(sizeof(foo) < 10);

  static const unsigned long Linux = ULONG_MAX;

  switch (argc) {
  case Linux:
    std::cout << "This is a Linux machine." << std::endl;
  }
    
  std::cout << "Linux is " << Linux
            << "; size is " << sizeof(Linux) << std::endl;
  std::cout << "MaxInt is " << MaxInt
            << "; size is " << sizeof(MaxInt) << std::endl;

  assert(sizeof(Linux) == sizeof(MaxInt));
  assert(sizeof(UINT_MAX) == sizeof(MaxInt));

  return 1;
}