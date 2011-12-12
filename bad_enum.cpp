#include <iostream>
#include <climits>
#include <cassert>

enum System { Mac, Linux, Unix, Windows };

enum IntValues { MinInt = 0x00000000,
                 MaxInt = 0xFFFFFFFF };

int main(int argc, char *[])
{
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
