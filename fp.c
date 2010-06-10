#include <stdio.h>
#include "gdtoa.h"

double c_to_f(double c_temp)
{
  return 32.0 + ((c_temp * 9.0) / 5.0);
}

double f_to_c(double f_temp)
{
  return (f_temp - 32.0) * (5.0 / 9);
}

int main()
{
  double foo = f_to_c(119.32);
  double bar = c_to_f(foo);
  double baz = 119.3200000001;
  double bow = 119.32;

  int decpt, sign;
  char *se;

  // First, with glibc
  printf("bar = %.15f (%llx)\n", bar, *((long long *)&bar));
  printf("baz = %.15f (%llx)\n", baz, *((long long *)&baz));
  printf("bow = %.15f (%llx)\n", bow, *((long long *)&bow));

  // Then, with gdtoa
  char buf[128];
  g_dfmt(buf, &bar, 15, 127);
  printf("bar = %s\n", buf);
  g_dfmt(buf, &baz, 15, 127);
  printf("baz = %s\n", buf);
  g_dfmt(buf, &bow, 15, 127);
  printf("bow = %s\n", buf);

  return 0;
}
