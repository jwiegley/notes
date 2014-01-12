void speed_test(void (*f)())
{
  int i;
  for (i = 0; i < 100; i++)
    f();
}
