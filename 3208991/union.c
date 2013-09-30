int main() {
  union foo_t {
    int a;
    long l;
    char b;
    float c;
  } foo;
  foo.l = 10;
  return foo.a == 10 ? 0 : 1;
}
