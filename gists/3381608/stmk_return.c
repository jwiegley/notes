/*
  CHECK: define i32 @main()
*/
int main() {
  /*
    CHECK: ret i32 0
  */
  int a;
  if (a) {
    return 1;
    a = 10;                     /* this should not appear in the output */
  }
  return 0;
}