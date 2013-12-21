/*
  CHECK: define i32 @main()
*/
int main() {
  /*
    CHECK: ret i32 0
  */
  int a;
  if (a)
    return 1;
  return 0;
}