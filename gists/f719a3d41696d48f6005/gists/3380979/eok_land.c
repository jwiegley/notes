int land1(int a, int b) {
  /*
    CHECK: %0 = load i32* %a.addr, align 4
    CHECK: %tobool = icmp ne i32 %0, 0
    CHECK: br i1 %tobool, label %land.end, label %land.rhs
    CHECK: land.rhs:                                         ; preds = %entry
    CHECK: %1 = load i32* %b.addr, align 4
    CHECK: %tobool1 = icmp ne i32 %1, 0
    CHECK: br label %land.end
    CHECK: land.end:                                         ; preds = %land.rhs, %entry
    CHECK: %2 = phi i1 [ false, %land.end ], [ %tobool1, %land.rhs ]
    CHECK: %land.ext = zext i1 %2 to i32
    CHECK: ret i32 %land.ext
  */
  return a && b;
}

int land2(int a, int b) {
  return (a && b) || (a && b);
}

int land3(int a, int b, int c, int d) {
  return (a && b) || (c && d);
}

int land4(int a, int b, int c, int d) {
  return ((b, c, a) && b) || (a, b, (c && d));
}

int main() {
  if (!land1(10, 10))
    return 1;
  if (land2(10, 20))
    return 1;
  if (!land3(10, 10, 10, 10))
    return 1;
  if (land4(10, 20, 30, 40))
    return 1;
  return 0;
}