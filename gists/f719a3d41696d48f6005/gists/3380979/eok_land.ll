define i32 @land1(i32 %a, i32 %b) {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  store i32 %b, i32* %b.addr, align 4
  %0 = load i32* %a.addr, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %land.end, label %land.rhs
land.rhs:                                         ; preds = %entry
  %1 = load i32* %b.addr, align 4
  %tobool1 = icmp ne i32 %1, 0
  br label %land.end
land.end:                                         ; preds = %land.rhs, %entry
  %2 = phi i1 [ false, %land.end ], [ %tobool1, %land.rhs ]
  %land.ext = zext i1 %2 to i32
  ret i32 %land.ext
}
define i32 @land2(i32 %a, i32 %b) {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  store i32 %b, i32* %b.addr, align 4
  %0 = load i32* %a.addr, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %land.end, label %land.rhs
lor.rhs:                                          ; preds = %land.end
  %1 = load i32* %a.addr, align 4
  %tobool3 = icmp ne i32 %1, 0
  br i1 %tobool3, label %land.end5, label %land.rhs2
land.rhs:                                         ; preds = %entry
  %2 = load i32* %b.addr, align 4
  %tobool1 = icmp ne i32 %2, 0
  br label %land.end
land.end:                                         ; preds = %land.rhs, %entry
  %3 = phi i1 [ false, %land.end ], [ %tobool1, %land.rhs ]
  br i1 %3, label %lor.end, label %lor.rhs
land.rhs2:                                        ; preds = %lor.rhs
  %4 = load i32* %b.addr, align 4
  %tobool4 = icmp ne i32 %4, 0
  br label %land.end5
land.end5:                                        ; preds = %land.rhs2, %lor.rhs
  %5 = phi i1 [ false, %land.end5 ], [ %tobool4, %land.rhs2 ]
  br label %lor.end
lor.end:                                          ; preds = %land.end5, %land.end
  %6 = phi i1 [ false, %lor.end ], [ %5, %land.end5 ]
  %lor.ext = zext i1 %6 to i32
  ret i32 %lor.ext
}
define i32 @land3(i32 %a, i32 %b, i32 %c, i32 %d) {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %c.addr = alloca i32, align 4
  %d.addr = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  store i32 %b, i32* %b.addr, align 4
  store i32 %c, i32* %c.addr, align 4
  store i32 %d, i32* %d.addr, align 4
  %0 = load i32* %a.addr, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %land.end, label %land.rhs
lor.rhs:                                          ; preds = %land.end
  %1 = load i32* %c.addr, align 4
  %tobool3 = icmp ne i32 %1, 0
  br i1 %tobool3, label %land.end5, label %land.rhs2
land.rhs:                                         ; preds = %entry
  %2 = load i32* %b.addr, align 4
  %tobool1 = icmp ne i32 %2, 0
  br label %land.end
land.end:                                         ; preds = %land.rhs, %entry
  %3 = phi i1 [ false, %land.end ], [ %tobool1, %land.rhs ]
  br i1 %3, label %lor.end, label %lor.rhs
land.rhs2:                                        ; preds = %lor.rhs
  %4 = load i32* %d.addr, align 4
  %tobool4 = icmp ne i32 %4, 0
  br label %land.end5
land.end5:                                        ; preds = %land.rhs2, %lor.rhs
  %5 = phi i1 [ false, %land.end5 ], [ %tobool4, %land.rhs2 ]
  br label %lor.end
lor.end:                                          ; preds = %land.end5, %land.end
  %6 = phi i1 [ false, %lor.end ], [ %5, %land.end5 ]
  %lor.ext = zext i1 %6 to i32
  ret i32 %lor.ext
}
define i32 @land4(i32 %a, i32 %b, i32 %c, i32 %d) {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %c.addr = alloca i32, align 4
  %d.addr = alloca i32, align 4
  store i32 %a, i32* %a.addr, align 4
  store i32 %b, i32* %b.addr, align 4
  store i32 %c, i32* %c.addr, align 4
  store i32 %d, i32* %d.addr, align 4
  %0 = load i32* %b.addr, align 4
  %1 = load i32* %c.addr, align 4
  %2 = load i32* %a.addr, align 4
  %tobool = icmp ne i32 %2, 0
  br i1 %tobool, label %land.end, label %land.rhs
lor.rhs:                                          ; preds = %land.end
  %3 = load i32* %a.addr, align 4
  %4 = load i32* %b.addr, align 4
  %5 = load i32* %c.addr, align 4
  %tobool3 = icmp ne i32 %5, 0
  br i1 %tobool3, label %land.end5, label %land.rhs2
land.rhs:                                         ; preds = %entry
  %6 = load i32* %b.addr, align 4
  %tobool1 = icmp ne i32 %6, 0
  br label %land.end
land.end:                                         ; preds = %land.rhs, %entry
  %7 = phi i1 [ false, %land.end ], [ %tobool1, %land.rhs ]
  br i1 %7, label %lor.end, label %lor.rhs
land.rhs2:                                        ; preds = %lor.rhs
  %8 = load i32* %d.addr, align 4
  %tobool4 = icmp ne i32 %8, 0
  br label %land.end5
land.end5:                                        ; preds = %land.rhs2, %lor.rhs
  %9 = phi i1 [ false, %land.end5 ], [ %tobool4, %land.rhs2 ]
  br label %lor.end
lor.end:                                          ; preds = %land.end5, %land.end
  %10 = phi i1 [ false, %lor.end ], [ %9, %land.end5 ]
  %lor.ext = zext i1 %10 to i32
  ret i32 %lor.ext
}
define i32 @main() {
entry:
  %call = call i32 @land1(i32 10, i32 10)
  %0 = xor i32 %call, -1
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %if.then, label %if.else
if.then:                                          ; preds = %entry
  ret i32 1
  br label %if.end
if.else:                                          ; preds = %entry
  br label %if.end
if.end:                                           ; preds = %if.else, %if.then
  %call2 = call i32 @land2(i32 10, i32 20)
  %tobool3 = icmp ne i32 %call2, 0
  br i1 %tobool3, label %if.then1, label %if.else4
if.then1:                                         ; preds = %if.end
  ret i32 1
  br label %if.end5
if.else4:                                         ; preds = %if.end
  br label %if.end5
if.end5:                                          ; preds = %if.else4, %if.then1
  %call7 = call i32 @land3(i32 10, i32 10, i32 10, i32 10)
  %1 = xor i32 %call7, -1
  %tobool8 = icmp ne i32 %1, 0
  br i1 %tobool8, label %if.then6, label %if.else9
if.then6:                                         ; preds = %if.end5
  ret i32 1
  br label %if.end10
if.else9:                                         ; preds = %if.end5
  br label %if.end10
if.end10:                                         ; preds = %if.else9, %if.then6
  %call12 = call i32 @land4(i32 10, i32 20, i32 30, i32 40)
  %tobool13 = icmp ne i32 %call12, 0
  br i1 %tobool13, label %if.then11, label %if.else14
if.then11:                                        ; preds = %if.end10
  ret i32 1
  br label %if.end15
if.else14:                                        ; preds = %if.end10
  br label %if.end15
if.end15:                                         ; preds = %if.else14, %if.then11
  ret i32 0
}