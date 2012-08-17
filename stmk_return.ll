define i32 @main() {
entry:
  %a = alloca i32, align 4
  %0 = load i32* %a, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %if.then, label %if.end
if.then:                                          ; preds = %entry
  br label %return
if.end:                                           ; preds = %entry
  br label %return
return:                                           ; preds = %if.end, %if.then
  ret i32 %1
}