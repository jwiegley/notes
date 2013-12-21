%union.foo_t = type { i64 }

define i32 @main() nounwind uwtable ssp {
entry:
  %retval = alloca i32, align 4
  %foo = alloca %union.foo_t, align 8
  store i32 0, i32* %retval
  %l = bitcast %union.foo_t* %foo to i64*
  store i64 10, i64* %l, align 8
  %a = bitcast %union.foo_t* %foo to i32*
  %0 = load i32* %a, align 4
  %cmp = icmp eq i32 %0, 10
  %cond = select i1 %cmp, i32 0, i32 1
  ret i32 %cond
}
