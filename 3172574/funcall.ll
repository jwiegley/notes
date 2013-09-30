; int f() {
;   int x = 10;
;   int * y = &x;
;   return *y;
; }
; 
; int main()
; {
;   return f();
; }

define i32 @_Z1fv() {
entry:
  %0 = alloca i32, i8 4
  %1 = getelementptr i32* %0, i32 0
  store i32 10, i32* %1
  %2 = alloca i32*, i8 8
  %3 = alloca i32*, i8 8
  %4 = getelementptr i32* %0, i32 0
  store i32* %4, i32** %3
  %5 = load i32** %2
  %6 = load i32* %5, align 4
  ret i32 %6
}

define i32 @main() {
entry:
  %0 = call i32 @_Z1fv()
  ret i32 %0
}