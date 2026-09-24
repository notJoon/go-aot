@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"

declare i32 @printf(ptr, ...)

define internal i64 @go_f() {
bb0:
  br label %bb1

bb1:
  br label %bb2

bb2:
  ret i64 1
}

define internal i64 @go_g() {
bb0:
  br label %bb1

bb1:
  br label %bb2

bb2:
  br label %bb1
}

define i32 @main() {
bb0:
  %v0 = call i64 @go_f()
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v0)
  ret i32 0
}
