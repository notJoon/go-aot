@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"

declare i32 @printf(ptr, ...)

define internal i64 @go_fib(i64 %arg0) {
bb0:
  %slot0 = alloca i64
  store i64 %arg0, ptr %slot0
  %v0 = load i64, ptr %slot0
  %v1 = icmp slt i64 %v0, 2
  br i1 %v1, label %bb1, label %bb2

bb1:
  %v2 = load i64, ptr %slot0
  ret i64 %v2

bb2:
  %v3 = load i64, ptr %slot0
  %v4 = sub i64 %v3, 1
  %v5 = call i64 @go_fib(i64 %v4)
  %v6 = load i64, ptr %slot0
  %v7 = sub i64 %v6, 2
  %v8 = call i64 @go_fib(i64 %v7)
  %v9 = add i64 %v5, %v8
  ret i64 %v9
}

define i32 @main() {
bb0:
  %v0 = call i64 @go_fib(i64 10)
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v0)
  ret i32 0
}
