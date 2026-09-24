@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"

declare i32 @printf(ptr, ...)

define internal i64 @go_choose(i64 %arg0) {
bb0:
  %slot0 = alloca i64
  store i64 %arg0, ptr %slot0
  %v0 = load i64, ptr %slot0
  %v1 = icmp slt i64 %v0, 2
  br i1 %v1, label %bb1, label %bb2

bb1:
  ret i64 7

bb2:
  %v2 = load i64, ptr %slot0
  %v3 = add i64 %v2, 1
  ret i64 %v3
}

define i32 @main() {
bb0:
  %v0 = call i64 @go_choose(i64 1)
  %v1 = call i64 @go_choose(i64 2)
  %v2 = add i64 %v0, %v1
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v2)
  ret i32 0
}
