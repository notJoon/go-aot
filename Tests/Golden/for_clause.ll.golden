@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
bb0:
  %slot0 = alloca i64
  store i64 0, ptr %slot0
  br label %bb1

bb1:
  %v0 = load i64, ptr %slot0
  %v1 = icmp slt i64 %v0, 4
  br i1 %v1, label %bb2, label %bb3

bb2:
  %v2 = load i64, ptr %slot0
  %v3 = icmp slt i64 %v2, 2
  br i1 %v3, label %bb5, label %bb6

bb3:
  ret i32 0

bb4:
  %v5 = load i64, ptr %slot0
  %v6 = add i64 %v5, 1
  store i64 %v6, ptr %slot0
  br label %bb1

bb5:
  br label %bb4

bb6:
  %v4 = load i64, ptr %slot0
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v4)
  br label %bb4
}
