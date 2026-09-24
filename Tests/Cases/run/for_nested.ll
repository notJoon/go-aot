@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"

declare i32 @printf(ptr, ...)

define i32 @main() {
bb0:
  %slot0 = alloca i64
  %slot1 = alloca i64
  store i64 0, ptr %slot0
  br label %bb1

bb1:
  %v0 = load i64, ptr %slot0
  %v1 = icmp slt i64 %v0, 2
  br i1 %v1, label %bb2, label %bb3

bb2:
  store i64 0, ptr %slot1
  br label %bb5

bb3:
  ret i32 0

bb4:
  %v12 = load i64, ptr %slot0
  %v13 = add i64 %v12, 1
  store i64 %v13, ptr %slot0
  br label %bb1

bb5:
  %v2 = load i64, ptr %slot1
  %v3 = icmp slt i64 %v2, 3
  br i1 %v3, label %bb6, label %bb7

bb6:
  %v4 = load i64, ptr %slot1
  %v5 = icmp slt i64 %v4, 1
  br i1 %v5, label %bb9, label %bb10

bb7:
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 8)
  br label %bb4

bb8:
  %v10 = load i64, ptr %slot1
  %v11 = add i64 %v10, 1
  store i64 %v11, ptr %slot1
  br label %bb5

bb9:
  br label %bb8

bb10:
  %v6 = load i64, ptr %slot1
  %v7 = icmp slt i64 1, %v6
  br i1 %v7, label %bb11, label %bb12

bb11:
  br label %bb7

bb12:
  %v8 = load i64, ptr %slot0
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v8)
  %v9 = load i64, ptr %slot1
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v9)
  br label %bb8
}
