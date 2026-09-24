@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"

declare i32 @printf(ptr, ...)

define internal i1 @go_less(i64 %arg0, i64 %arg1) {
bb0:
  %slot0 = alloca i64
  %slot1 = alloca i64
  store i64 %arg0, ptr %slot0
  store i64 %arg1, ptr %slot1
  %v0 = load i64, ptr %slot0
  %v1 = load i64, ptr %slot1
  %v2 = icmp slt i64 %v0, %v1
  ret i1 %v2
}

define internal i1 @go_not(i1 %arg0) {
bb0:
  %slot0 = alloca i1
  store i1 %arg0, ptr %slot0
  %v0 = load i1, ptr %slot0
  br i1 %v0, label %bb1, label %bb2

bb1:
  ret i1 false

bb2:
  ret i1 true
}

define i32 @main() {
bb0:
  %slot0 = alloca i1
  %slot1 = alloca i1
  %slot2 = alloca i1
  %slot3 = alloca i64
  store i1 false, ptr %slot0
  %v0 = load i1, ptr %slot0
  %v1 = call i1 @go_not(i1 %v0)
  br i1 %v1, label %bb1, label %bb2

bb1:
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 1)
  br label %bb2

bb2:
  %v2 = call i1 @go_less(i64 1, i64 2)
  store i1 %v2, ptr %slot1
  %v3 = load i1, ptr %slot1
  br i1 %v3, label %bb3, label %bb4

bb3:
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 2)
  br label %bb4

bb4:
  %v4 = call i1 @go_not(i1 true)
  br i1 %v4, label %bb5, label %bb6

bb5:
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 3)
  br label %bb7

bb6:
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 4)
  br label %bb7

bb7:
  store i1 false, ptr %slot2
  %v5 = call i1 @go_less(i64 2, i64 1)
  store i1 %v5, ptr %slot2
  %v6 = load i1, ptr %slot2
  %v7 = call i1 @go_not(i1 %v6)
  br i1 %v7, label %bb8, label %bb9

bb8:
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 5)
  br label %bb9

bb9:
  store i64 6, ptr %slot3
  %v8 = load i64, ptr %slot3
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v8)
  ret i32 0
}
