@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"
@.true = private unnamed_addr constant [5 x i8] c"true\00"
@.false = private unnamed_addr constant [6 x i8] c"false\00"

declare i32 @printf(ptr, ...)
declare i32 @puts(ptr)

define internal { i64, i1 } @go_split(i64 %arg0) {
bb0:
  %slot0 = alloca i64
  store i64 %arg0, ptr %slot0
  %v0 = load i64, ptr %slot0
  %v1 = sub i64 %v0, 1
  %v2 = load i64, ptr %slot0
  %v3 = icmp sgt i64 %v2, 0
  %ret0.0 = insertvalue { i64, i1 } poison, i64 %v1, 0
  %ret0.1 = insertvalue { i64, i1 } %ret0.0, i1 %v3, 1
  ret { i64, i1 } %ret0.1
}

define i32 @main() {
bb0:
  %slot0 = alloca i64
  %slot1 = alloca i1
  %results0 = call { i64, i1 } @go_split(i64 3)
  %v0 = extractvalue { i64, i1 } %results0, 0
  %v1 = extractvalue { i64, i1 } %results0, 1
  store i64 %v0, ptr %slot0
  store i1 %v1, ptr %slot1
  %v2 = load i64, ptr %slot0
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v2)
  %v3 = load i1, ptr %slot1
  %print0.8 = select i1 %v3, ptr @.true, ptr @.false
  call i32 @puts(ptr %print0.8)
  ret i32 0
}
