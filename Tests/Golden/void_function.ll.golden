@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"

declare i32 @printf(ptr, ...)

define internal void @go_f() {
bb0:
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 1)
  ret void
}

define internal void @go_show(i64 %arg0) {
bb0:
  %slot0 = alloca i64
  store i64 %arg0, ptr %slot0
  %v0 = load i64, ptr %slot0
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v0)
  ret void
}

define i32 @main() {
bb0:
  call void @go_f()
  call void @go_show(i64 2)
  ret i32 0
}
