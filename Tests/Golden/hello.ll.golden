@.str.0 = private unnamed_addr constant [14 x i8] c"Hello, world!\00"

declare i32 @fflush(ptr)
declare i64 @write(i32, ptr, i64)

define internal void @goaot.print_line(ptr %bytes, i64 %length) {
entry:
  %newline = alloca i8
  store i8 10, ptr %newline
  call i32 @fflush(ptr null)
  br label %loop

loop:
  %offset = phi i64 [ 0, %entry ], [ %next, %body ]
  %done = icmp eq i64 %offset, %length
  br i1 %done, label %exit, label %body

body:
  %address = getelementptr i8, ptr %bytes, i64 %offset
  %remaining = sub i64 %length, %offset
  %written = call i64 @write(i32 1, ptr %address, i64 %remaining)
  %next = add i64 %offset, %written
  %failed = icmp slt i64 %written, 1
  br i1 %failed, label %exit, label %loop

exit:
  call i64 @write(i32 1, ptr %newline, i64 1)
  ret void
}

define i32 @main() {
bb0:
  call void @goaot.print_line(ptr @.str.0, i64 13)
  ret i32 0
}
