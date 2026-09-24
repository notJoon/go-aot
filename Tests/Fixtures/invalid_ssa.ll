define i32 @main() {
entry:
  br i1 true, label %defines, label %skips

defines:
  %value = add i32 1, 2
  br label %exit

skips:
  br label %exit

exit:
  ret i32 %value
}
