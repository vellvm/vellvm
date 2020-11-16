define noundef i32 @src() {
  %a = add nsw i32 2147483647, 1
  ret i32 %a
}

define noundef i32 @tgt() {
  unreachable
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
