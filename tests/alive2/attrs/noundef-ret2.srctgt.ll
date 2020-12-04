define noundef i32 @src() {
  ret i32 0
}

define noundef i32 @tgt() {
  unreachable
}

; ERROR: Source is more defined than target

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
