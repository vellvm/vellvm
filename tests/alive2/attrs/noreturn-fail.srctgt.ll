declare void @f() noreturn

define void @src() {
  call void @f()
  ret void
}

define void @tgt() {
  unreachable
}

; ERROR: Source is more defined than target

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
