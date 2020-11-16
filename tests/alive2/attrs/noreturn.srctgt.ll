declare void @f() noreturn

define void @src() {
  call void @f()
  call void @f()
  ret void
}

define void @tgt() {
  call void @f()
  unreachable
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
