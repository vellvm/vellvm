declare void @f() noreturn
declare void @g() noreturn

define void @src() {
  call void @f()
  ret void
}

define void @tgt() {
  call void @g()
  ret void
}

; ERROR: Source is more defined than target

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
