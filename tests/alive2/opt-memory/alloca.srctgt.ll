; TEST-ARGS: -dbg

define void @src() {
  %p = alloca i64
  ret void
}

define void @tgt() {
  %p = alloca i64
  ret void
}

; CHECK: max_alloc_size: 8

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
