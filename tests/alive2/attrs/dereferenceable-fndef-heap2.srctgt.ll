define dereferenceable(4) i8* @src() {
  %p = call i8* @malloc(i64 4)
  call void @free(i8* %p)
  ret i8* %p
}

define dereferenceable(4) i8* @tgt() {
  unreachable
}

declare i8* @malloc(i64)
declare void @free(i8*)

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
