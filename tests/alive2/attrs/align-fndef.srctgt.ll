define void @src(i8* align(4) %p) {
  load i8, i8* %p
  ret void
}

define void @tgt(i8* align(4) %p) {
  load i8, i8* %p, align 4
  ret void
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
