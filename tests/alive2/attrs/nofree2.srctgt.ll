define void @src() nofree {
  call void @fn()
  ret void
}

define void @tgt() nofree {
  unreachable
}

declare void @fn()

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
