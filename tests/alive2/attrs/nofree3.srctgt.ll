define void @src() nofree {
  call void @fn()
  ret void
}

define void @tgt() nofree {
  unreachable
}

; ERROR: Source is more defined than target

declare void @fn() nofree

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
