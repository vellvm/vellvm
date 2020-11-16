define void @src() noreturn {
  ret void
}

define void @tgt() noreturn {
  unreachable
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
