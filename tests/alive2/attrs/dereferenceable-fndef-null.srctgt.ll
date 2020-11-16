define dereferenceable(4) i32* @src(i32* %p) {
  ret i32* null
}

define dereferenceable(4) i32* @tgt(i32* %p) {
  unreachable
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
