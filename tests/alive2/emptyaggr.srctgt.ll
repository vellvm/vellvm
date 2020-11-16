; SKIP-IDENTITY

define {} @src({} %v, {} %w) {
  ret {} %v
}

define {} @tgt({} %v, {} %w) {
  ret {} %w
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
