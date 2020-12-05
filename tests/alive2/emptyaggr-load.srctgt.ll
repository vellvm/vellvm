; SKIP-IDENTITY

define {} @src({}* %p, {}* %q) {
  %v = load {}, {}* %p
  %w = load {}, {}* %q
  ret {} %v
}

define {} @tgt({}* %p, {}* %q) {
  %v = load {}, {}* %p
  %w = load {}, {}* %q
  ret {} %w
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
