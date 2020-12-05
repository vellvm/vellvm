; Show that storing {} is a nop

define void @src(i8* noundef %p) {
  ret void
}

define void @tgt(i8* noundef %p) {
  %p2 = bitcast i8* %p to {}*
  store {} {}, {}* %p2
  ret void
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
