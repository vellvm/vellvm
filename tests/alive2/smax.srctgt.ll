declare i8 @llvm.smax.i8(i8, i8)

define i8 @src(i8 %v0, i8 %v1) {
  %cmp = icmp sge i8 %v0, %v1
  %r = select i1 %cmp, i8 %v0, i8 %v1
  ret i8 %r
}

define i8 @tgt(i8 %v0, i8 %v1) {
  %r = call i8 @llvm.smax.i8(i8 %v0, i8 %v1)
  ret i8 %r
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
