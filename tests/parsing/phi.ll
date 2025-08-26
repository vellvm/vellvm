define i64 @foo() {
  %i = icmp eq i64 0, 2
  br i1 %i, label %then, label %else

then:
  br label %merge

else:
  br label %merge

merge:
  %ans = phi i64 [0, %then], [1, %else], !dbg !0
  ret i64 %ans
}

!0 = !{}
  
