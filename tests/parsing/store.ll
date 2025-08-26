define void @foo() {
  %dst = alloca i64
  store atomic i64 0, ptr %dst , align 8 
  store i64 0, ptr %dst release, align 8
  store i64 0, ptr %dst seq_cst, align 8
  ret void
}

!1 = !{}
!2 = !{i32 0}
!3 = !{}
