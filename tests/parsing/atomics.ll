define void @foo() {
  %ptr = alloca i32
  %old = atomicrmw add ptr %ptr, i32 1 acquire
  ret void
}

!1 = !{}
!2 = !{i32 0}
!3 = !{}
