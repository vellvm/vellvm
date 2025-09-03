define void @foo() {
  %ptr = alloca i32
  %old = atomicrmw add ptr %ptr, i32 1 acquire
  %new1 = atomicrmw sub ptr %ptr, i32 %old release, align 8
  %new2 = atomicrmw sub ptr %ptr, i32 %old acq_rel, align 8
  %new3 = atomicrmw sub ptr %ptr, i32 %old seq_cst, align 8
  %new4 = atomicrmw volatile xor ptr %ptr, i32 %old syncscope("target") seq_cst, align 8
  %val_success = cmpxchg ptr %ptr, i32 %new1, i32 %new2 acq_rel monotonic
  ret void
}

!1 = !{}
!2 = !{i32 0}
!3 = !{}
