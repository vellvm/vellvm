define void @foo() {
  %p = alloca i64
  %r = load i64, ptr %p, align 8, !foo !1, !align !1, !nontemporal !2
  %s = load volatile i64, ptr %p, !invariant.load !3, !noundef !3
  %self19.i.i.i.i.i.i = load i64, ptr %12, align 8, !alias.scope !9, !noalias !15, !nonnull !4
  %x = load atomic i64, ptr %s monotonic, align 8
  %x1 = load i64, ptr %p acquire, align 8
  %x2 = load i64, ptr %x1 seq_cst, align 8
  ret void
}

!1 = !{}
!2 = !{i32 0}
!3 = !{}
