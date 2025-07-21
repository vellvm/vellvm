; Function Attrs: mustprogress nofree norecurse nosync nounwind sspstrong willreturn memory(none) uwtable
define {i32, i1} @llvm.umul.with.overflow.i32(i32 noundef %0, i32 noundef %1) local_unnamed_addr {
  %3 = mul i32 %1, %0
  %4 = icmp ult i32 %3, %0
  %5 = icmp ult i32 %3, %1
  %overflow = and i1 %4, %5
  %base = insertvalue {i32, i1} {i32 0, i1 0}, i32 %3, 0
  %fullres = insertvalue {i32, i1} %base, i1 %overflow, 1
  ret {i32, i1} %fullres
}
