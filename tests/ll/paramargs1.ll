%struct.ether_addr = type {i32}


define fastcc void @foo(i8* nocapture %name, i8* nocapture %domain, i8** nocapture %s, i64 %call, i64 %call1) nounwind uwtable {
  ret void
}

; Function Attrs: nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #1

define void @foo1(%struct.ether_addr* nocapture readonly %ether_src, %struct.ether_addr* nocapture readonly %ether_dst) #0 {
  %addr = alloca i8
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %addr, i8* %addr, i64 6, i32 1, i1 false), !tbaa.struct !1
  ret void
}

!1 = !{}
