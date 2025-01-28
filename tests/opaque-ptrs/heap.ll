%Node = type { ptr, ptr, i64 } 
 
@n6 = global %Node { ptr null, ptr null, i64 67 } 
@n5 = global %Node { ptr null, ptr null, i64 -42 } 
@n4 = global %Node { ptr null, ptr null, i64 12 } 
@n3 = global %Node { ptr null, ptr null, i64 1 } 
@n2 = global %Node { ptr @n5, ptr @n6, i64 -5 } 
@n1 = global %Node { ptr @n3, ptr @n4, i64 -9 } 
@root = global %Node { ptr @n1, ptr @n2, i64 15 } 
 
define void @swap(ptr %n1, ptr %n2) { 
  %n1l.p = getelementptr %Node, ptr %n1, i32 0, i32 0 
  %temp_l = load ptr, ptr %n1l.p 
  %n1r.p = getelementptr %Node, ptr %n1, i32 0, i32 1 
  %temp_r = load ptr, ptr %n1r.p 
  %n1v.p = getelementptr %Node, ptr %n1, i32 0, i32 2 
  %temp_v = load i64, ptr %n1v.p 
  %n2l.p = getelementptr %Node, ptr %n2, i32 0, i32 0 
  %t2_l = load ptr, ptr %n2l.p 
  store ptr %t2_l, ptr %n1l.p  
  %n2r.p = getelementptr %Node, ptr %n2, i32 0, i32 1 
  %t2_r = load ptr, ptr %n2r.p 
  store ptr %t2_r, ptr %n1r.p  
  %n2v.p = getelementptr %Node, ptr %n2, i32 0, i32 2 
  %t2_v = load i64, ptr %n2v.p 
  store i64 %t2_v, ptr %n1v.p  
  store ptr %temp_l, ptr %n2l.p  
  store ptr %temp_r, ptr %n2r.p  
  store i64 %temp_v, ptr %n2v.p  
  ret void 
} 
 
define void @heapify(ptr %0) { 
  %2 = alloca ptr 
  %3 = alloca ptr 
  %4 = alloca ptr 
  %5 = alloca ptr 
  store ptr %0, ptr %2 
  %6 = load ptr, ptr %2 
  %7 = getelementptr %Node, ptr %6, i32 0, i32 0 
  %8 = load ptr, ptr %7 
  store ptr %8, ptr %3 
  %9 = load ptr, ptr %2 
  %10 = getelementptr %Node, ptr %9, i32 0, i32 1 
  %11 = load ptr, ptr %10 
  store ptr %11, ptr %4 
  %12 = load ptr, ptr %2 
  store ptr %12, ptr %5 
  %13 = load ptr, ptr %3 
  %14 = icmp ne ptr %13, null
  %15 = alloca ptr
  br i1 %14, label %l15, label %l25 
l15:                                                
  %16 = load ptr, ptr %3 
  %17 = getelementptr %Node, ptr %16, i32 0, i32 2 
  %18 = load i64, ptr %17 
  %19 = load ptr, ptr %2 
  %20 = getelementptr %Node, ptr %19, i32 0, i32 2 
  %21 = load i64, ptr %20 
  %22 = icmp sgt i64 %18, %21
  %23 = alloca ptr
  br i1 %22, label %l23, label %l25 
l23:                                              
  %24 = load ptr, ptr %3
  %25 = alloca ptr
  store ptr %24, ptr %5 
  br label %l25 
l25:                                               
  %26 = load ptr, ptr %4 
  %27 = icmp ne ptr %26, null
  %28 = alloca ptr
  br i1 %27, label %l28, label %l38 
l28:                                                
  %29 = load ptr, ptr %4 
  %30 = getelementptr %Node, ptr %29, i32 0, i32 2 
  %31 = load i64, ptr %30 
  %32 = load ptr, ptr %2 
  %33 = getelementptr %Node, ptr %32, i32 0, i32 2 
  %34 = load i64, ptr %33 
  %35 = icmp sgt i64 %31, %34
  %36 = alloca ptr
  br i1 %35, label %l36, label %l38 
l36:                                                
  %37 = load ptr, ptr %4
  %38 = alloca ptr
  store ptr %37, ptr %5 
  br label %l38 
l38:                                               
  %39 = load ptr, ptr %5 
  %40 = load ptr, ptr %2 
  %41 = icmp ne ptr %39, %40
  %42 = alloca ptr
  br i1 %41, label %l42, label %l46 
l42:                                               
  %43 = load ptr, ptr %2 
  %44 = load ptr, ptr %5 
  call void @swap(ptr %43, ptr %44) 
  %45 = load ptr, ptr %2 
  call void @heapify(ptr %45) 
  br label %l46 
l46:                                               
  ret void 
} 
 
define void @heapify_total(ptr %0) { 
  %2 = alloca ptr 
  store ptr %0, ptr %2 
  %3 = load ptr, ptr %2 
  %4 = getelementptr %Node, ptr %3, i32 0, i32 0 
  %5 = load ptr, ptr %4 
  %6 = icmp eq ptr %5, null
  %7 = alloca ptr
  br i1 %6, label %l7, label %l13 
l7:                                                 
  %8 = load ptr, ptr %2 
  %9 = getelementptr %Node, ptr %8, i32 0, i32 1 
  %10 = load ptr, ptr %9 
  %11 = icmp eq ptr %10, null
  %12 = alloca ptr
  %13 = alloca ptr
  br i1 %11, label %l12, label %l13 
l12:                                                
  br label %l51 
l13:                                                
  %14 = load ptr, ptr %2 
  %15 = getelementptr %Node, ptr %14, i32 0, i32 0 
  %16 = load ptr, ptr %15 
  %17 = icmp ne ptr %16, null
  %18 = alloca ptr
  br i1 %17, label %l18, label %l31 
l18:                                               
  %19 = load ptr, ptr %2 
  %20 = getelementptr %Node, ptr %19, i32 0, i32 1 
  %21 = load ptr, ptr %20 
  %22 = icmp ne ptr %21, null
  %23 = alloca ptr
  br i1 %22, label %l23, label %l31 
l23:                                                
  %24 = load ptr, ptr %2 
  %25 = getelementptr %Node, ptr %24, i32 0, i32 0 
  %26 = load ptr, ptr %25 
  call void @heapify_total(ptr %26) 
  %27 = load ptr, ptr %2 
  %28 = getelementptr %Node, ptr %27, i32 0, i32 1 
  %29 = load ptr, ptr %28 
  call void @heapify_total(ptr %29) 
  %30 = load ptr, ptr %2
  %31 = alloca ptr
  call void @heapify(ptr %30) 
  br label %l51 
l31:                                                
  %32 = load ptr, ptr %2 
  %33 = getelementptr %Node, ptr %32, i32 0, i32 0 
  %34 = load ptr, ptr %33 
  %35 = icmp eq ptr %34, null
  %36 = alloca ptr
  br i1 %35, label %l36, label %l41 
l36:                                                
  %37 = load ptr, ptr %2 
  %38 = getelementptr %Node, ptr %37, i32 0, i32 1 
  %39 = load ptr, ptr %38 
  call void @heapify_total(ptr %39) 
  %40 = load ptr, ptr %2
  %41 = alloca ptr
  call void @heapify(ptr %40) 
  br label %l51 
l41:                                                
  %42 = load ptr, ptr %2 
  %43 = getelementptr %Node, ptr %42, i32 0, i32 1 
  %44 = load ptr, ptr %43 
  %45 = icmp eq ptr %44, null
  %46 = alloca ptr
  br i1 %45, label %l46, label %l51 
l46:                                                
  %47 = load ptr, ptr %2 
  %48 = getelementptr %Node, ptr %47, i32 0, i32 0 
  %49 = load ptr, ptr %48 
  call void @heapify_total(ptr %49) 
  %50 = load ptr, ptr %2 
  call void @heapify(ptr %50) 
  br label %l51 
l51:                                                
  ret void 
} 
 
define i64 @main() { 
  call void @heapify_total(ptr @root) 
  %max_val_ptr = getelementptr %Node, ptr @root, i32 0, i32 2 
  %max_val = load i64, ptr %max_val_ptr 
  ret i64 %max_val 
}

; ASSERT EQ: i64 67 = call i64 @main(i64 0, ptr null)