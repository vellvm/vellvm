%Node = type { %Node*, %Node*, i64 } 
 
@n6 = global %Node { %Node* null, %Node* null, i64 67 } 
@n5 = global %Node { %Node* null, %Node* null, i64 -42 } 
@n4 = global %Node { %Node* null, %Node* null, i64 12 } 
@n3 = global %Node { %Node* null, %Node* null, i64 1 } 
@n2 = global %Node { %Node* @n5, %Node* @n6, i64 -5 } 
@n1 = global %Node { %Node* @n3, %Node* @n4, i64 -9 } 
@root = global %Node { %Node* @n1, %Node* @n2, i64 15 } 
 
define void @swap(%Node* %n1, %Node* %n2) { 
  %n1l.p = getelementptr %Node, %Node* %n1, i32 0, i32 0 
  %temp_l = load %Node*, %Node** %n1l.p 
  %n1r.p = getelementptr %Node, %Node* %n1, i32 0, i32 1 
  %temp_r = load %Node*, %Node** %n1r.p 
  %n1v.p = getelementptr %Node, %Node* %n1, i32 0, i32 2 
  %temp_v = load i64, i64* %n1v.p 
  %n2l.p = getelementptr %Node, %Node* %n2, i32 0, i32 0 
  %t2_l = load %Node*, %Node** %n2l.p 
  store %Node* %t2_l, %Node** %n1l.p  
  %n2r.p = getelementptr %Node, %Node* %n2, i32 0, i32 1 
  %t2_r = load %Node*, %Node** %n2r.p 
  store %Node* %t2_r, %Node** %n1r.p  
  %n2v.p = getelementptr %Node, %Node* %n2, i32 0, i32 2 
  %t2_v = load i64, i64* %n2v.p 
  store i64 %t2_v, i64* %n1v.p  
  store %Node* %temp_l, %Node** %n2l.p  
  store %Node* %temp_r, %Node** %n2r.p  
  store i64 %temp_v, i64* %n2v.p  
  ret void 
} 
 
define void @heapify(%Node* %0) { 
  %2 = alloca %Node* 
  %3 = alloca %Node* 
  %4 = alloca %Node* 
  %5 = alloca %Node* 
  store %Node* %0, %Node** %2 
  %6 = load %Node*, %Node** %2 
  %7 = getelementptr %Node, %Node* %6, i32 0, i32 0 
  %8 = load %Node*, %Node** %7 
  store %Node* %8, %Node** %3 
  %9 = load %Node*, %Node** %2 
  %10 = getelementptr %Node, %Node* %9, i32 0, i32 1 
  %11 = load %Node*, %Node** %10 
  store %Node* %11, %Node** %4 
  %12 = load %Node*, %Node** %2 
  store %Node* %12, %Node** %5 
  %13 = load %Node*, %Node** %3 
  %14 = icmp ne %Node* %13, null 
  br i1 %14, label %l15, label %l25 
l15:                                                
  %16 = load %Node*, %Node** %3 
  %17 = getelementptr %Node, %Node* %16, i32 0, i32 2 
  %18 = load i64, i64* %17 
  %19 = load %Node*, %Node** %2 
  %20 = getelementptr %Node, %Node* %19, i32 0, i32 2 
  %21 = load i64, i64* %20 
  %22 = icmp sgt i64 %18, %21 
  br i1 %22, label %l23, label %l25 
l23:                                              
  %24 = load %Node*, %Node** %3 
  store %Node* %24, %Node** %5 
  br label %l25 
l25:                                               
  %26 = load %Node*, %Node** %4 
  %27 = icmp ne %Node* %26, null 
  br i1 %27, label %l28, label %l38 
l28:                                                
  %29 = load %Node*, %Node** %4 
  %30 = getelementptr %Node, %Node* %29, i32 0, i32 2 
  %31 = load i64, i64* %30 
  %32 = load %Node*, %Node** %2 
  %33 = getelementptr %Node, %Node* %32, i32 0, i32 2 
  %34 = load i64, i64* %33 
  %35 = icmp sgt i64 %31, %34 
  br i1 %35, label %l36, label %l38 
l36:                                                
  %37 = load %Node*, %Node** %4 
  store %Node* %37, %Node** %5 
  br label %l38 
l38:                                               
  %39 = load %Node*, %Node** %5 
  %40 = load %Node*, %Node** %2 
  %41 = icmp ne %Node* %39, %40 
  br i1 %41, label %l42, label %l46 
l42:                                               
  %43 = load %Node*, %Node** %2 
  %44 = load %Node*, %Node** %5 
  call void @swap(%Node* %43, %Node* %44) 
  %45 = load %Node*, %Node** %2 
  call void @heapify(%Node* %45) 
  br label %l46 
l46:                                               
  ret void 
} 
 
define void @heapify_total(%Node* %0) { 
  %2 = alloca %Node* 
  store %Node* %0, %Node** %2 
  %3 = load %Node*, %Node** %2 
  %4 = getelementptr %Node, %Node* %3, i32 0, i32 0 
  %5 = load %Node*, %Node** %4 
  %6 = icmp eq %Node* %5, null 
  br i1 %6, label %l7, label %l13 
l7:                                                 
  %8 = load %Node*, %Node** %2 
  %9 = getelementptr %Node, %Node* %8, i32 0, i32 1 
  %10 = load %Node*, %Node** %9 
  %11 = icmp eq %Node* %10, null 
  br i1 %11, label %l12, label %l13 
l12:                                                
  br label %l51 
l13:                                                
  %14 = load %Node*, %Node** %2 
  %15 = getelementptr %Node, %Node* %14, i32 0, i32 0 
  %16 = load %Node*, %Node** %15 
  %17 = icmp ne %Node* %16, null 
  br i1 %17, label %l18, label %l31 
l18:                                               
  %19 = load %Node*, %Node** %2 
  %20 = getelementptr %Node, %Node* %19, i32 0, i32 1 
  %21 = load %Node*, %Node** %20 
  %22 = icmp ne %Node* %21, null 
  br i1 %22, label %l23, label %l31 
l23:                                                
  %24 = load %Node*, %Node** %2 
  %25 = getelementptr %Node, %Node* %24, i32 0, i32 0 
  %26 = load %Node*, %Node** %25 
  call void @heapify_total(%Node* %26) 
  %27 = load %Node*, %Node** %2 
  %28 = getelementptr %Node, %Node* %27, i32 0, i32 1 
  %29 = load %Node*, %Node** %28 
  call void @heapify_total(%Node* %29) 
  %30 = load %Node*, %Node** %2 
  call void @heapify(%Node* %30) 
  br label %l51 
l31:                                                
  %32 = load %Node*, %Node** %2 
  %33 = getelementptr %Node, %Node* %32, i32 0, i32 0 
  %34 = load %Node*, %Node** %33 
  %35 = icmp eq %Node* %34, null 
  br i1 %35, label %l36, label %l41 
l36:                                                
  %37 = load %Node*, %Node** %2 
  %38 = getelementptr %Node, %Node* %37, i32 0, i32 1 
  %39 = load %Node*, %Node** %38 
  call void @heapify_total(%Node* %39) 
  %40 = load %Node*, %Node** %2 
  call void @heapify(%Node* %40) 
  br label %l51 
l41:                                                
  %42 = load %Node*, %Node** %2 
  %43 = getelementptr %Node, %Node* %42, i32 0, i32 1 
  %44 = load %Node*, %Node** %43 
  %45 = icmp eq %Node* %44, null 
  br i1 %45, label %l46, label %l51 
l46:                                                
  %47 = load %Node*, %Node** %2 
  %48 = getelementptr %Node, %Node* %47, i32 0, i32 0 
  %49 = load %Node*, %Node** %48 
  call void @heapify_total(%Node* %49) 
  %50 = load %Node*, %Node** %2 
  call void @heapify(%Node* %50) 
  br label %l51 
l51:                                                
  ret void 
} 
 
define i64 @main() { 
  call void @heapify_total(%Node* @root) 
  %max_val_ptr = getelementptr %Node, %Node* @root, i32 0, i32 2 
  %max_val = load i64, i64* %max_val_ptr 
  ret i64 %max_val 
}