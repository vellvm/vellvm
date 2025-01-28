;; XOR doubly linked list

%struct.node = type { i32, ptr }

@head = common global ptr null, align 8
@tail = common global ptr null, align 8
; Function Attrs: noinline nounwind optnone ssp uwtable
define ptr @xor(ptr %0, ptr %1) #0 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
  store ptr %1, ptr %4, align 8
  %5 = load ptr, ptr %3, align 8
  %6 = ptrtoint ptr %5 to i64
  %7 = load ptr, ptr %4, align 8
  %8 = ptrtoint ptr %7 to i64
  %9 = xor i64 %6, %8
  %10 = inttoptr i64 %9 to ptr
  ret ptr %10
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define void @insert(i32 %0, i8 %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i8, align 1
  %5 = alloca ptr, align 8
  store i32 %0, ptr %3, align 4
  %6 = add i8 %1, 0
  store i8 %6, ptr %4, align 1
  %7 = call ptr @malloc(i64 16) #4
  ;; %7 = alloca %struct.node
  %8 = bitcast ptr %7 to ptr
  store ptr %8, ptr %5, align 8
  %9 = load i32, ptr %3, align 4
  %10 = load ptr, ptr %5, align 8
  %11 = getelementptr inbounds %struct.node, ptr %10, i32 0, i32 0
  store i32 %9, ptr %11, align 8
  %12 = load ptr, ptr @head, align 8
  %13 = icmp eq ptr null, %12
  br i1 %13, label %14, label %18

14:                                               ; preds = %2
  %15 = load ptr, ptr %5, align 8
  %16 = getelementptr inbounds %struct.node, ptr %15, i32 0, i32 1
  store ptr null, ptr %16, align 8
  %17 = load ptr, ptr %5, align 8
  store ptr %17, ptr @tail, align 8
  store ptr %17, ptr @head, align 8
  br label %50

18:                                               ; preds = %2
  %19 = load i8, ptr %4, align 1
  %20 = trunc i8 %19 to i1
  br i1 %20, label %21, label %35

21:                                               ; preds = %18
  %22 = load ptr, ptr @tail, align 8
  %23 = call ptr @xor(ptr %22, ptr null)
  %24 = load ptr, ptr %5, align 8
  %25 = getelementptr inbounds %struct.node, ptr %24, i32 0, i32 1
  store ptr %23, ptr %25, align 8
  %26 = load ptr, ptr %5, align 8
  %27 = load ptr, ptr @tail, align 8
  %28 = getelementptr inbounds %struct.node, ptr %27, i32 0, i32 1
  %29 = load ptr, ptr %28, align 8
  %30 = call ptr @xor(ptr %29, ptr null)
  %31 = call ptr @xor(ptr %26, ptr %30)
  %32 = load ptr, ptr @tail, align 8
  %33 = getelementptr inbounds %struct.node, ptr %32, i32 0, i32 1
  store ptr %31, ptr %33, align 8
  %34 = load ptr, ptr %5, align 8
  store ptr %34, ptr @tail, align 8
  br label %49

35:                                               ; preds = %18
  %36 = load ptr, ptr @head, align 8
  %37 = call ptr @xor(ptr null, ptr %36)
  %38 = load ptr, ptr %5, align 8
  %39 = getelementptr inbounds %struct.node, ptr %38, i32 0, i32 1
  store ptr %37, ptr %39, align 8
  %40 = load ptr, ptr %5, align 8
  %41 = load ptr, ptr @head, align 8
  %42 = getelementptr inbounds %struct.node, ptr %41, i32 0, i32 1
  %43 = load ptr, ptr %42, align 8
  %44 = call ptr @xor(ptr null, ptr %43)
  %45 = call ptr @xor(ptr %40, ptr %44)
  %46 = load ptr, ptr @head, align 8
  %47 = getelementptr inbounds %struct.node, ptr %46, i32 0, i32 1
  store ptr %45, ptr %47, align 8
  %48 = load ptr, ptr %5, align 8
  store ptr %48, ptr @head, align 8
  br label %49

49:                                               ; preds = %35, %21
  br label %50

50:                                               ; preds = %49, %14
  ret void
}
; Function Attrs: allocsize(0)
declare ptr @malloc(i64) #1
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @delete(i8 %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i8, align 1
  %4 = alloca ptr, align 8
  %5 = alloca i32, align 4
  %6 = alloca ptr, align 8
  %7 = alloca ptr, align 8
  %8 = alloca i32, align 4
  %9 = alloca ptr, align 8
  %10 = add i8 %0, 0
  store i8 %10, ptr %3, align 1
  %11 = load ptr, ptr @head, align 8
  %12 = icmp eq ptr null, %11
  br i1 %12, label %13, label %14

13:                                               ; preds = %1
  call void @exit(i32 1) #5
  unreachable

14:                                               ; preds = %1
  %15 = load i8, ptr %3, align 1
  %16 = trunc i8 %15 to i1
  br i1 %16, label %17, label %43

17:                                               ; preds = %14
  %18 = load ptr, ptr @tail, align 8
  store ptr %18, ptr %4, align 8
  %19 = load ptr, ptr %4, align 8
  %20 = getelementptr inbounds %struct.node, ptr %19, i32 0, i32 0
  %21 = load i32, ptr %20, align 8
  store i32 %21, ptr %5, align 4
  %22 = load ptr, ptr %4, align 8
  %23 = getelementptr inbounds %struct.node, ptr %22, i32 0, i32 1
  %24 = load ptr, ptr %23, align 8
  %25 = call ptr @xor(ptr %24, ptr null)
  store ptr %25, ptr %6, align 8
  %26 = load ptr, ptr %6, align 8
  %27 = icmp eq ptr null, %26
  br i1 %27, label %28, label %29

28:                                               ; preds = %17
  store ptr null, ptr @head, align 8
  br label %38

29:                                               ; preds = %17
  %30 = load ptr, ptr %4, align 8
  %31 = load ptr, ptr %6, align 8
  %32 = getelementptr inbounds %struct.node, ptr %31, i32 0, i32 1
  %33 = load ptr, ptr %32, align 8
  %34 = call ptr @xor(ptr %33, ptr null)
  %35 = call ptr @xor(ptr %30, ptr %34)
  %36 = load ptr, ptr %6, align 8
  %37 = getelementptr inbounds %struct.node, ptr %36, i32 0, i32 1
  store ptr %35, ptr %37, align 8
  br label %38

38:                                               ; preds = %29, %28
  %39 = load ptr, ptr %6, align 8
  store ptr %39, ptr @tail, align 8
  %40 = load ptr, ptr %4, align 8
  %41 = bitcast ptr %40 to ptr
  call void @free(ptr %41)
  store ptr null, ptr %4, align 8
  %42 = load i32, ptr %5, align 4
  store i32 %42, ptr %2, align 4
  br label %69

43:                                               ; preds = %14
  %44 = load ptr, ptr @head, align 8
  store ptr %44, ptr %7, align 8
  %45 = load ptr, ptr %7, align 8
  %46 = getelementptr inbounds %struct.node, ptr %45, i32 0, i32 0
  %47 = load i32, ptr %46, align 8
  store i32 %47, ptr %8, align 4
  %48 = load ptr, ptr %7, align 8
  %49 = getelementptr inbounds %struct.node, ptr %48, i32 0, i32 1
  %50 = load ptr, ptr %49, align 8
  %51 = call ptr @xor(ptr null, ptr %50)
  store ptr %51, ptr %9, align 8
  %52 = load ptr, ptr %9, align 8
  %53 = icmp eq ptr null, %52
  br i1 %53, label %54, label %55

54:                                               ; preds = %43
  store ptr null, ptr @tail, align 8
  br label %64

55:                                               ; preds = %43
  %56 = load ptr, ptr %7, align 8
  %57 = load ptr, ptr %9, align 8
  %58 = getelementptr inbounds %struct.node, ptr %57, i32 0, i32 1
  %59 = load ptr, ptr %58, align 8
  %60 = call ptr @xor(ptr null, ptr %59)
  %61 = call ptr @xor(ptr %56, ptr %60)
  %62 = load ptr, ptr %9, align 8
  %63 = getelementptr inbounds %struct.node, ptr %62, i32 0, i32 1
  store ptr %61, ptr %63, align 8
  br label %64

64:                                               ; preds = %55, %54
  %65 = load ptr, ptr %9, align 8
  store ptr %65, ptr @head, align 8
  %66 = load ptr, ptr %7, align 8
  %67 = bitcast ptr %66 to ptr
  call void @free(ptr %67)
  store ptr null, ptr %7, align 8
  %68 = load i32, ptr %8, align 4
  store i32 %68, ptr %2, align 4
  br label %69

69:                                               ; preds = %64, %38
  %70 = load i32, ptr %2, align 4
  ret i32 %70
}
; Function Attrs: noreturn
declare void @exit(i32) #2
declare void @free(ptr) #3

;; mimic this, check that returned values are 8, 7, 6, 1, 2, 3
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @list() #0 {
  %array = alloca [6 x i32]
  store [6 x i32] [i32 8, i32 7, i32 6, i32 1, i32 2, i32 3], ptr %array
  %1 = alloca ptr, align 8 ;; curr
  %2 = alloca ptr, align 8 ;; prev
  %3 = alloca ptr, align 8 ;; next
  %countPtr = alloca i32
  store i32 0, ptr %countPtr
  %4 = load ptr, ptr @head, align 8
  store ptr %4, ptr %1, align 8
  store ptr null, ptr %2, align 8
  br label %5

5:                                                ; preds = %8, %0
  %6 = load i32, ptr %countPtr
  %7 = icmp sle i32 %6, 4
  %correctValPtr = getelementptr [6 x i32], ptr %array, i32 0, i32 %6
  %correctVal = load i32, ptr %correctValPtr
  %newCount = add i32 %6, 1
  store i32 %newCount, ptr %countPtr
  br i1 %7, label %8, label %16

8:                                                ; preds = %5
  %9 = load ptr, ptr %2, align 8
  %10 = load ptr, ptr %1, align 8
  %11 = getelementptr inbounds %struct.node, ptr %10, i32 0, i32 1
  %12 = load ptr, ptr %11, align 8
  %13 = call ptr @xor(ptr %9, ptr %12)
  store ptr %13, ptr %3, align 8 ;; next
  %14 = load ptr, ptr %1, align 8
  store ptr %14, ptr %2, align 8 ;; prev
  %15 = load ptr, ptr %3, align 8
  %storedValPtr = getelementptr %struct.node, ptr %14, i32 0, i32 0
  %storedVal = load i32, ptr %storedValPtr
  %correctValCheck = icmp eq i32 %storedVal, %correctVal
  br i1 %correctValCheck, label %continue, label %fail
continue:
  store ptr %15, ptr %1, align 8 ;; curr
  br label %5
16:                                               ; preds = %5
  %17 = load ptr, ptr %2, align 8
  %18 = load ptr, ptr %1, align 8
  %19 = getelementptr inbounds %struct.node, ptr %18, i32 0, i32 1
  %20 = load ptr, ptr %19, align 8
  %21 = call ptr @xor(ptr %17, ptr %20)
  store ptr %21, ptr %3, align 8 ;; next
  %22 = load ptr, ptr %1, align 8
  store ptr %22, ptr %2, align 8 ;; prev
  %storedValPtr2 = getelementptr %struct.node, ptr %22, i32 0, i32 0
  %storedVal2 = load i32, ptr %storedValPtr2
  %correctValCheck2 = icmp eq i32 %storedVal2, 3
  br i1 %correctValCheck2, label %success, label %fail
success:
  ret i32 1
fail:
  ret i32 0
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 {
  %1 = add i32 0, 0
  %2 = alloca ptr
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca ptr, align 8
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32 0, ptr %3, align 4
  store i32 %1, ptr %4, align 4
  store ptr %2, ptr %5, align 8
  store i32 1, ptr %6, align 4
  br label %8

8:                                                ; preds = %15, %2
  %9 = load i32, ptr %6, align 4
  %10 = icmp sle i32 %9, 10
  br i1 %10, label %11, label %18

11:                                               ; preds = %8
  %12 = load i32, ptr %6, align 4
  %13 = load i32, ptr %6, align 4
  %14 = icmp slt i32 %13, 6
  %sext14 = zext i1 %14 to i8
  call void @insert(i32 %12, i8 %sext14)
  br label %15

15:                                               ; preds = %11
  %16 = load i32, ptr %6, align 4
  %17 = add nsw i32 %16, 1
  store i32 %17, ptr %6, align 4
  br label %8

18:                                               ; preds = %8
  ;; call void @list()
  store i32 1, ptr %7, align 4
  br label %19

19:                                               ; preds = %26, %18
  %20 = load i32, ptr %7, align 4
  %21 = icmp sle i32 %20, 4
  br i1 %21, label %22, label %29

22:                                               ; preds = %19
  %23 = load i32, ptr %7, align 4
  %24 = icmp slt i32 %23, 3
  %zext24 = zext i1 %24 to i8
  %25 = call i32 @delete(i8 %zext24)
  br label %26

26:                                               ; preds = %22
  %27 = load i32, ptr %7, align 4
  %28 = add nsw i32 %27, 1
  store i32 %28, ptr %7, align 4
  br label %19

29:                                               ; preds = %19
  %list = call i32 @list()
  ret i32 %list
}

; ASSERT EQ: i32 1 = call i32 @main();

