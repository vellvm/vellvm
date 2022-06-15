;; XOR doubly linked list

%struct.node = type { i32, %struct.node* }

@head = common global %struct.node* null, align 8
@tail = common global %struct.node* null, align 8
; Function Attrs: noinline nounwind optnone ssp uwtable
define %struct.node* @xor(%struct.node* %0, %struct.node* %1) #0 {
  %3 = alloca %struct.node*, align 8
  %4 = alloca %struct.node*, align 8
  store %struct.node* %0, %struct.node** %3, align 8
  store %struct.node* %1, %struct.node** %4, align 8
  %5 = load %struct.node*, %struct.node** %3, align 8
  %6 = ptrtoint %struct.node* %5 to i64
  %7 = load %struct.node*, %struct.node** %4, align 8
  %8 = ptrtoint %struct.node* %7 to i64
  %9 = xor i64 %6, %8
  %10 = inttoptr i64 %9 to %struct.node*
  ret %struct.node* %10
}
; Function Attrs: noinline nounwind optnone ssp uwtable
define void @insert(i32 %0, i8 %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i8, align 1
  %5 = alloca %struct.node*, align 8
  store i32 %0, i32* %3, align 4
  %6 = add i8 %1, 0
  store i8 %6, i8* %4, align 1
  %7 = call i8* @malloc(i64 16) #4
  ;; %7 = alloca %struct.node
  %8 = bitcast i8* %7 to %struct.node*
  store %struct.node* %8, %struct.node** %5, align 8
  %9 = load i32, i32* %3, align 4
  %10 = load %struct.node*, %struct.node** %5, align 8
  %11 = getelementptr inbounds %struct.node, %struct.node* %10, i32 0, i32 0
  store i32 %9, i32* %11, align 8
  %12 = load %struct.node*, %struct.node** @head, align 8
  %13 = icmp eq %struct.node* null, %12
  br i1 %13, label %14, label %18

14:                                               ; preds = %2
  %15 = load %struct.node*, %struct.node** %5, align 8
  %16 = getelementptr inbounds %struct.node, %struct.node* %15, i32 0, i32 1
  store %struct.node* null, %struct.node** %16, align 8
  %17 = load %struct.node*, %struct.node** %5, align 8
  store %struct.node* %17, %struct.node** @tail, align 8
  store %struct.node* %17, %struct.node** @head, align 8
  br label %50

18:                                               ; preds = %2
  %19 = load i8, i8* %4, align 1
  %20 = trunc i8 %19 to i1
  br i1 %20, label %21, label %35

21:                                               ; preds = %18
  %22 = load %struct.node*, %struct.node** @tail, align 8
  %23 = call %struct.node* @xor(%struct.node* %22, %struct.node* null)
  %24 = load %struct.node*, %struct.node** %5, align 8
  %25 = getelementptr inbounds %struct.node, %struct.node* %24, i32 0, i32 1
  store %struct.node* %23, %struct.node** %25, align 8
  %26 = load %struct.node*, %struct.node** %5, align 8
  %27 = load %struct.node*, %struct.node** @tail, align 8
  %28 = getelementptr inbounds %struct.node, %struct.node* %27, i32 0, i32 1
  %29 = load %struct.node*, %struct.node** %28, align 8
  %30 = call %struct.node* @xor(%struct.node* %29, %struct.node* null)
  %31 = call %struct.node* @xor(%struct.node* %26, %struct.node* %30)
  %32 = load %struct.node*, %struct.node** @tail, align 8
  %33 = getelementptr inbounds %struct.node, %struct.node* %32, i32 0, i32 1
  store %struct.node* %31, %struct.node** %33, align 8
  %34 = load %struct.node*, %struct.node** %5, align 8
  store %struct.node* %34, %struct.node** @tail, align 8
  br label %49

35:                                               ; preds = %18
  %36 = load %struct.node*, %struct.node** @head, align 8
  %37 = call %struct.node* @xor(%struct.node* null, %struct.node* %36)
  %38 = load %struct.node*, %struct.node** %5, align 8
  %39 = getelementptr inbounds %struct.node, %struct.node* %38, i32 0, i32 1
  store %struct.node* %37, %struct.node** %39, align 8
  %40 = load %struct.node*, %struct.node** %5, align 8
  %41 = load %struct.node*, %struct.node** @head, align 8
  %42 = getelementptr inbounds %struct.node, %struct.node* %41, i32 0, i32 1
  %43 = load %struct.node*, %struct.node** %42, align 8
  %44 = call %struct.node* @xor(%struct.node* null, %struct.node* %43)
  %45 = call %struct.node* @xor(%struct.node* %40, %struct.node* %44)
  %46 = load %struct.node*, %struct.node** @head, align 8
  %47 = getelementptr inbounds %struct.node, %struct.node* %46, i32 0, i32 1
  store %struct.node* %45, %struct.node** %47, align 8
  %48 = load %struct.node*, %struct.node** %5, align 8
  store %struct.node* %48, %struct.node** @head, align 8
  br label %49

49:                                               ; preds = %35, %21
  br label %50

50:                                               ; preds = %49, %14
  ret void
}
; Function Attrs: allocsize(0)
declare i8* @malloc(i64) #1
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @delete(i8 %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i8, align 1
  %4 = alloca %struct.node*, align 8
  %5 = alloca i32, align 4
  %6 = alloca %struct.node*, align 8
  %7 = alloca %struct.node*, align 8
  %8 = alloca i32, align 4
  %9 = alloca %struct.node*, align 8
  %10 = add i8 %0, 0
  store i8 %10, i8* %3, align 1
  %11 = load %struct.node*, %struct.node** @head, align 8
  %12 = icmp eq %struct.node* null, %11
  br i1 %12, label %13, label %14

13:                                               ; preds = %1
  call void @exit(i32 1) #5
  unreachable

14:                                               ; preds = %1
  %15 = load i8, i8* %3, align 1
  %16 = trunc i8 %15 to i1
  br i1 %16, label %17, label %43

17:                                               ; preds = %14
  %18 = load %struct.node*, %struct.node** @tail, align 8
  store %struct.node* %18, %struct.node** %4, align 8
  %19 = load %struct.node*, %struct.node** %4, align 8
  %20 = getelementptr inbounds %struct.node, %struct.node* %19, i32 0, i32 0
  %21 = load i32, i32* %20, align 8
  store i32 %21, i32* %5, align 4
  %22 = load %struct.node*, %struct.node** %4, align 8
  %23 = getelementptr inbounds %struct.node, %struct.node* %22, i32 0, i32 1
  %24 = load %struct.node*, %struct.node** %23, align 8
  %25 = call %struct.node* @xor(%struct.node* %24, %struct.node* null)
  store %struct.node* %25, %struct.node** %6, align 8
  %26 = load %struct.node*, %struct.node** %6, align 8
  %27 = icmp eq %struct.node* null, %26
  br i1 %27, label %28, label %29

28:                                               ; preds = %17
  store %struct.node* null, %struct.node** @head, align 8
  br label %38

29:                                               ; preds = %17
  %30 = load %struct.node*, %struct.node** %4, align 8
  %31 = load %struct.node*, %struct.node** %6, align 8
  %32 = getelementptr inbounds %struct.node, %struct.node* %31, i32 0, i32 1
  %33 = load %struct.node*, %struct.node** %32, align 8
  %34 = call %struct.node* @xor(%struct.node* %33, %struct.node* null)
  %35 = call %struct.node* @xor(%struct.node* %30, %struct.node* %34)
  %36 = load %struct.node*, %struct.node** %6, align 8
  %37 = getelementptr inbounds %struct.node, %struct.node* %36, i32 0, i32 1
  store %struct.node* %35, %struct.node** %37, align 8
  br label %38

38:                                               ; preds = %29, %28
  %39 = load %struct.node*, %struct.node** %6, align 8
  store %struct.node* %39, %struct.node** @tail, align 8
  %40 = load %struct.node*, %struct.node** %4, align 8
  %41 = bitcast %struct.node* %40 to i8*
  call void @free(i8* %41)
  store %struct.node* null, %struct.node** %4, align 8
  %42 = load i32, i32* %5, align 4
  store i32 %42, i32* %2, align 4
  br label %69

43:                                               ; preds = %14
  %44 = load %struct.node*, %struct.node** @head, align 8
  store %struct.node* %44, %struct.node** %7, align 8
  %45 = load %struct.node*, %struct.node** %7, align 8
  %46 = getelementptr inbounds %struct.node, %struct.node* %45, i32 0, i32 0
  %47 = load i32, i32* %46, align 8
  store i32 %47, i32* %8, align 4
  %48 = load %struct.node*, %struct.node** %7, align 8
  %49 = getelementptr inbounds %struct.node, %struct.node* %48, i32 0, i32 1
  %50 = load %struct.node*, %struct.node** %49, align 8
  %51 = call %struct.node* @xor(%struct.node* null, %struct.node* %50)
  store %struct.node* %51, %struct.node** %9, align 8
  %52 = load %struct.node*, %struct.node** %9, align 8
  %53 = icmp eq %struct.node* null, %52
  br i1 %53, label %54, label %55

54:                                               ; preds = %43
  store %struct.node* null, %struct.node** @tail, align 8
  br label %64

55:                                               ; preds = %43
  %56 = load %struct.node*, %struct.node** %7, align 8
  %57 = load %struct.node*, %struct.node** %9, align 8
  %58 = getelementptr inbounds %struct.node, %struct.node* %57, i32 0, i32 1
  %59 = load %struct.node*, %struct.node** %58, align 8
  %60 = call %struct.node* @xor(%struct.node* null, %struct.node* %59)
  %61 = call %struct.node* @xor(%struct.node* %56, %struct.node* %60)
  %62 = load %struct.node*, %struct.node** %9, align 8
  %63 = getelementptr inbounds %struct.node, %struct.node* %62, i32 0, i32 1
  store %struct.node* %61, %struct.node** %63, align 8
  br label %64

64:                                               ; preds = %55, %54
  %65 = load %struct.node*, %struct.node** %9, align 8
  store %struct.node* %65, %struct.node** @head, align 8
  %66 = load %struct.node*, %struct.node** %7, align 8
  %67 = bitcast %struct.node* %66 to i8*
  call void @free(i8* %67)
  store %struct.node* null, %struct.node** %7, align 8
  %68 = load i32, i32* %8, align 4
  store i32 %68, i32* %2, align 4
  br label %69

69:                                               ; preds = %64, %38
  %70 = load i32, i32* %2, align 4
  ret i32 %70
}
; Function Attrs: noreturn
declare void @exit(i32) #2
declare void @free(i8*) #3

;; mimic this, check that returned values are 8, 7, 6, 1, 2, 3
; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @list() #0 {
  %array = alloca [6 x i32]
  store [6 x i32] [i32 8, i32 7, i32 6, i32 1, i32 2, i32 3], [6 x i32]* %array
  %1 = alloca %struct.node*, align 8 ;; curr
  %2 = alloca %struct.node*, align 8 ;; prev
  %3 = alloca %struct.node*, align 8 ;; next
  %countPtr = alloca i32
  store i32 0, i32* %countPtr
  %4 = load %struct.node*, %struct.node** @head, align 8
  store %struct.node* %4, %struct.node** %1, align 8
  store %struct.node* null, %struct.node** %2, align 8
  br label %5

5:                                                ; preds = %8, %0
  %6 = load i32, i32* %countPtr
  %7 = icmp sle i32 %6, 4
  %correctValPtr = getelementptr [6 x i32], [6 x i32]* %array, i32 0, i32 %6
  %correctVal = load i32, i32* %correctValPtr
  %newCount = add i32 %6, 1
  store i32 %newCount, i32* %countPtr
  br i1 %7, label %8, label %16

8:                                                ; preds = %5
  %9 = load %struct.node*, %struct.node** %2, align 8
  %10 = load %struct.node*, %struct.node** %1, align 8
  %11 = getelementptr inbounds %struct.node, %struct.node* %10, i32 0, i32 1
  %12 = load %struct.node*, %struct.node** %11, align 8
  %13 = call %struct.node* @xor(%struct.node* %9, %struct.node* %12)
  store %struct.node* %13, %struct.node** %3, align 8 ;; next
  %14 = load %struct.node*, %struct.node** %1, align 8
  store %struct.node* %14, %struct.node** %2, align 8 ;; prev
  %15 = load %struct.node*, %struct.node** %3, align 8
  %storedValPtr = getelementptr %struct.node, %struct.node* %14, i32 0, i32 0
  %storedVal = load i32, i32* %storedValPtr
  %correctValCheck = icmp eq i32 %storedVal, %correctVal
  br i1 %correctValCheck, label %continue, label %fail
continue:
  store %struct.node* %15, %struct.node** %1, align 8 ;; curr
  br label %5
16:                                               ; preds = %5
  %17 = load %struct.node*, %struct.node** %2, align 8
  %18 = load %struct.node*, %struct.node** %1, align 8
  %19 = getelementptr inbounds %struct.node, %struct.node* %18, i32 0, i32 1
  %20 = load %struct.node*, %struct.node** %19, align 8
  %21 = call %struct.node* @xor(%struct.node* %17, %struct.node* %20)
  store %struct.node* %21, %struct.node** %3, align 8 ;; next
  %22 = load %struct.node*, %struct.node** %1, align 8
  store %struct.node* %22, %struct.node** %2, align 8 ;; prev
  %storedValPtr = getelementptr %struct.node, %struct.node* %22, i32 0, i32 0
  %storedVal = load i32, i32* %storedValPtr
  %correctValCheck = icmp eq i32 %storedVal, 3
  br i1 %correctValCheck, label %success, label %fail
success:
  ret i32 1
fail:
  ret i32 0
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 {
  %1 = add i32 0, 0
  %2 = alloca i8*
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 8
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32 0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  store i8** %2, i8*** %5, align 8
  store i32 1, i32* %6, align 4
  br label %8

8:                                                ; preds = %15, %2
  %9 = load i32, i32* %6, align 4
  %10 = icmp sle i32 %9, 10
  br i1 %10, label %11, label %18

11:                                               ; preds = %8
  %12 = load i32, i32* %6, align 4
  %13 = load i32, i32* %6, align 4
  %14 = icmp slt i32 %13, 6
  %sext14 = zext i1 %14 to i8
  call void @insert(i32 %12, i8 %sext14)
  br label %15

15:                                               ; preds = %11
  %16 = load i32, i32* %6, align 4
  %17 = add nsw i32 %16, 1
  store i32 %17, i32* %6, align 4
  br label %8

18:                                               ; preds = %8
  ;; call void @list()
  store i32 1, i32* %7, align 4
  br label %19

19:                                               ; preds = %26, %18
  %20 = load i32, i32* %7, align 4
  %21 = icmp sle i32 %20, 4
  br i1 %21, label %22, label %29

22:                                               ; preds = %19
  %23 = load i32, i32* %7, align 4
  %24 = icmp slt i32 %23, 3
  %zext24 = zext i1 %24 to i8
  %25 = call i32 @delete(i8 %zext24)
  br label %26

26:                                               ; preds = %22
  %27 = load i32, i32* %7, align 4
  %28 = add nsw i32 %27, 1
  store i32 %28, i32* %7, align 4
  br label %19

29:                                               ; preds = %19
  %list = call i32 @list()
  ret i32 %list
}

; ASSERT EQ: i32 1 = call i32 @main();

