@valuesSeen = global [15 x i64] [i64 0, i64 0, i64 0, i64 0, i64 0,
                                i64 0, i64 0, i64 0, i64 0, i64 0,
                                i64 0, i64 0, i64 0, i64 0, i64 0 ]

@inputArray = global [10 x i64]  [i64 5, i64 7, i64 14, i64 0, i64 0,
                                 i64 9, i64 12, i64 5, i64 5, i64 6]

@outputArray = global [10 x i64]  [i64 0, i64 0, i64 0, i64 0, i64 0,
                                   i64 0, i64 0, i64 0, i64 0, i64 0]

define i64 @insert(i64 %val, i64 %numCopies, i64 %startIndex) {
    %endIndex = add i64 %startIndex, %numCopies
    %currentInsertionIndexPtr = alloca i64
    store i64 %startIndex, i64* %currentInsertionIndexPtr
    %c3 = icmp eq i64 %startIndex, %endIndex

    br i1 %c3, label %finishInsert, label %innerInsertLoop

    innerInsertLoop:
       %currentInsertionIndex = load i64, i64* %currentInsertionIndexPtr 

       %insertionPtr = getelementptr [10 x i64], [10 x i64]* @outputArray, i32 0, i64 %currentInsertionIndex
       store i64 %val, i64* %insertionPtr	

       %newCurrentInsertionIndex = add i64 %currentInsertionIndex, 1
       store i64 %newCurrentInsertionIndex, i64* %currentInsertionIndexPtr
       %c0 = icmp eq i64 %newCurrentInsertionIndex, %endIndex
       br i1 %c0, label %finishInsert, label %innerInsertLoop

    finishInsert:
       ret i64 %endIndex
}

define void @countSortInPlace() {
    %currentIndexPtr = alloca i64
    store i64 0, i64* %currentIndexPtr
    br label %countLoop

    ; create all the counts
    countLoop:
        ; load in the element at currentIndex
        %currentIndex = load i64, i64* %currentIndexPtr
        %currentElPtr = getelementptr [10 x i64], [10 x i64]* @inputArray, i32 0, i64 %currentIndex
        %currentEl = load i64, i64* %currentElPtr

        ; load in the count at currentIndex
        %countPtr = getelementptr [15 x i64], [15 x i64]* @valuesSeen, i32 0, i64 %currentEl
        %count = load i64, i64* %countPtr
        
        ; update the count and store it
        %newCount = add i64 %count, 1
        store i64 %newCount, i64* %countPtr
        
        ; Update the current index and store it
        %newCurrentIndex = add i64 %currentIndex, 1 
        store i64 %newCurrentIndex, i64* %currentIndexPtr

        ; If we've reached the end of the list, end the loop
	    %c1 = icmp eq i64 %newCurrentIndex, 10
        br i1 %c1, label %performInsertions, label %countLoop

    ; insert into the final array
    performInsertions:
        ; the index in the list of counts
        store i64 0, i64* %currentIndexPtr
        %insertionPointPtr = alloca i64
        ; the index in the output array
        store i64 0, i64* %insertionPointPtr
        br label %insertionLoop

    insertionLoop:
        %currentVal = load i64, i64* %currentIndexPtr
        
        %currentCountPtr = getelementptr [15 x i64], [15 x i64]* @valuesSeen, i32 0, i64 %currentVal	
        %currentCount = load i64, i64* %currentCountPtr
        
        %insertionPoint = load i64, i64* %insertionPointPtr
        %newInsertionPoint = call i64 @insert(i64 %currentVal, i64 %currentCount, i64 %insertionPoint)
        
        store i64 %newInsertionPoint, i64* %insertionPointPtr
        
        %newCurrentVal = add i64 %currentVal, 1
        store i64 %newCurrentVal, i64* %currentIndexPtr

        %c2 = icmp eq i64 %newCurrentVal, 15 
        br i1 %c2, label %complete, label %insertionLoop
	
    complete:
        ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  call void @countSortInPlace()
  %testPtr = getelementptr [10 x i64], [10 x i64]* @outputArray, i32 0, i64 5
  %res = load i64, i64* %testPtr
  ; should return 6
  ret i64 %res
}
