%list = type [31 x i64]
@length = global i64 31

@input = global %list [i64 5, i64 100, i64 2, i64 0, i64 18, i64 10, i64 2, i64 1, i64 22, i64 98, i64 107, i64 105, i64 116, i64 116, i64 101, i64 110, i64 20, i64 23, i64 102, i64 23, i64 98, i64 97, i64 98, i64 121, i64 15, i64 5, i64 16, i64 116, i64 105, i64 110, i64 155]

define void @slowsort(i64 %i, i64 %j) {
  %1 = icmp sge i64 %i, %j
  br i1 %1, label %done, label %notdone
notdone:
  %2 = add i64 %i, %j
  %mid = ashr i64 %2, 1
  %mid1 = add i64 %mid, 1
  call void @slowsort(i64 %i, i64 %mid)
  call void @slowsort(i64 %mid1, i64 %j)
  %ptrm = getelementptr %list, %list* @input, i64 0, i64 %mid
  %valm = load i64, i64* %ptrm
  %ptrj = getelementptr %list, %list* @input, i64 0, i64 %j
  %valj = load i64, i64* %ptrj
  %isrev = icmp slt i64 %valj, %valm
  br i1 %isrev, label %swap, label %finish
swap:
  store i64 %valj, i64* %ptrm
  store i64 %valm, i64* %ptrj
  br label %finish
finish:
  %jminus = sub i64 %j, 1
  call void @slowsort(i64 %i, i64 %jminus)
  br label %done
done:
  ret void
}

define i1 @issorted() {
  %len = load i64, i64* @length
  %len1 = sub i64 %len, 1
  %iptr = alloca i64
  store i64 0, i64* %iptr
  br label %loop
loop:
  %i = load i64, i64* %iptr
  %ptri = getelementptr %list, %list* @input, i64 0, i64 %i
  %vali = load i64, i64* %ptri
  %j = add i64 %i, 1
  %ptrj = getelementptr %list, %list* @input, i64 0, i64 %j
  %valj = load i64, i64* %ptrj
  store i64 %j, i64* %iptr
  %inorder = icmp sle i64 %vali, %valj
  br i1 %inorder, label %checkloop, label %succ
checkloop:
  %isdone = icmp eq i64 %i, %len1
  br i1 %isdone, label %succ, label %loop
fail:
  ret i1 0
succ:
  ret i1 1
}

define i64 @main(i64 %argc, i8** %arcv) {
  %len = load i64, i64* @length
  %len1 = sub i64 %len, 1
  call void @slowsort(i64 0, i64 %len1)
  %test = call i1 @issorted()
  br i1 %test, label %succ, label %fail
fail:
  ret i64 0
succ:
  %p = getelementptr %list, %list* @input, i64 0, i64 %len1
  %big = load i64, i64* %p
  ret i64 %big
}