@arr = global [5 x i64] [ i64 4, i64 2, i64 3, i64 10, i64 6 ]

define void @swap(i64 * %p1, i64 * %p2) {
  %temp1 = load i64, i64* %p1
  %temp2 = load i64,i64* %p2
  store i64 %temp2, i64* %p1
  store i64 %temp1, i64* %p2
  ret void
}

define i64 @getminidx(i64 %curr, i64 %indvar, i64 %arrsize){
  %1 = icmp eq i64 %indvar, %arrsize
  br i1 %1, label %fin, label %calc
fin:
  ret i64 0
calc:
  %curr_val_ptr = getelementptr [5 x i64], [5 x i64]* @arr, i64 0, i64 %curr
  %curr_val = load i64, i64* %curr_val_ptr 
  %cmp_val_ptr = getelementptr [5 x i64], [5 x i64]* @arr, i64 0, i64 %indvar
  %cmp_val = load i64, i64* %cmp_val_ptr
  %cmp_bool = icmp sgt i64 %curr_val, %cmp_val
  br i1 %cmp_bool, label %returnval, label %nextloop
returnval:
  ret i64 %indvar
nextloop:
  %nextindvar = add i64 %indvar, 1
  %res = call i64 @getminidx(i64 %curr, i64 %nextindvar, i64 %arrsize)
  ret i64 %res
}

define i64 @selectsort(i64 %curridx, i64 %acc, i64 %arrsize) {
  %1 = icmp eq i64 %curridx, %arrsize
  br i1 %1, label %donesorting, label %nextsort
donesorting:
  ret i64 %acc
nextsort:
  %indvar = add i64 %curridx, 1
  %minidx = call i64 @getminidx(i64 %curridx, i64 %indvar, i64 %arrsize)
  %idxcmp = icmp sgt i64 %minidx, 0
  br i1 %idxcmp, label %swappos, label %donothing
donothing:
  %currvalptr = getelementptr [5 x i64], [5 x i64]* @arr, i64 0, i64 %curridx
  %currval = load i64, i64* %currvalptr
  %newacc = add i64 %acc, %currval
  %nextidx = add i64 %curridx, 1
  %res = call i64 @selectsort(i64 %nextidx, i64 %newacc, i64 %arrsize)
  ret i64 %res
swappos:
  %currvalptr = getelementptr [5 x i64], [5 x i64]* @arr, i64 0, i64 %curridx
  %swapvalptr = getelementptr [5 x i64], [5 x i64]* @arr, i64 0, i64 %minidx
  %newval = load i64, i64* %swapvalptr
  %newacc = add i64 %acc, %newval
  call void @swap(i64 * %currvalptr, i64 * %swapvalptr)
  %nextidx1 = add i64 %curridx, 1
  %res1 = call i64 @selectsort(i64 %nextidx1, i64 %newacc, i64 %arrsize)
  ret i64 %res1
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @selectsort(i64 0, i64 0, i64 5)
  ret i64 %1
}