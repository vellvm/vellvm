%disju = type { i64, i8* }
%var1 = type { i64, i64* }
%var2 = type { i64, i8** }

@gstr = global [14 x i8] c"hello, world!\00"
@gint = global i64 42
@v1 = global %var1 { i64 0, i64* @gint }
@v2 = global %var2 { i64 1, i8** null }

define i64 @main(i32 %argc, i8** %argv) {
  %p0 = alloca i64
  %p1 = getelementptr %var2, %var2* @v2, i32 0, i32 0
  store i64 5, i64* %p1
  %vb = bitcast %var2* @v2 to %disju*
  call void @foo(%disju* %vb)
  %n1 = load i64, i64* %p1
  ret i64 %n1
}

define void @foo(%disju* %pu) {
  %p1 = getelementptr %disju, %disju* %pu, i32 0, i32 0
  store i64 6, i64* %p1
  %n1 = load i64, i64* %p1
  ret void
}
