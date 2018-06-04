@gstr = global [14 x i8] c"hello, world!\00"
@gint = global i64 42
@v1 = global { i64, i64* } { i64 0, i64* @gint }
@v2 = global { i64, i8** } { i64 1, i8** null }

define i64 @main(i32 %argc, i8** %argv) {
  %p0 = alloca i64
  %p1 = getelementptr { i64, i8** }, { i64, i8** }* @v2, i32 0, i32 0
  store i64 5, i64* %p1
  %vb = bitcast { i64, i8** }* @v2 to { i64, i8* }*
  call void @foo({ i64, i8* }* %vb)
  %n1 = load i64, i64* %p1
  ret i64 %n1
}

define void @foo({ i64, i8* }* %pu) {
  %p1 = getelementptr { i64, i8* }, { i64, i8* }* %pu, i32 0, i32 0
  store i64 6, i64* %p1
  %n1 = load i64, i64* %p1
  ret void
}
