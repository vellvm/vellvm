@format = global [49 x i8] c"Hello, world!%s %s %lld %lld %lld %lld %lld %lld\00"
@text = global [5 x i8] c"2020\00"
@integer = global i64 4

define void @changetext() {
  %1 = load i64, i64* @integer
  %2 = sub i64 %1, 1
  store i64 %2, i64* @integer
  ret void
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = getelementptr [49 x i8], [49 x i8]* @format, i32 0, i32 0
  %2 = getelementptr i8*, i8** %argv, i32 1
  %3 = load i8*, i8** %2
  %4 = getelementptr [5 x i8], [5 x i8]* @text, i32 0, i32 0
  call void @changetext() 
  %5 = load i64, i64* @integer
  call void @printf(i8* %1, i8* %3, i8* %4, i64 %5, i64 4, i64 5, i64 6, i64 7, i64 8)
  ret i64 0
}