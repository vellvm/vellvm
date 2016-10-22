define i64 @baz(i64 %x1, i64 %x2, i64 %x3, i64 %x4, i64 %x5, i64 %x6, i64 %x7, i64 %x8) {
  %1 = add i64 %x1, %x2
  %2 = add i64 %1, %x3
  %3 = add i64 %2, %x4
  %4 = add i64 %3, %x5
  %5 = add i64 %4, %x6
  %6 = add i64 %5, %x7
  %7 = add i64 %6, %x8	  
  ret i64 %7
}


define i64 @bar(i64 %x1, i64 %x2, i64 %x3, i64 %x4, i64 %x5, i64 %x6, i64 %x7, i64 %x8) {
  %1 = add i64 %x1, %x2
  %2 = add i64 %1, %x3
  %3 = add i64 %2, %x4
  %4 = add i64 %3, %x5
  %tmp = call i64 @baz(i64 %1, i64 %2, i64 %3, i64 %4, i64 %x5, i64 %x6, i64 %x7, i64 %x8)
  %5 = add i64 %4, %x6
  %6 = add i64 %5, %x7
  %7 = add i64 %6, %x8
  %8 = add i64 %7, %tmp
  ret i64 %8
}

define i64 @foo(i64 %x) {
  %1 = call i64 @bar(i64 %x, i64 %x, i64 %x, i64 %x, i64 %x, i64 %x, i64 %x, i64 %x)
  ret i64 %1
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo(i64 1)
  ret i64 %1
}
