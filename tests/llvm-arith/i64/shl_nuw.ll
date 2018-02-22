define i64 @main(i64 %argc, i8** %arcv) {
  %1 = shl nuw i64 8, 63
  ret i64 %1
}

