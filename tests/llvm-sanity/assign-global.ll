define i64 @main(i64 %argc, i8** %arcv) {
  @global = icmp eq i64 2, %argc
  %1 = icmp eq i64 3, %argc
  %z = select i1 %1 , i64 100, i64 200
  ret i64 %z
}
