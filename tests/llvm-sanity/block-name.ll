define i64 @main(i64 %argc, i8** %arcv) {
0label:
  %0 = icmp eq i64 3, %argc
  %z = select i1 %0 , i64 100, i64 200
  ret i64 %z
}
