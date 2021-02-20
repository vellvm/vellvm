define i64 @main(i64 %argc, i8** %arcv) {

  ; Emulate a conditional br instruction
  %value = i1 1
  %Val = zext i1          %value to i32
  switch i32 %Val, label %truedest [ i32 0, label %falsedest ]

falsedest:
  ret i64 0

truedest:
  ret i64 1

}
