@value = global i1 0

define i64 @main(i64 %argc, i8** %arcv) {

  ; Emulate a conditional br instruction
  %Val = zext i1 %value to i32
  switch i32 %Val, label %truedest [ i32 0, label %falsedest ]

falsedest:
  ret i64 0

truedest:
  ret i64 1

}
