define i64 @main(i64 %argc, i8** %arcv) {

  ; Emulate an unconditional br instruction
  switch i32 0, label %dest [ ]

dest:
  ret i64 0

}
