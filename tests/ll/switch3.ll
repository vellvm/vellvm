define i64 @main(i64 %argc, i8** %arcv) {

  %val = 132 2
  ; Implement a jump table:
  switch i32 %val, label %otherwise [ i32 0, label %onzero
                                      i32 1, label %onone
                                      i32 2, label %ontwo ]

onone:
  unreachable

ontwo:
  unreachable

onthree:
  ret i64 0

}
