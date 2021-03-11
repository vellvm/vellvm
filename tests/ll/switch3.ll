define i64 @main(i64 %argc, i8** %arcv) {

  ; Implement a jump table:
  switch i32 2, label %otherwise [ i32 0, label %onzero
                                      i32 1, label %onone
                                      i32 2, label %ontwo ]

onzero:
  unreachable

onone:
  unreachable

ontwo:
  ret i64 0

otherwise:
  ret i64 1
}
