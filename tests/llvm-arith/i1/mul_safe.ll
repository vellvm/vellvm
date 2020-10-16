define i1 @main(i1 %argc, i8** %arcv) {
  %1 = mul nuw nsw i1 0, 1
  ret i1 %1
}

; ASSERT EQ: i1 0 = call i1 @main(i64 0, i8** null)

