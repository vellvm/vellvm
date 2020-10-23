define i1 @main(i1 %argc, i8** %arcv) {
  %1 = add i1 0, 1
  %2 = mul i1 1, 1
  %3 = sub i1 %2, %1
  ret i1 %3
}

; ASSERT EQ: i1 0 = call i1 @main(i64 0, i8** null)

