define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add i64 5, 9
  %2 = mul i64 3, 6
  %3 = sub i64 %2, %1
  ret i64 %2
}

; ASSERT EQ: i64 18 = call i64 @main(i64 0, i8** null)
