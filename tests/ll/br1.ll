define i64 @main(i64 %argc, i8** %arcv) {
  br label %end

end:
  ret i64 9
}

; ASSERT EQ: i64 9 = call i64 @main(i64 0, i8** null)
