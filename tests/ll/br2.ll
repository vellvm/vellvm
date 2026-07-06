define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add i64 5, 12
  br label %next

next:
  br label %end

end:
  ret i64 %1
}

; ASSERT EQ: i64 17 = call i64 @main(i64 0, i8** null)
