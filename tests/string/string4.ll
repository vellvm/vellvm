@str = global [1 x i8] c"\\"

define i8 @index(i32 %x) {
  %addr = getelementptr [1 x i8], [1 x i8]* @str, i32 0, i32 %x
  %char = load i8, i8* %addr
  ret i8 %char
}

; ASSERT EQ: i8 92  = call i8 @index(i32 0)
