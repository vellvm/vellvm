@str = global [1 x i8] c"\22"

define i8 @index(i32 %x) {
  %addr = getelementptr [1 x i8], [1 x i8]* @str, i32 0, i32 %x
  %char = load i8, i8* %addr
  ret i8 %char
}

; ASSERT EQ: i8 34  = call i8 @index(i32 0)
