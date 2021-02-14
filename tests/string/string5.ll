@str = global [3 x i8] c"\1X"

define i8 @index(i32 %x) {
  %addr = getelementptr [3 x i8], [3 x i8]* @str, i32 0, i32 %x
  %char = load i8, i8* %addr
  ret i8 %char
}

; ASSERT EQ: i8 92  = call i8 @index(i32 0)
; ASSERT EQ: i8 49  = call i8 @index(i32 1)
; ASSERT EQ: i8 88  = call i8 @index(i32 2)
