@str = global [7 x i8] c"\n\03\XY\17"

define i8 @index(i32 %x) {
  %addr = getelementptr [7 x i8], [7 x i8]* @str, i32 0, i32 %x
  %char = load i8, i8* %addr
  ret i8 %char
}

; ASSERT EQ: i8 92  = call i8 @index(i32 0)
; ASSERT EQ: i8 110 = call i8 @index(i32 1)
; ASSERT EQ: i8 3   = call i8 @index(i32 2)
; ASSERT EQ: i8 92  = call i8 @index(i32 3)
; ASSERT EQ: i8 88  = call i8 @index(i32 4)
; ASSERT EQ: i8 89  = call i8 @index(i32 5)
; ASSERT EQ: i8 23  = call i8 @index(i32 6)
