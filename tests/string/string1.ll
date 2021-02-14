@str = global [14 x i8] c"Hello World!\0A\00"

@arr = global [14 x i8] [i8 72, i8 101, i8 108, i8 108, i8 111, i8 32,  i8 87,  i8 111, i8 114, i8 108, i8 100, i8 33,  i8 10,  i8 0]


define i8 @index(i32 %x) {
  %addr = getelementptr [14 x i8], [14 x i8]* @str, i32 0, i32 %x
  %char = load i8, i8* %addr
  ret i8 %char
}

; ASSERT EQ: i8 72  = call i8 @index(i32 0)
; ASSERT EQ: i8 101 = call i8 @index(i32 1)
; ASSERT EQ: i8 108 = call i8 @index(i32 2)
; ASSERT EQ: i8 108 = call i8 @index(i32 3)
; ASSERT EQ: i8 111 = call i8 @index(i32 4)
; ASSERT EQ: i8 32  = call i8 @index(i32 5)
; ASSERT EQ: i8 87  = call i8 @index(i32 6)
; ASSERT EQ: i8 111 = call i8 @index(i32 7)
; ASSERT EQ: i8 114 = call i8 @index(i32 8)
; ASSERT EQ: i8 108 = call i8 @index(i32 9)
; ASSERT EQ: i8 100 = call i8 @index(i32 10)
; ASSERT EQ: i8 33  = call i8 @index(i32 11)
; ASSERT EQ: i8 10  = call i8 @index(i32 12)
; ASSERT EQ: i8 0   = call i8 @index(i32 13)

