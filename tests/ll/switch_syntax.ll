define i32 @foo(i32 %x) {
  switch i32 %x, label %default [ i32 0, label %zero
                                  i32 u0x00000001, label %one
				  i32 17, label %seventeen
				  i32 s0x1111111111111111, label %negative_one
                                  i32 42, label %argmem
                                ]

zero:
  ret i32 u0x1

default:
  ret i32 %x

argmem:
  ret i32 43

one:
  ret i32 2

seventeen: 
  ret i32 18

negative_one:
  ret i32 -2
}

; ASSERT EQ: i32 1 = call i32 @foo(i32 0)
; ASSERT EQ: i32 2 = call i32 @foo(i32 1)
; ASSERT EQ: i32 18 = call i32 @foo(i32 17)
; ASSERT EQ: i32 -1 = call i32 @foo(i32 -1)
; ASSERT EQ: i32 43 = call i32 @foo(i32 42)
