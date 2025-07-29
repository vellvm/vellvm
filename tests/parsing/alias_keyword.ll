@g = global i32 21
@g_alias = alias i32, i32* @g

define i32 @foo() {
  %x = load i32, i32* @g
  %y = load i32, i32* @g_alias
  %ans = add i32 %x, %y
  ret i32 %ans
}

; ASSERT EQ: i32 42 = call i32 @foo()
