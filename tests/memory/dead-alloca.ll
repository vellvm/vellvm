define i64 @foo() {
  %x = alloca i64
  %dead = alloca i64
  %y = alloca i64*
  store i64 17, i64* %x
  store i64* %x, i64** %y
  %u = load i64*, i64** %y
  %ans = load i64, i64* %u
  ret i64 %ans
}

define i64 @bar() {
  %x = alloca i64
  %y = alloca i64*
  store i64 17, i64* %x
  store i64* %x, i64** %y
  %u = load i64*, i64** %y
  %ans = load i64, i64* %u
  ret i64 %ans
}

; ASSERT EQ: i64 17 = call i64 @foo()
; ASSERT EQ: i64 17 = call i64 @bar()

