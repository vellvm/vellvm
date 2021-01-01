
define i1 @main() {
  %1 = xor i1 1, 1
  ret i1 %1
}

; ASSERT EQ: i1 0 = call i1 @main()

