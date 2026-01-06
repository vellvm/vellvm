define i8 @splat_test() {
  %q = alloca <16 x i8>
  store <16 x i8> splat (i8 255), ptr %q
  %m = load <16 x i8>, ptr %q
  %bits = lshr <16 x i8> %m, splat (i8 7)
  %ans = extractelement <16 x i8> %bits, i32 0
  ret i8 %ans
}

; ASSERT EQ: i8 1 = call i8 @splat_test()
