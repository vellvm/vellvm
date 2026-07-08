; ASSERT EQ: float 0x3a80000000000000 = call float @make_float1()
define float @make_float1() {
  ret float 0x3a80000000000000
}

define float @make_float2() {
  ret float 0x39638e3900000000
}   

; ASSERT EQ: float 0.0009765625 = call float @frac()
define float @frac() {
  %frac = fdiv float 1.0, 1024.0
  ret float %frac
}

; ASSERT EQ: float 0.00021701389050576836 = call float @main()
define float @main() {
  %frac = call float @frac()
  %ret = fmul float %frac, 0x3FCC71C720000000 ; = 0x3e638e39
  ret float %ret
}
