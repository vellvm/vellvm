; ASSERT EQ: double 3.125000e+00 = call double @f()

define double @f() {
  %ans = fpext float 3.125 to double         ; yields double:3.125000e+00
  ret double %ans
}   
