define <2 x i1> @fcmp_une(<2 x float> %v, <2 x float> %w) {
  %ans = fcmp une <2 x float> %v, %w
  ret <2 x i1> %ans
}

define <2 x i1> @get_it() {
  ret <2 x i1> <i1 1, i1 1>
}  

define i1 @get_i1() {
  ret i1 1
}  

; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @fcmp_une(<2 x float> <float 1.0, float 2.0>, <2 x float> <float 0.0, float 0.0>)

; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @get_it()

; ASSERT EQ: i1 1 = call i1 @get_i1()
