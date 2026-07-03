define <2 x i1> @get_it() {
  ret <2 x i1> <i1 1, i1 1>
}  

define i1 @get_i1() {
  ret i1 1
}  

; ASSERT EQ: i1 1 = call i1 @get_i1()
; ASSERT EQ: <2 x i1> <i1 1, i1 1> = call <2 x i1> @get_it()
