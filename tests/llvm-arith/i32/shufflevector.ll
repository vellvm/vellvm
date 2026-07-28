; Examples from the LLVM LangRef's shufflevector section.

define <4 x i32> @interleave(<4 x i32> %v1, <4 x i32> %v2) {
  %r = shufflevector <4 x i32> %v1, <4 x i32> %v2,
                      <4 x i32> <i32 0, i32 4, i32 1, i32 5>
  ret <4 x i32> %r
}

define <4 x i32> @identity(<4 x i32> %v1) {
  %r = shufflevector <4 x i32> %v1, <4 x i32> poison,
                      <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  ret <4 x i32> %r
}

define <4 x i32> @narrow(<8 x i32> %v1) {
  %r = shufflevector <8 x i32> %v1, <8 x i32> poison,
                      <4 x i32> <i32 0, i32 1, i32 2, i32 3>
  ret <4 x i32> %r
}

define <8 x i32> @widen(<4 x i32> %v1, <4 x i32> %v2) {
  %r = shufflevector <4 x i32> %v1, <4 x i32> %v2,
                      <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7>
  ret <8 x i32> %r
}

; ASSERT EQ: <4 x i32> <i32 10, i32 100, i32 20, i32 200> = call <4 x i32> @interleave(<4 x i32> <i32 10, i32 20, i32 30, i32 40>, <4 x i32> <i32 100, i32 200, i32 300, i32 400>)
; ASSERT EQ: <4 x i32> <i32 10, i32 20, i32 30, i32 40> = call <4 x i32> @identity(<4 x i32> <i32 10, i32 20, i32 30, i32 40>)
; ASSERT EQ: <4 x i32> <i32 1, i32 2, i32 3, i32 4> = call <4 x i32> @narrow(<8 x i32> <i32 1, i32 2, i32 3, i32 4, i32 5, i32 6, i32 7, i32 8>)
; ASSERT EQ: <8 x i32> <i32 10, i32 20, i32 30, i32 40, i32 100, i32 200, i32 300, i32 400> = call <8 x i32> @widen(<4 x i32> <i32 10, i32 20, i32 30, i32 40>, <4 x i32> <i32 100, i32 200, i32 300, i32 400>)
