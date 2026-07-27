define <4 x i32> @shuffle_it() {
  %r = shufflevector <4 x i32> <i32 10, i32 20, i32 30, i32 40>, <4 x i32> <i32 100, i32 200, i32 300, i32 400>, <4 x i32> <i32 0, i32 4, i32 3, i32 7>
  ret <4 x i32> %r
}

; ASSERT EQ: <4 x i32> <i32 10, i32 100, i32 40, i32 400> = call <4 x i32> @shuffle_it()
