
define <2 x i8> @trunc_i16_to_i8(<2 x i16> %v) {
  %ans = trunc <2 x i16> %v to <2 x i8>
  ret <2 x i8> %ans
}

; ASSERT EQ: <2 x i8> <i8 8, i8 7> = call <2 x i8> @trunc_i16_to_i8(<2 x i16><i16 8, i16 7>)
; ASSERT EQ: <2 x i8> <i8 8, i8 7> = call <2 x i8> @trunc_i16_to_i8(<2 x i16><i16 264, i16 263>)


define <2 x i8> @trunc_i32_to_i8(<2 x i32> %v) {
  %ans = trunc <2 x i32> %v to <2 x i8>
  ret <2 x i8> %ans
}

; ASSERT EQ: <2 x i8> <i8 8, i8 7> = call <2 x i8> @trunc_i32_to_i8(<2 x i32><i32 8, i32 7>)
; ASSERT EQ: <2 x i8> <i8 8, i8 7> = call <2 x i8> @trunc_i32_to_i8(<2 x i32><i32 264, i32 263>)


define <2 x i16> @zext_i8_to_i16(<2 x i8> %v) {
  %ans = zext <2 x i8> %v to <2 x i16>
  ret <2 x i16> %ans
}

; ASSERT EQ: <2 x i16> <i16 8, i16 7> = call <2 x i16> @zext_i8_to_i16(<2 x i8><i8 8, i8 7>)
; ASSERT EQ: <2 x i16> <i16 255, i16 128> = call <2 x i16> @zext_i8_to_i16(<2 x i8><i8 -1, i8 -128>)


define <2 x i32> @zext_i16_to_i32(<2 x i16> %v) {
  %ans = zext <2 x i16> %v to <2 x i32>
  ret <2 x i32> %ans
}

; ASSERT EQ: <2 x i32> <i32 8, i32 7> = call <2 x i32> @zext_i16_to_i32(<2 x i16><i16 8, i16 7>)
; ASSERT EQ: <2 x i32> <i32 65535, i32 32768> = call <2 x i32> @zext_i16_to_i32(<2 x i16><i16 -1, i16 -32768>)


define <2 x i16> @sext_i8_to_i16(<2 x i8> %v) {
  %ans = sext <2 x i8> %v to <2 x i16>
  ret <2 x i16> %ans
}

; ASSERT EQ: <2 x i16> <i16 8, i16 7> = call <2 x i16> @sext_i8_to_i16(<2 x i8><i8 8, i8 7>)
; ASSERT EQ: <2 x i16> <i16 -1, i16 -128> = call <2 x i16> @sext_i8_to_i16(<2 x i8><i8 -1, i8 -128>)


define <2 x i32> @sext_i16_to_i32(<2 x i16> %v) {
  %ans = sext <2 x i16> %v to <2 x i32>
  ret <2 x i32> %ans
}

; ASSERT EQ: <2 x i32> <i32 8, i32 7> = call <2 x i32> @sext_i16_to_i32(<2 x i16><i16 8, i16 7>)
; ASSERT EQ: <2 x i32> <i32 -1, i32 -32768> = call <2 x i32> @sext_i16_to_i32(<2 x i16><i16 -1, i16 -32768>)
