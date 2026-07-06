define i64 @main(i64 %argc, i8** %argv) {
  %1 = alloca i64
  store i64 3, i64* %1
  %2 = bitcast i64* %1 to [10 x i64]*
  %3 = bitcast [10 x i64]* %2 to i64*
  %4 = load i64, i64* %3
  ret i64 %4
}


; ASSERT EQ: i64 3 = call i64 @main(i64 0, i8** null)


; test1 (line 20): bitcast i8 255 to i8 ; yields i8 -1
define i8 @test1() {
  %X = bitcast i8 255 to i8
  ret i8 %X
}
; ASSERT EQ: i8 -1 = call i8 @test1()


; test2 (line 21): bitcast i32* %x to i16* ; yields i16*:%x
; Store 0 through i32*, cast pointer to i16*, load i16 -> 0 (endianness-independent)
define i16 @test2() {
  %p = alloca i32
  store i32 0, i32* %p
  %Y = bitcast i32* %p to i16*
  %r = load i16, i16* %Y
  ret i16 %r
}
; ASSERT EQ: i16 0 = call i16 @test2()


; test3 (line 22): bitcast <2 x i32> %V to i64 ; yields i64 (endianness-dependent)
; Use all-zero vector so the result is 0 regardless of endianness.
define i64 @test3(<2 x i32> %V) {
  %Z = bitcast <2 x i32> %V to i64
  ret i64 %Z
}
; ASSERT EQ: i64 0 = call i64 @test3(<2 x i32> <i32 0, i32 0>)


; test4 (line 23): bitcast <2 x i32*> %V to <2 x i64*> ; yields <2 x i64*>
; Round-trip through the cast to verify the pointer identity is preserved.
define i32 @test4() {
  %p = alloca i32
  store i32 99, i32* %p
  %v0 = insertelement <2 x i32*> undef, i32* %p, i32 0
  %v1 = insertelement <2 x i32*> %v0, i32* null, i32 1
  %Z  = bitcast <2 x i32*> %v1 to <2 x i64*>
  %w  = bitcast <2 x i64*> %Z  to <2 x i32*>
  %q  = extractelement <2 x i32*> %w, i32 0
  %r  = load i32, i32* %q
  ret i32 %r
}
; ASSERT EQ: i32 99 = call i32 @test4()


; test_a (line 26): bitcast i64 %bi to i64 ; no-op cast, returns the integer unchanged
; (%bi is an integer parameter; b64 is not a standard LLVM type so we use i64)
define i64 @test_a(i64 %bi) {
  %a = bitcast i64 %bi to i64
  ret i64 %a
}
; ASSERT EQ: i64 42 = call i64 @test_a(i64 42)
; ASSERT EQ: i64 0  = call i64 @test_a(i64 0)

; Lines 27-29 involve converting between integers and pointers (%bi <-> %bp).
; In standard LLVM IR these use ptrtoint / inttoptr, not bitcast, so they are
; not representable here.
