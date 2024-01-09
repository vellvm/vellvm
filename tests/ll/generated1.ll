define  i8 @test() {
b8:
    %v30 = ashr i32 2, 14
    br label %b9

b9:
    %v31 = udiv i8 3, 6
    %v32 = add i8 %v31, %v31
    %v33 = udiv i1 0, 1
    %v34 = ashr i1 %v33, 0
    ret i8 %v31
}

define i32 @main(i32 %argc, i8** %arcv) {
  %ans = call i8 @test()
  ret i32 0
}

; ASSERT EQ: i8 0 = call i8 @test()
