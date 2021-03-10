define i64 @test(i64 %x) {
  %b = icmp sgt i64 %x, 10
  br i1 %b, label %1, label %2

1: ; explicit anonymous label
  br label %3

; implicit label 2
  %c = icmp sgt i64 %x, 5
  br i1 %c, label %3, label %4

; implicit label 3
  %z = phi i64 [15, %1], [7, %2], [2, %4]
  ret i64 %z

4: br label %3
}

; ASSERT EQ: i64 15 = call i64 @test(i64 15)
; ASSERT EQ: i64 7 = call i64 @test(i64 9)
; ASSERT EQ: i64 2 = call i64 @test(i64 0)


