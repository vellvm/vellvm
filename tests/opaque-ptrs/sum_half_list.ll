%struct.List = type { i64, ptr }

@one_elt = global %struct.List { i64 1, ptr null }
@two_elts = global %struct.List { i64 2, ptr @one_elt }
@three_elts = global %struct.List { i64 4, ptr @two_elts }
@four_elts = global %struct.List { i64 8, ptr @three_elts }
@test = global %struct.List { i64 16, ptr @four_elts }

define i64 @sum_half_list(ptr %l) {
  %1 = icmp eq ptr %l, null
  br i1 %1, label %then, label %else
then:
  ret i64 0
else:
  %2 = getelementptr %struct.List, ptr %l, i32 0, i32 0
  %3 = load i64, ptr %2
  %4 = ashr i64 %3, 1
  %5 = getelementptr %struct.List, ptr %l, i32 0, i32 1
  %6 = load ptr, ptr %5
  %7 = call i64 @sum_half_list(ptr %6)
  %8 = add i64 %4, %7
  ret i64 %8
}

define i64 @main(i64 %argc, ptr %argv) {
  %1 = call i64 @sum_half_list(ptr @test)
  ret i64 %1
}

; ASSERT EQ: i64 15 = call i64 @main(i64 0, ptr null)

