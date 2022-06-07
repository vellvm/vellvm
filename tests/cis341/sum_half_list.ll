%struct.List = type { i64, %struct.List* }

@one_elt = global %struct.List { i64 1, %struct.List* null }
@two_elts = global %struct.List { i64 2, %struct.List* @one_elt }
@three_elts = global %struct.List { i64 4, %struct.List* @two_elts }
@four_elts = global %struct.List { i64 8, %struct.List* @three_elts }
@test = global %struct.List { i64 16, %struct.List* @four_elts }

define i64 @sum_half_list(%struct.List* %l) {
  %1 = icmp eq %struct.List* %l, null
  br i1 %1, label %then, label %else
then:
  ret i64 0
else:
  %2 = getelementptr %struct.List, %struct.List* %l, i32 0, i32 0
  %3 = load i64, i64* %2
  %4 = ashr i64 %3, 1
  %5 = getelementptr %struct.List, %struct.List* %l, i32 0, i32 1
  %6 = load %struct.List*, %struct.List** %5
  %7 = call i64 @sum_half_list(%struct.List* %6)
  %8 = add i64 %4, %7
  ret i64 %8
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @sum_half_list(%struct.List* @test)
  ret i64 %1
}

