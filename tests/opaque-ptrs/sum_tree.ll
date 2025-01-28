%struct.Node = type { ptr, ptr, i64 }

@test1 = global %struct.Node { ptr null, ptr null, i64 100 }
@test2 = global %struct.Node { ptr @test1, ptr null, i64 10 }
@test3 = global %struct.Node { ptr null, ptr null, i64 1 }
@test = global %struct.Node { ptr @test2, ptr @test3, i64 5 }

define i64 @sum_tree(ptr %t) {
  %1 = icmp eq ptr %t, null
  br i1 %1, label %then, label %else

then:  
  ret i64 0

else: 
  %2 = getelementptr %struct.Node, ptr %t, i32 0, i32 2
  %3 = load i64, ptr %2
  %4 = getelementptr %struct.Node, ptr %t, i32 0, i32 1
  %5 = load ptr, ptr %4
  %6 = call i64 @sum_tree(ptr %5)
  %7 = add i64 %3, %6
  %8 = getelementptr %struct.Node, ptr %t, i32 0, i32 0
  %9 = load ptr, ptr %8
  %10 = call i64 @sum_tree(ptr %9)
  %11 = add i64 %7, %10
  ret i64 %11
}

define i64 @main(i64 %argc, ptr %argv) {
  %1 = call i64 @sum_tree(ptr @test)
  ret i64 %1
}
