%struct.Node = type { %struct.Node*, %struct.Node*, i64 }

@test1 = global %struct.Node { %struct.Node* null, %struct.Node* null, i64 100 }
@test2 = global %struct.Node { %struct.Node* @test1, %struct.Node* null, i64 10 }
@test3 = global %struct.Node { %struct.Node* null, %struct.Node* null, i64 1 }
@test = global %struct.Node { %struct.Node* @test2, %struct.Node* @test3, i64 5 }

define i64 @sum_tree(%struct.Node* %t) {
  %1 = icmp eq %struct.Node* %t, null
  br i1 %1, label %then, label %else

then:  
  ret i64 0

else: 
  %2 = getelementptr %struct.Node, %struct.Node* %t, i32 0, i32 2
  %3 = load i64, i64* %2
  %4 = getelementptr %struct.Node, %struct.Node* %t, i32 0, i32 1
  %5 = load %struct.Node*, %struct.Node** %4
  %6 = call i64 @sum_tree(%struct.Node* %5)
  %7 = add i64 %3, %6
  %8 = getelementptr %struct.Node, %struct.Node* %t, i32 0, i32 0
  %9 = load %struct.Node*, %struct.Node** %8
  %10 = call i64 @sum_tree(%struct.Node* %9)
  %11 = add i64 %7, %10
  ret i64 %11
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @sum_tree(%struct.Node* @test)
  ret i64 %1
}
