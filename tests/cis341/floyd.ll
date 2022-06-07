%Node = type { i64, %Node* }

; Small test case with cycle
@test1_n1 = global %Node { i64 1, %Node* @test1_n2 }
@test1_n2 = global %Node { i64 2, %Node* @test1_n3 }
@test1_n3 = global %Node { i64 3, %Node* @test1_n1 }

; Larger test case with cycle
@test2_n1 = global %Node { i64 1, %Node* @test2_n2 }
@test2_n2 = global %Node { i64 2, %Node* @test2_n3 }
@test2_n3 = global %Node { i64 3, %Node* @test2_n4 }
@test2_n4 = global %Node { i64 4, %Node* @test2_n5 }
@test2_n5 = global %Node { i64 5, %Node* @test2_n6 }
@test2_n6 = global %Node { i64 6, %Node* @test2_n7 }
@test2_n7 = global %Node { i64 7, %Node* @test2_n8 }
@test2_n8 = global %Node { i64 8, %Node* @test2_n4 }

; Test case with no cycle
@test3_n1 = global %Node { i64 1, %Node* @test3_n2 }
@test3_n2 = global %Node { i64 2, %Node* @test3_n3 }
@test3_n3 = global %Node { i64 3, %Node* @test3_n4 }
@test3_n4 = global %Node { i64 4, %Node* @test3_n5 }
@test3_n5 = global %Node { i64 5, %Node* @test3_n6 }
@test3_n6 = global %Node { i64 6, %Node* @test3_n7 }
@test3_n7 = global %Node { i64 7, %Node* null }

define i64 @find_cycle(%Node* %head) {
  %head_null = icmp eq %Node* %head, null
  br i1 %head_null, label %return_false, label %init_pointers
init_pointers:
  %tortoise_ptr = alloca %Node*
  %hare_ptr = alloca %Node*
  store %Node* %head, %Node** %tortoise_ptr
  store %Node* %head, %Node** %hare_ptr
  br label %check_loop_conds
check_loop_conds:
  %tortoise = load %Node*, %Node** %tortoise_ptr
  %hare = load %Node*, %Node** %hare_ptr
  br label %check_tortoise_next
check_tortoise_next:
  %tortoise_link = getelementptr %Node, %Node* %tortoise, i32 0, i32 1
  %tortoise_next = load %Node*, %Node** %tortoise_link
  %tortoise_next_null = icmp eq %Node* %tortoise_next, null
  br i1 %tortoise_next_null, label %return_false, label %check_hare_next
check_hare_next:
  %hare_link = getelementptr %Node, %Node* %hare, i32 0, i32 1
  %hare_next = load %Node*, %Node** %hare_link
  %hare_next_null = icmp eq %Node* %hare_next, null
  br i1 %hare_next_null, label %return_false, label %check_hare_next_next
check_hare_next_next:
  %hare_next_link = getelementptr %Node, %Node* %hare_next, i32 0, i32 1
  %hare_next_next = load %Node*, %Node** %hare_next_link
  %hare_next_next_null = icmp eq %Node* %hare_next_next, null
  br i1 %hare_next_next_null, label %return_false, label %enter_loop
enter_loop:
  %equals = icmp eq %Node* %tortoise_next, %hare_next_next
  store %Node* %tortoise_next, %Node** %tortoise_ptr
  store %Node* %hare_next_next, %Node** %hare_ptr
  br i1 %equals, label %find_first, label %check_loop_conds
find_first:
  store %Node* %head, %Node** %tortoise_ptr
  br label %check_equals_in_cycle
check_equals_in_cycle:
  %tortoise_cycle = load %Node*, %Node** %tortoise_ptr
  %hare_cycle = load %Node*, %Node** %hare_ptr
  %equals_cycle = icmp eq %Node* %tortoise_cycle, %hare_cycle
  br i1 %equals_cycle, label %return_first_cycle_val, label %find_first_loop
find_first_loop:
  %tortoise_cycle_link = getelementptr %Node, %Node* %tortoise_cycle, i32 0, i32 1
  %tortoise_cycle_next = load %Node*, %Node** %tortoise_cycle_link
  store %Node* %tortoise_cycle_next, %Node** %tortoise_ptr
  %hare_cycle_link = getelementptr %Node, %Node* %hare_cycle, i32 0, i32 1
  %hare_cycle_next = load %Node*, %Node** %hare_cycle_link
  store %Node* %hare_cycle_next, %Node** %hare_ptr
  br label %check_equals_in_cycle
return_first_cycle_val:
  %first_val_ptr = getelementptr %Node, %Node* %tortoise_cycle, i32 0, i32 0
  %val = load i64, i64* %first_val_ptr
  ret i64 %val
return_false:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @find_cycle(%Node* @test2_n1)
  ret i64 %1
}