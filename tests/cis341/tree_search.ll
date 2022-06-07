%node = type { %node*, %node*, i64 }

@root = global %node { %node* @node1, %node* @node2, i64 5 }
@node1 = global %node { %node* @node3, %node* @node4, i64 2 }
@node2 = global %node { %node* @node5, %node* null, i64 8 }
@node3 = global %node { %node* null, %node* null, i64 1 }
@node4 = global %node { %node* null, %node* null, i64 3 }
@node5 = global %node { %node* null, %node* null, i64 7 }

define i64 @tree_search(%node* %root, i64 %target) {
    %is_null = icmp eq %node* %root, null
    br i1 %is_null, label %null_node, label %valid_node
valid_node:
    %value_ptr = getelementptr %node, %node* %root, i32 0, i32 2
    %value = load i64, i64* %value_ptr
    %check = icmp eq i64 %target, %value
    br i1 %check, label %found, label %not_found
null_node:
    ret i64 0
found:
    ret i64 1
not_found:
    %left_child = getelementptr %node, %node* %root, i32 0, i32 0
    %right_child = getelementptr %node, %node* %root, i32 0, i32 1
    %left_child_ptr = load %node*, %node** %left_child
    %right_child_ptr = load %node*, %node** %right_child
    %left_check = call i64 @tree_search(%node* %left_child_ptr, i64 %target)
    %right_check = call i64 @tree_search(%node* %right_child_ptr, i64 %target)
    %result = or i64 %left_check, %right_check
    ret i64 %result
}

define i64 @main(i64 %argc, i8** %arcv) {
  %answer = call i64 @tree_search(%node* @root, i64 7)
  ret i64 %answer
}
