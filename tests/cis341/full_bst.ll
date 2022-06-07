

%Node = type { %Node*, %Node*, i64 }


@n1 = global %Node { %Node* null, %Node* null, i64 1 }
@n2 = global %Node { %Node* null, %Node* null, i64 1 }
@n3 = global %Node { %Node* null, %Node* null, i64 1 }
@n4 = global %Node { %Node* null, %Node* null, i64 1 }
@n5 = global %Node { %Node* @n1, %Node* @n2, i64 1 }
@n6 = global %Node { %Node* @n3, %Node* @n4, i64 1 }
@root1 = global %Node { %Node* @n5, %Node* @n6, i64 1 }

@n5_2 = global %Node { %Node* @n1, %Node* null, i64 1 }
@root2 = global %Node { %Node* @n5_2, %Node* @n6, i64 1 }

define i1 @bst_full(%Node* %n) {
  %1 = icmp eq %Node* %n, null
  br i1 %1, label %full, label %check_leaf

check_leaf:

  %nlptr = getelementptr %Node, %Node* %n, i64 0, i32 0
  %nl = load %Node*, %Node** %nlptr
  %cmp1 = icmp eq %Node* %nl, null

  %nrptr = getelementptr %Node, %Node* %n, i64 0, i32 1
  %nr = load %Node*, %Node** %nrptr
  %cmp2 = icmp eq %Node* %nr, null

  %and = and i1 %cmp1, %cmp2
  br i1 %and, label %full, label %check_one_is_null

check_one_is_null:
  %xor = xor i1 %cmp1, %cmp2
  br i1 %xor, label %not_full, label %check_subtrees

check_subtrees:
  %left = call i1 @bst_full(%Node* %nl)
  %right = call i1 @bst_full(%Node* %nr) 
  %result = and i1 %left, %right
  br i1 %result, label %full, label %not_full

full:
  ret i1 1

not_full:
  ret i1 0

}

define i64 @main(i64 %argc, i8** %argv) {
  %2 = call i1 @bst_full(%Node* @root1)
  ret i1 %2
}