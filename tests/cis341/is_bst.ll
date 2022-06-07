%Node = type { %Node*, %Node*, i64 }

@test1 = global %Node { %Node* null, %Node* null, i64 1 }
@test2 = global %Node { %Node* null, %Node* null, i64 4 }
@test3 = global %Node { %Node* null, %Node* null, i64 6 }
@test4 = global %Node { %Node* @test1, %Node* null, i64 2 }
@test5 = global %Node { %Node* @test2, %Node* @test3, i64 5 }
@test = global %Node { %Node* @test4, %Node* @test5, i64 3 }

define i1 @is_bst(%Node* %n, i64* %min, i64* %max) {
  ; if (n == null) return true;
  %1 = icmp eq %Node* %n, null
  br i1 %1, label %bst, label %process_min
process_min:
  %n.val.ptr = getelementptr %Node, %Node* %n, i64 0, i32 2
  %n.val = load i64, i64* %n.val.ptr
  ; if (min && n->val < *min) return false
  %min.null = icmp eq i64* %min, null
  br i1 %min.null, label %process_max, label %process_min_2
process_min_2:
  %2 = load i64, i64* %min
  %3 = icmp slt i64 %n.val, %2
  br i1 %3, label %not_bst, label %process_max
process_max:
  ; if (max && n->val > *max) return false;
  %max.null = icmp eq i64* %max, null
  br i1 %max.null, label %recur_left, label %process_max_2
process_max_2:
  %4 = load i64, i64* %max
  %5 = icmp sgt i64 %n.val, %4
  br i1 %5, label %not_bst, label %recur_left
recur_left:
  ; if (!is_bst(n->l, min, &n->val)) return false;
  %n.l.ptr = getelementptr %Node, %Node* %n, i64 0, i32 0
  %n.l = load %Node*, %Node** %n.l.ptr
  %l = call i1 @is_bst(%Node* %n.l, i64* %min, i64* %n.val.ptr)
  br i1 %l, label %recur_right, label %not_bst 
recur_right:
  ; return is_bst(n->r, &n->val, max);
  %n.r.ptr = getelementptr %Node, %Node* %n, i64 0, i32 1
  %n.r = load %Node*, %Node** %n.r.ptr
  %r = call i1 @is_bst(%Node* %n.r, i64* %n.val.ptr, i64* %max)
  br i1 %r, label %bst, label %not_bst 
not_bst:
  ret i1 0
bst:
  ret i1 1
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i1 @is_bst(%Node* @test, i64* null, i64* null)
  br i1 %1, label %succ, label %fail
succ:
  ret i64 0
fail:
  ret i64 1
}