; At i1 the signed values are {-1, 0}, so `srem i1 1, 1` is INT_MIN srem -1,
; which LangRef makes undefined behavior ("Overflow also leads to undefined
; behavior ... by taking the remainder of a 32-bit division of -2147483648 by
; -1").  llubi agrees; LLVM's instsimplify folds it to 0, a legal refinement.
define i1 @main(i1 %argc, i8** %arcv) {
  %1 = srem i1 1, 1
  ret i1 %1
}

; ASSERT UB 6: call i1 @main(i64 0, i8** null)
