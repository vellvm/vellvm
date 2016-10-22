define i32 @foo(i32 %a, i32 %b) {
  add i32 %a, %b
  icmp eq i32 %1, 0
  br i1 %2, label %5, label %3

; <label>:3                                       ; preds = %0
  %4 = add nsw i32 %b, %a
  br label %7

; <label>:5                                       ; preds = %0
  %6 = mul nsw i32 %b, %a
  br label %7

; <label>:7                                       ; preds = %5, %3
  %.0 = phi i32 [ %4, %3 ], [ %6, %5 ]
  ret i32 %.0
}

