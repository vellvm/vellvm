; ModuleID = 'phi-same.ll'
source_filename = "phi-same.ll"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.12.0"

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = icmp eq i64 2, %argc
  br i1 %1, label %left, label %right

left:                                             ; preds = %0
  br label %merge

right:                                            ; preds = %0
  br label %merge

merge:                                            ; preds = %right, %left
  %z = phi i64 [ 100, %left ], [ 200, %left ]
  ret i64 %z
}
