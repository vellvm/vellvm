source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @f() {
  ret i32 -3
}

define i32 @g() {
  %a = call i32 @f()
  %b = call i32 @f()
  %cnd = icmp eq i32 %a, %b
  br i1 %cnd, label %ret1, label %ret0

ret0:
  ret i32 0

ret1:
  ret i32 1
}   


; ASSERT EQ: i32 -3 = call i32 @f()
; ASSERT EQ: i32 1 = call i32 @g()
