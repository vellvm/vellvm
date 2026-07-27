; PERF: function-call machinery.
; Naive doubly-recursive Fibonacci: exponentially many calls, each one
; exercising the Call/Return events, argument binding, and local frame
; push/pop on the stack handler. Very little arithmetic per call, so
; call overhead dominates.
;
; Tune: change the argument to @fib in @main (cost ~ fib(n) calls).
; fib(20) = 6765.

define i64 @fib(i64 %n) {
  %base = icmp sle i64 %n, 1
  br i1 %base, label %done, label %rec

rec:
  %n1 = sub i64 %n, 1
  %n2 = sub i64 %n, 2
  %f1 = call i64 @fib(i64 %n1)
  %f2 = call i64 @fib(i64 %n2)
  %r = add i64 %f1, %f2
  ret i64 %r

done:
  ret i64 %n
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @fib(i64 23)
  ret i64 %r
}

; ASSERT EQ: i64 28657 = call i64 @main(i64 0, i8** null)
