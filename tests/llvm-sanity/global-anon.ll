; @0 = global i64 123
; @1 = global i64 13

; define i64 @main(i64 %argc, i8** %argv) {
;   %1 = load i64, i64* @0
;   %ans = call i64 @foo(i64 %1)
;   ret i64 %ans
; }



define i64 @foo(i64 %x) {
  %1 = add i64 %x, %x
  ret i64 %1
}
