define i64 @f1(i64) {
  ret i64 %0
}   

define i64 @f1a(i64) {
1:
  ret i64 %0
}   


; This variant is an error -- it is ill-typed
; define i64 @f1x(i64 %x) {
;   ret i64 %0
; }   


define i64 @f2(i64) {
  br label %2

  ret i64 %0
}

; define i64 @f2a(i64) {
; 1:
;   br label %2

; 2:
;   ret i64 %0
; }


; define i64 @f2x(i64 %x) {
;   br label %2

;   ret i64 %0
; }



; define i64 @f3(i64) {
;   br label %1

;   ret i64 %0     ;; This is technically dead code -- block label %2 is unreachable
; }

; define i64 @f3a(i64) {
; 1:
;   br label %1
; 2:
;   ret i64 %0     ;; This is technically dead code -- block label %2 is unreachable
; }



; define i64 @f3x(i64 %x) {
;   br label %1

;   ret i64 %0     ;; This is no longer dead, but is now ill typed
; }


define i64 @0() {
  add i64 3, 4
  ret i64 %1
}

define i32 @boo(i32) {
  ret i32 %0
}   
