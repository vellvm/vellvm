; clang seems to change the constant 128 into -128 in this code
; Apple LLVM version 8.0.0 (clang-800.0.42.1)
define i1 @exact_lshr_ne_last_zero(i8 %a) {         
  %shr = lshr exact i8 129, %a                      
  %cmp = icmp ne i8 %shr, 0                         
  ret i1 %cmp                                       
}

; Running:
; clang -S -emit-llvm -o lshr.clang.ll lshr.ll 
;
; produces the following output, where the constant 128 has been changed to -128:
;
; ; ModuleID = 'lshr.ll'
; source_filename = "lshr.ll"
; target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
; target triple = "x86_64-apple-macosx10.12.0"

; define i1 @exact_lshr_ne_last_zero(i8 %a) {
;   %shr = lshr exact i8 -128, %a
;   %cmp = icmp ne i8 %shr, 0
;   ret i1 %cmp
; }
