; ModuleID = 'lshr2.ll'
source_filename = "lshr2.ll"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.12.0"

define i1 @exact_lshr_ne_last_zero(i8 %a) {
  %shr = lshr exact i8 -127, %a
  %cmp = icmp ne i8 %shr, 0
  ret i1 %cmp
}
