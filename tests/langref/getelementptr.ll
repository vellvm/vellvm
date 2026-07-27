; Examples from the LLVM LangRef's 'getelementptr' Instruction section.
; langref: getelementptr-instruction sha1=1b190fd6f5e2b3ce02447b82d0fa4bcc8b6d331a
;
; LangRef 24.0.0git gives the following example(s):
;
; %aptr = getelementptr {i32, [12 x i8]}, ptr %saptr, i64 0, i32 1
; %vptr = getelementptr {i32, <2 x i8>}, ptr %svptr, i64 0, i32 1, i32 1
; %eptr = getelementptr [12 x i8], ptr %aptr, i64 0, i32 1
; %iptr = getelementptr [10 x i32], ptr @arr, i16 0, i16 0

@arr = global [10 x i32] [i32 0, i32 1, i32 2, i32 3, i32 4,
                          i32 5, i32 6, i32 7, i32 8, i32 9]

; %aptr = getelementptr {i32, [12 x i8]}, ptr %saptr, i64 0, i32 1
; %eptr = getelementptr [12 x i8], ptr %aptr, i64 0, i32 1
; Field 1 of the struct is the array; element 1 of that array is the second i8.
define i8 @struct_then_array() {
  %saptr = alloca {i32, [12 x i8]}
  %aptr = getelementptr {i32, [12 x i8]}, ptr %saptr, i64 0, i32 1
  %eptr = getelementptr [12 x i8], ptr %aptr, i64 0, i32 1
  store i8 42, ptr %eptr
  %r = load i8, ptr %eptr
  ret i8 %r
}

; %vptr = getelementptr {i32, <2 x i8>}, ptr %svptr, i64 0, i32 1, i32 1
define i8 @struct_then_vector() {
  %svptr = alloca {i32, <2 x i8>}
  %vptr = getelementptr {i32, <2 x i8>}, ptr %svptr, i64 0, i32 1, i32 1
  store i8 7, ptr %vptr
  %r = load i8, ptr %vptr
  ret i8 %r
}

; %iptr = getelementptr [10 x i32], ptr @arr, i16 0, i16 0
; The index type need not be i64; the first index steps over whole arrays.
define i32 @global_array(i16 %i) {
  %iptr = getelementptr [10 x i32], ptr @arr, i16 0, i16 %i
  %r = load i32, ptr %iptr
  ret i32 %r
}

; The same walk with an i64 index, which Vellvm does handle.
define i32 @global_array64(i64 %i) {
  %iptr = getelementptr [10 x i32], ptr @arr, i64 0, i64 %i
  %r = load i32, ptr %iptr
  ret i32 %r
}

; ASSERT EQ: i8 42 = call i8 @struct_then_array()
; ASSERT EQ: i8 7 = call i8 @struct_then_vector()
; ASSERT EQ: i32 0 = call i32 @global_array64(i64 0)
; ASSERT EQ: i32 6 = call i32 @global_array64(i64 6)
;
; VELLVM GAP: LangRef's own example indexes with i16, but Gep.v:92-102 only
; matches i8/i32/i64/iptr indices and raises "handle_gep_ptr: unsupported
; index type" for any other width. Re-enable by restoring the leading
; single ';' once i16 is accepted:
;; ASSERT EQ: i32 0 = call i32 @global_array(i16 0)
;; ASSERT EQ: i32 6 = call i32 @global_array(i16 6)
