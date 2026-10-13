; Parsing (and, through make test-full, pretty-printing) of flags,
; attributes, and metadata forms:
; - fast-math flags on fcmp and select;
; - trunc nuw/nsw in either order;
; - getelementptr inbounds/nusw/nuw in any order;
; - nofpclass, nofreeobj, dead_on_return, captures(ret: ...);
; - metadata whose name is a keyword (!captures, !dereferenceable);
; - blockaddress.

define double @fast_math(double %x, double %y, i1 %c) {
  %a = fcmp nnan oeq double %x, %y
  %b = fcmp fast olt double %x, %y
  %ab = and i1 %a, %b
  %s = select nnan ninf i1 %c, double %x, double %y
  %t = select i1 %ab, double %y, double %s
  ret double %t
}

; ASSERT EQ: double 1.0 = call double @fast_math(double 1.0, double 2.0, i1 1)

define i32 @trunc_flags() {
  %a = trunc nuw nsw i64 7 to i32
  %b = trunc nsw nuw i64 8 to i32
  %r = add i32 %a, %b
  ret i32 %r
}

; ASSERT EQ: i32 15 = call i32 @trunc_flags()

@arr = global [4 x i32] [i32 10, i32 11, i32 12, i32 13]

define i32 @gep_flags() {
  %p = getelementptr inbounds nuw [4 x i32], ptr @arr, i64 0, i64 1
  %q = getelementptr nuw inbounds i32, ptr %p, i64 1
  %r = getelementptr nusw nuw i32, ptr %q, i64 1
  %v = load i32, ptr %r
  ret i32 %v
}

; ASSERT EQ: i32 13 = call i32 @gep_flags()

define nofpclass(nan inf) double @attrs(double nofpclass(zero sub) %x, double nofpclass(519) %y,
                                        ptr dead_on_return %p, ptr dead_on_return(4) %q,
                                        ptr nofreeobj %r, ptr captures(address, ret: provenance) %s) {
  ret double %x
}

define double @call_attrs() {
  %a = alloca i32
  %r = call double @attrs(double 1.0, double 2.0, ptr %a, ptr %a, ptr %a, ptr %a)
  ret double %r
}

; ASSERT EQ: double 1.0 = call double @call_attrs()

@slot = global ptr null

define i32 @keyword_metadata() {
  %a = alloca i32
  store i32 5, ptr %a
  store ptr %a, ptr @slot, !captures !0
  %p = load ptr, ptr @slot, !dereferenceable !1, !align !1
  %v = load i32, ptr %p
  ret i32 %v
}

; ASSERT EQ: i32 5 = call i32 @keyword_metadata()

define i32 @block_address(i1 %c) {
entry:
  %t = select i1 %c, ptr blockaddress(@block_address, %a), ptr blockaddress(@block_address, %b)
  indirectbr ptr %t, [ label %a, label %b ]
a:
  ret i32 1
b:
  ret i32 2
}

; ASSERT EQ: i32 2 = call i32 @block_address(i1 0)

!0 = !{!"address", !"provenance"}
!1 = !{i64 4}
