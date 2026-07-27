; Examples from the LLVM LangRef's 'extractvalue' Instruction section.
; langref: extractvalue-instruction sha1=7302130040c519639db90455418707b0b49b33e7
;
; LangRef 24.0.0git gives the following example(s):
;
; <result> = extractvalue {i32, float} %agg, 0    ; yields i32

; The LangRef fragment reads %agg out of thin air; here it is built first.
define i32 @extract_first(i32 %x, float %f) {
  %agg0 = insertvalue {i32, float} poison, i32 %x, 0
  %agg = insertvalue {i32, float} %agg0, float %f, 1
  %r = extractvalue {i32, float} %agg, 0
  ret i32 %r
}

; ASSERT EQ: i32 7 = call i32 @extract_first(i32 7, float 1.5)
