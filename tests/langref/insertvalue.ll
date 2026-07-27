; Examples from the LLVM LangRef's 'insertvalue' Instruction section.
; langref: insertvalue-instruction sha1=d84490ca561daf058a8aa16d5607b97ea417d231
;
; LangRef 24.0.0git gives the following example(s):
;
; %agg1 = insertvalue {i32, float} poison, i32 1, 0              ; yields {i32 1, float poison}
; %agg2 = insertvalue {i32, float} %agg1, float %val, 1          ; yields {i32 1, float %val}
; %agg3 = insertvalue {i32, {float}} poison, float %val, 1, 0    ; yields {i32 poison, {float %val}}

define {i32, float} @agg1() {
  %agg1 = insertvalue {i32, float} poison, i32 1, 0
  ret {i32, float} %agg1
}

define {i32, float} @agg2(float %val) {
  %agg1 = insertvalue {i32, float} poison, i32 1, 0
  %agg2 = insertvalue {i32, float} %agg1, float %val, 1
  ret {i32, float} %agg2
}

define {i32, {float}} @agg3(float %val) {
  %agg3 = insertvalue {i32, {float}} poison, float %val, 1, 0
  ret {i32, {float}} %agg3
}

; ASSERT EQ: {i32, float} {i32 1, float poison} = call {i32, float} @agg1()
; ASSERT EQ: {i32, float} {i32 1, float 2.5} = call {i32, float} @agg2(float 2.5)
; ASSERT EQ: {i32, {float}} {i32 poison, {float} {float 2.5}} = call {i32, {float}} @agg3(float 2.5)
