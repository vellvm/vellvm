define {i32, float} @f(){
  %agg1 = insertvalue {i32, float} poison, i32 1, 0              ; yields {i32 1, float poison}
  ret {i32, float} %agg1
}

; ASSERT EQ: {i32, float} {i32 1, float poison} = call {i32, float} @f()


define {i32, float} @g(float %val){
  %agg1 = insertvalue {i32, float} poison, i32 1, 0              ; yields {i32 1, float poison}
  %agg2 = insertvalue {i32, float} %agg1, float %val, 1          ; yields {i32 1, float %val}
  ret {i32, float} %agg2
}

; ASSERT EQ: {i32, float} {i32 1, float 1.0} = call {i32, float} @g(float 1.0)
; ASSERT EQ: {i32, float} {i32 1, float 2.0} = call {i32, float} @g(float 2.0)


define {i32, float} @h(float %val){
  %agg3 = insertvalue {i32, {float}} poison, float %val, 1, 0    ; yields {i32 poison, {float %val}}  
  ret {i32, {float} } %agg3
}

; ASSERT EQ: {i32, {float}} {i32 poison, {float} {float 1.0}} = call {i32, float} @h(float 1.0)

define i1 @main() {
  %p = alloca { i64 }, align 8
  %a = insertvalue { i64 } poison, i64 123, 0
  %b = extractvalue { i64 } %a, 0
  %c = icmp uge i64 %b, 456
  ret i1 %c
}

; ASSERT EQ: i1 0 = call i1 @main()
