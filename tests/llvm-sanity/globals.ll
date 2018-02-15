%T1 = type {%T2*}
%T2 = type {%T1*}
%B = type {i64, i64}
%C = type {%C*, %B}

@G1 = global i64 17
@G3 = global i64** @G2
@G2 = global i64* @G1

@R1 = global %T1 {%T2* @R2}
@R2 = global %T2 {%T1* @R1}

@F1 = global i64 (i64)* @fun

define i64 @fun (i64 %arg) {
  %x = load i64, i64* @G1
  ret i64 %x
}

define i64 @main(i64 %argc, i8** %arcv) {
  %ans = call i64 @fun(i64 0)
  ret i64 %ans
}



