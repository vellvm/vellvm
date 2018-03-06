%T1 = type {%T2*, i64}
%T2 = type {%T1*, i64, i64}

@R1 = global %T1 {%T2* @R2, i64 42}
@R2 = global %T2 {%T1* @R1, i64 101, i64 317}

define i64 @main(i64 %argc, i8** %arcv) {
  ret i64 0  
}



