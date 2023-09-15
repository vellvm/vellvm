target datalayout="E"
target triple = "powerpc64-unknown-linux-gnu"

define <8 x i1> @src(<8 x i1> %t){
  %v = bitcast <8 x i1> %t to i8
  %t2 = bitcast i8 %v to <8 x i1>
  ret <8 x i1> %t2
}

define <8 x i1> @tgt(<8 x i1> %t){
  ret <8 x i1> %t
}

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
