%vec = type [2 x i64]
%mat = type [2 x %vec]

@mat1 = global %mat [ %vec [ i64  1, i64  2 ], %vec [ i64  3, i64  4 ] ]
@mat2 = global %mat [ %vec [ i64  5, i64  6 ], %vec [ i64  7, i64  8 ] ]
@mat3 = global %mat [ %vec [ i64 19, i64 22 ], %vec [ i64 43, i64 50 ] ]
@matr = global %mat [ %vec [ i64  0, i64  0 ], %vec [ i64  0, i64  0 ] ]

define i64 @main(i64 %argc, i8** %argv) {
  call void @matmul(%mat* @mat1, %mat* @mat2, %mat* @matr)
  %1 = call i64 @mateq (%mat* @mat3, %mat* @matr)
  ret i64 %1
}

define void @matmul(%mat* %a, %mat* %b, %mat* %c) {
  %i = alloca i64
  %j = alloca i64
  store i64 0, i64* %i
  br label %starti

starti:
  %iv = load i64, i64* %i
  %ic = icmp slt i64 %iv, 2
  br i1 %ic, label %theni, label %endi

theni:
  store i64 0, i64* %j
  br label %startj

startj:
  %jv = load i64, i64* %j
  %jc = icmp slt i64 %jv, 2
  br i1 %jc, label %thenj, label %endj

thenj:
  %r  = getelementptr %mat, %mat* %c, i64 0, i64 %iv, i64 %jv

  %a1 = getelementptr %mat, %mat* %a, i64 0, i64 %iv, i64   0
  %b1 = getelementptr %mat, %mat* %b, i64 0, i64   0, i64 %jv
  %a2 = getelementptr %mat, %mat* %a, i64 0, i64 %iv, i64   1
  %b2 = getelementptr %mat, %mat* %b, i64 0, i64   1, i64 %jv

  %a1v = load i64, i64* %a1
  %b1v = load i64, i64* %b1
  %a2v = load i64, i64* %a2
  %b2v = load i64, i64* %b2

  %ab1 = mul i64 %a1v, %b1v
  %ab2 = mul i64 %a2v, %b2v
  %ab = add i64 %ab1, %ab2
  store i64 %ab, i64* %r

  %jinc = add i64 %jv, 1
  store i64 %jinc, i64* %j
  br label %startj

endj:
  %iinc = add i64 %iv, 1
  store i64 %iinc, i64* %i
  br label %starti

endi:
  ret void
}

define i64 @mateq(%mat* %ma, %mat* %mb) {
  %r = alloca i64
  store i64 0, i64* %r

  %i = alloca i64
  %j = alloca i64
  store i64 0, i64* %i
  br label %starti1

starti1:
  %iv = load i64, i64* %i
  %ic = icmp slt i64 %iv, 2
  br i1 %ic, label %theni1, label %endi1

theni1:
  store i64 0, i64* %j
  br label %startj1

startj1:
  %jv = load i64, i64* %j
  %jc = icmp slt i64 %jv, 2
  br i1 %jc, label %thenj1, label %endj1

thenj1:
  %a = getelementptr %mat, %mat* %ma, i64 0, i64 %iv, i64 %jv
  %b = getelementptr %mat, %mat* %mb, i64 0, i64 %iv, i64 %jv
  %av = load i64, i64* %a
  %bv = load i64, i64* %b

  %cmp = xor i64 %av, %bv
  %rv = load i64, i64* %r
  %tmp = or i64 %cmp, %rv
  store i64 %tmp, i64* %r

  %jinc = add i64 %jv, 1
  store i64 %jinc, i64* %j
  br label %startj1

endj1:
  %iinc = add i64 %iv, 1
  store i64 %iinc, i64* %i
  br label %starti1

endi1:
  %rv1 = load i64, i64* %r
  ret i64 %rv1
}
