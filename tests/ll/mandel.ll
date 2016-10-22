@v = global i64 2
@con = global i64 1
@it = global i64 32
@bnd = global i64 10

define i64 @escape(i64* %val, i64* %c, i64* %iter, i64* %bound) {
    %mlt = load i64, i64* %val
    %mult = mul i64 %mlt, %mlt
    %reso = alloca i64
    %conta = load i64, i64* %c
    %rest = add i64 %mult, %conta
    store i64 %rest, i64* %reso
    %lim = load i64, i64* %bound
    %cmp = icmp sgt i64 %lim, %rest
    br i1 %cmp, label %cont, label %quit

cont:
   %itr = load i64, i64* %iter
   %cmp2 = icmp sgt i64 %itr, 0
   br i1 %cmp, label %keep, label %en

keep:
   %irr = load i64, i64* %iter
   %sbt = sub i64 %irr, 1
   %sb = alloca i64
   store i64 %sbt, i64* %sb
   %tmp = call i64 @escape (i64* %reso, i64* %c, i64* %sb, i64* %bound)
   ret i64 %tmp
en:
   ret i64 1

quit:
   ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
    %tst = call i64 @escape(i64* @v, i64* @con, i64* @it, i64* @bnd)
    ret i64 %tst
}
