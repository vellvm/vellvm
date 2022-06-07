%point = type [2 x i64]

@pt1 = global %point [ i64 10, i64 20 ]
@pt2 = global %point [ i64 10, i64 10 ]
@pt3 = global %point [ i64 20, i64 10 ]
@pt4 = global %point [ i64 20, i64 20 ]


define i64 @distance(%point* %fst, %point* %snd) {
    %one = getelementptr %point, %point* %fst, i32 0, i64 0
    %two = getelementptr %point, %point* %fst, i32 0, i64 1
    %thre = getelementptr %point, %point* %snd, i32 0, i64 0
    %four = getelementptr %point, %point* %snd, i32 0, i64 1
    %x1 = load i64, i64* %one
    %y1 = load i64, i64* %two
    %x2 = load i64, i64* %thre
    %y2 = load i64, i64* %four


    %1 = sub i64 %x1, %x2
    %2 = mul i64 %1, %1
    %3 = sub i64 %y1, %y2
    %4 = mul i64 %3, %3 
    %5 = add i64 %2, %4 
    ret i64 %5
}

define i64 @is_square(%point* %p1, %point* %p2, %point* %p3, %point* %p4) {
  %d2 = call i64 @distance(%point* %p1, %point* %p2)
  %d3 = call i64 @distance(%point* %p1, %point* %p3)
  %d4 = call i64 @distance(%point* %p1, %point* %p4)

  %part1c1 = icmp eq i64 %d2, 0
  %part1c2 = icmp eq i64 %d3, 0
  %part1c3 = icmp eq i64 %d4, 0

  %b1tmp = or i1 %part1c1, %part1c2
  %b1 = or i1 %b1tmp, %part1c3
  br i1 %b1, label %end, label %part2
  
part2:
  %c1 = icmp eq i64 %d2, %d3
  %1 = mul i64 %d2, 2
  %c2 = icmp eq i64 %1, %d4

  %d5 = call i64 @distance(%point* %p2, %point* %p4)
  %d6 = call i64 @distance(%point* %p2, %point* %p3)
  %2 = mul i64 %d5, 2
  %c3 = icmp eq i64 %2, %d6

  %cmp1 = and i1 %c1, %c2
  %b2 = and i1 %c3, %cmp1
  br i1 %b2, label %exitT, label %part3

part3:
  %3 = mul i64 %d3, 2

  %d7 = call i64 @distance(%point* %p3, %point* %p2)
  %d8 = call i64 @distance(%point* %p3, %point* %p4)
  %4 = mul i64 %d7, 2

  %part3c1 = icmp eq i64 %d3, %d4
  %part3c2 = icmp eq i64 %3, %d2
  %part3c3 = icmp eq i64 %4, %d8

  %cmp3_1 = and i1 %part3c1, %part3c2
  %b3 = and i1 %cmp3_1, %part3c3
  br i1 %b3, label %exitT, label %part4

part4:
  %5 = mul i64 %d2, 2
  %d9 = call i64 @distance(%point* %p2, %point* %p3)
  %d10 = call i64 @distance(%point* %p2, %point* %p4)
  %6 = mul i64 %d9, 2

  %part4c1 = icmp eq i64 %d2, %d4
  %part4c2 = icmp eq i64 %5, %d3
  %part4c3 = icmp eq i64 %6, %d10

  %cmp4_1 = and i1 %part4c1, %part4c2
  %b4 = and i1 %cmp4_1, %part4c3
  br i1 %b4, label %exitT, label %end
  
exitT:
  ret i64 1
end:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %argv) {
  %ans = call i64 @is_square(%point* @pt1, %point* @pt2, %point* @pt3, %point* @pt4)
  ret i64 %ans
}