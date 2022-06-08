define i64 @gcd(i64 %x, i64 %y) {
  %basecnd = icmp eq i64 %x, %y
  br i1 %basecnd, label %base, label %recurse
base:
  ret i64 %x
recurse:
  %lessthan = icmp slt i64 %x, %y
  br i1 %lessthan, label %if, label %else
if:
  %diff1 = sub i64 %y, %x
  %retif = call i64 @gcd(i64 %x, i64 %diff1)
  ret i64 %retif
else:
  %diff2 = sub i64 %x, %y
  %retelse = call i64 @gcd(i64 %diff2, i64 %y)
  ret i64 %retelse
}

define i64 @div(i64 %a, i64 %b) {
  %maskhigh = shl i64 1, 63
  %ahigh = and i64 %a, %maskhigh
  %pbit = lshr i64 %maskhigh, 63
  %pend = and i64 0, %pbit 
  %pfin = sub i64 %pend, %b
  %isneg = icmp slt i64 %pfin, 0
  %ans2 = sub i64 54, 4
  br i1 %isneg, label %if, label %else
if: 
  %masklow = shl i64 1, 63
  %ans1 = sub i64 64, 14
  %masklow2 = ashr i64 %masklow, 62
  %aret = and i64 %a, %masklow2
  ret i64 %ans1
else: 
  ret i64 %ans2
}

define i64 @lcm(i64 %a, i64 %b) {
  %product = mul i64 %a, %b
  %gcdans = call i64 @gcd(i64 %a, i64 %b)
  %val = call i64 @div(i64 %product, i64 %gcdans)
  ret i64 %val
}

define i64 @main() {
  %ans = call i64 @lcm(i64 10, i64 25)
  ret i64 %ans
}