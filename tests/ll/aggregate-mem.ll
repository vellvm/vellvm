%agg = type { i64, i64, {i64, i64} }

declare void @ll_puts(i8*)
declare i8* @ll_ltoa(i64)

define void @printint(i64 %x) {
  %1 = call i8* @ll_ltoa(i64 %x)
  call void @ll_puts(i8* %1)
  ret void
}

define void @printagg(%agg %x) {
  %x0 = extractvalue %agg %x, 0
  %x1 = extractvalue %agg %x, 1
  %x20 = extractvalue %agg %x, 2, 0
  %x21 = extractvalue %agg %x, 2, 1
  call void @printint(i64 %x0)
  call void @printint(i64 %x1)
  call void @printint(i64 %x20)
  call void @printint(i64 %x21)
  ret void
}


define %agg @bar() {
  %v = insertvalue %agg zeroinitializer, i64 1, 0
  %u = insertvalue %agg %v, i64 2, 1
  %w = insertvalue %agg %u, {i64, i64} {i64 3, i64 4}, 2
  ret %agg %w
}

define %agg @foo(%agg %big) {
  %updated = insertvalue %agg %big, i64 17, 2, 1 
  ret %agg %updated
}

define i64 @main(i64 %argc, i8** %arcv) {
  %ptr = alloca %agg
  store %agg { i64 1, i64 2, {i64, i64} {i64 3, i64 4} }, %agg* %ptr
  %val = load %agg, %agg* %ptr
  %val2 = call %agg @bar()
  call void @printagg(%agg %val2)
  ret i64 0
}
