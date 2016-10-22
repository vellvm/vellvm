declare void @ll_puts(i8*)
declare i8* @ll_ltoa(i64)

%node = type { i64, %node*}

@hd = global %node {i64 1, %node* @md}
@md = global %node {i64 2, %node* @tl}
@tl = global %node {i64 3, %node* null}

define void @printint(i64 %x) {
  %1 = call i8* @ll_ltoa(i64 %x)
  call void @ll_puts(i8* %1)
  ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  %head = getelementptr %node, %node* @hd, i32 0, i32 0
  %1 = load i64, i64* %head
  call void @printint (i64 %1)
  %link = getelementptr %node, %node* @hd, i32 0, i32 1
  %next = load %node*, %node** %link
  %val = getelementptr %node, %node* %next, i32 0, i32 0
  %2 = load i64, i64* %val
  call void @printint (i64 %2)
  %link2 = getelementptr %node, %node* %next, i32 0, i32 1
  %next2 = load %node*, %node** %link2
  %val2 = getelementptr %node, %node* %next2, i32 0, i32 0
  %3 = load i64, i64* %val2
  call void @printint (i64 %3)
  ret i64 0
}



