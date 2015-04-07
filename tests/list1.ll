%node = type { i64, %node*}

@hd = global %node {i64 1, %node* @md}
@md = global %node {i64 2, %node* @tl}
@tl = global %node {i64 3, %node* null}

define i64 @main(i64 %argc, i8** %arcv) {
  %head = getelementptr %node* @hd, i32 0, i32 0
  %link = getelementptr %node* @hd, i32 0, i32 1
  %next = load %node** %link
  %val = getelementptr %node* %next, i32 0, i32 0
  %link2 = getelementptr %node* %next, i32 0, i32 1
  %next2 = load %node** %link2
  %val2 = getelementptr %node* %next2, i32 0, i32 0
  %1 = load i64* %val2
  ret i64 %1
}



