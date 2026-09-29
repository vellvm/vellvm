define i32 @main(i32 %argc, i8** %arcv) {
  %ptr = alloca b64         ; allocate a byte type in memory
  %v = load b64, ptr %ptr   ; poison bytes
  store b64 %v, ptr %ptr    ; store poison
  ret i32 0
}


; ASSERT EQ: i32 0 = call i32 @main(i32 0, i8** null)
