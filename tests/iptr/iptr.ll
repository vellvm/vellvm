define i1 @test() {
  %p = alloca iptr
  store iptr 17, iptr* %p
  %int = ptrtoint iptr* %p to iptr
  %ptr = inttoptr iptr %int to iptr*
  %v = load iptr, iptr* %ptr
  %c = icmp eq iptr* %p, %ptr
  ret i1 %c
}

define i32 @main(i32 %argc, i8** %argv) {
  %v = call i1 @test()
  br i1 %v, label %true, label %false

true:
  ret i32 1

false:
  ret i32 0
}  
  

;; ASSERT EQ: i1 1 = call i1 @test() 
