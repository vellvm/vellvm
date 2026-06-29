define ptr @__personality_routine (i32 %version, i32 %actions, i64 %exception_class, ptr %ext, ptr %ctxt) {
  ret ptr null
}  


; doesn't actually raise any exceptions
define i64 @test_no_exception(i64 %n) {
  ret i64 %n
}


define i64 @test_invoke(i64 %n) personality i32 (i32, i32, i64, i8*, i8*)* @__personality_routine {
  %ans = invoke i64 @test_no_exception(i64 %n) to label %continue
            unwind label %exception

continue:
  ret i64 %ans

exception:
  %res = landingpad { ptr, i64 }
          cleanup
  ret i64 17	  
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = alloca i64
  store i64 0, i64* %1
  %2 = call i64 @test_invoke(i64 5)
  ret i64 %2
}


; ASSERT EQ: i64 5 = call i64 @main(i64 0, i8** null)
