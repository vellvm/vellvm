define i64 @foo() {
  %f = alloca float
  store float 0xBFE6A09E60000000, float* %f, align 4
  %v = load float, float* %f
  %cnd = fcmp oeq float %v, -7.0710676908493040e-1
  br i1 %cnd, label %tb, label %fb

tb:
  ret i64 1

fb:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %ans = call i64 @foo()
  ret i64 %ans
}

