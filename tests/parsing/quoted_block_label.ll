define i64 @foo() {
  br label %"this::rust % ; is a \xy \017 block@! label"

"this::rust % ; is a \xy \017 block@! label":
  ret i64 17
}


; ASSERT EQ: i64 17 = call i64 @foo()
