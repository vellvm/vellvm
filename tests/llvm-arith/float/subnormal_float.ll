; ASSERT EQ: i32 0 = call i32 @main()

define i32 @main() {
  ; Normal float
  %r1 = fcmp oeq float 0x400928F5C0000000, 3.1449999809265137
  br i1 %r1, label %good1, label %bad1
good1:
  ; Subnormal float
  %r2 = fcmp oeq float 0x380251eb80000000, 6.729705046353719e-39
  br i1 %r2, label %good2, label %bad2
good2:
  ret i32 0
bad1:
  ret i32 1
bad2:
  ret i32 2
}
