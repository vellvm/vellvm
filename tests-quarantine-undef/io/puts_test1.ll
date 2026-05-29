declare i32 @puts(i8* %str)

;; With our default semantics, this will succeed and print a single newline because
;; undef defaults to 0
define i32 @main(i32 %argc, i8** %argv) {
  %strptr = alloca i8
  %ans = call i32 @puts(i8* %strptr)
  ret i32 0
}
