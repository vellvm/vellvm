define i64 @g0(i64 %arg) {
    %res = add i64 %arg, 3
    ret i64 %res
}

define  i64 @main() {
    %fint = ptrtoint i64 (i64)* @g0 to i64
    %fptr = inttoptr i64 %fint to i64 (i64)*
    %res = call i64 (i64) %fptr(i64 0)
    ret i64 %res
}