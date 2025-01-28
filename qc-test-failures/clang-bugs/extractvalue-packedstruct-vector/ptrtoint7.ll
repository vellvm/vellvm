define  i8 @main() {
    %v0 = alloca i32
    store i32 0, i32* %v0, align 1
    %v1 = ptrtoint i32* %v0 to i64
    %v2 = inttoptr i64 %v1 to <{[3 x i8], i8}>*
    %v3 = load <{[3 x i8], i8}>, <{[3 x i8], i8}>* %v2, align 1
    %v4 = extractvalue <{[3 x i8], i8}> %v3, 1
    ret i8 %v4
}