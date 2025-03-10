declare i32 @printf(i8*, ...)
@format = private constant [2 x i8] c"%d"

declare i32 @puts(i8*)

define  i8 @main() {
    %v0 = alloca i32
    store i32 0, i32* %v0, align 1
    %v1 = ptrtoint i32* %v0 to i64
    %v2 = inttoptr i64 %v1 to <{i8, i8, i8, i8}>*
    %v3 = load <{i8, i8, i8, i8}>, <{i8, i8, i8, i8}>* %v2, align 1
    %v4 = extractvalue <{i8, i8, i8, i8}> %v3, 2
    %v5 = alloca i8
    store i8 %v4, i8* %v5, align 1
    %result = call i32 @puts(i8* %v5)
    ret i8 %v4
}