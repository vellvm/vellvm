declare  i8* @malloc(i8 )

declare  void @free(i8* )

define  i8 @main() {
b15:
    %v41 = add i8 4, 4
    %v42 = ashr i8 %v41, 6
    %v43 = call i8* (i8) @malloc(i8 102) 
    store i8 %v41, i8* %v43, align 1
    %v44 = getelementptr i8, i8* %v43, i32 0
    store i8 %v42, i8* %v44, align 1
    br i1 1, label %b16, label %b17

b16:
    call void (i8*) @free(i8* %v43) 
    store i8 %v41, i8* %v44, align 1
    %v45 = load i8, i8* %v44, align 1
    ret i8 %v45

b17:
    ret i8 %v41
}
