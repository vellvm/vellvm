; Examples from the LLVM LangRef's 'call' Instruction section.
; langref: call-instruction sha1=ef850fcd27087fa2426d01c3a0d05b61b036394c
;
; LangRef 24.0.0git gives the following example(s):
;
; %retval = call i32 @test(i32 %argc)
; call i32 (ptr, ...) @printf(ptr %msg, i32 12, i8 42)        ; yields i32
; %X = tail call i32 @foo()                                    ; yields i32
; %Y = tail call fastcc i32 @foo()  ; yields i32
; call void %foo(i8 signext 97)
;
; %struct.A = type { i32, i8 }
; %r = call %struct.A @foo()                        ; yields { i32, i8 }
; %gr = extractvalue %struct.A %r, 0                ; yields i32
; %gr1 = extractvalue %struct.A %r, 1               ; yields i8
; %Z = call void @foo() noreturn                    ; indicates that %foo never returns normally
; %ZZ = call zeroext i32 @bar()                     ; Return value is %zero extended

%struct.A = type { i32, i8 }

define i32 @test(i32 %argc) {
  %r = add i32 %argc, 1
  ret i32 %r
}

define i32 @foo() {
  ret i32 12
}

define void @void_fn(i8 signext %c) {
  ret void
}

define %struct.A @make_a() {
  %a0 = insertvalue %struct.A poison, i32 4, 0
  %a1 = insertvalue %struct.A %a0, i8 2, 1
  ret %struct.A %a1
}

; %retval = call i32 @test(i32 %argc)
define i32 @direct_call(i32 %argc) {
  %retval = call i32 @test(i32 %argc)
  ret i32 %retval
}

; %X = tail call i32 @foo()
define i32 @tail_call() {
  %X = tail call i32 @foo()
  ret i32 %X
}

; %Y = tail call fastcc i32 @foo()
define i32 @tail_call_fastcc() {
  %Y = tail call fastcc i32 @foo()
  ret i32 %Y
}

; call void %foo(i8 signext 97) -- an indirect call through a function pointer.
define void @indirect_void_call(ptr %foo) {
  call void %foo(i8 signext 97)
  ret void
}

; %r  = call %struct.A @foo()
; %gr = extractvalue %struct.A %r, 0
; %gr1 = extractvalue %struct.A %r, 1
define i32 @call_struct_returning() {
  %r = call %struct.A @make_a()
  %gr = extractvalue %struct.A %r, 0
  %gr1 = extractvalue %struct.A %r, 1
  %w = zext i8 %gr1 to i32
  %sum = add i32 %gr, %w
  ret i32 %sum
}

; Assertion arguments are turned into dvalues without a global environment
; (assertion.ml's texp_to_dvalue), so @void_fn cannot be named in an assertion
; directly; the function pointer is supplied here instead.
define void @call_indirect_void() {
  call void @indirect_void_call(ptr @void_fn)
  ret void
}

; ASSERT EQ: i32 43 = call i32 @direct_call(i32 42)
; ASSERT EQ: i32 12 = call i32 @tail_call()
; ASSERT EQ: i32 12 = call i32 @tail_call_fastcc()
; ASSERT SUCCEEDS: call void @void_fn(i8 signext 97)
; ASSERT SUCCEEDS: call void @call_indirect_void()
; ASSERT EQ: i32 6 = call i32 @call_struct_returning()
