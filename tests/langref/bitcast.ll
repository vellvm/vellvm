; Examples from the LLVM LangRef's 'bitcast .. to' Instruction section.
; langref: bitcast-to-instruction sha1=9316b45f3917bb38562760644ac82ebf4b8c6403
;
; LangRef 24.0.0git gives the following example(s):
;
; %X = bitcast i8 255 to i8         ; yields i8 :-1
; %Y = bitcast i32* %x to i16*      ; yields i16*:%x
; %Z = bitcast <2 x i32> %V to i64; ; yields i64: %V (depends on endianness)
; %Z = bitcast <2 x i32*> %V to <2 x i64*> ; yields <2 x i64*>
;
; ; considering %bi to hold an integer and %bp to hold a pointer,
; %a = bitcast b64 %bi to i64       ; returns an integer, no-op cast
; %b = bitcast b64 %bp to i64       ; reinterprets the pointer as an integer, returning its address without exposing provenance
; %c = bitcast b64 %bp to ptr       ; returns a pointer, no-op cast
; %d = bitcast b64 %bi to ptr       ; reinterprets the integer as a pointer, returning a pointer with no provenance
;
; %e = bitcast <2 x b32> %v to i64  ; reinterprets the raw bytes as an integer
; %f = bitcast <2 x b32> %v to ptr  ; reinterprets the raw bytes as a pointer
;
; %g = bitcast <2 x b32> %v to <4 x i16> ; reinterprets the raw bytes as integers

; A no-op cast between two types of the same width; the bits are unchanged,
; so i8 255 read back as i8 is -1.
define i8 @bitcast_255() {
  %X = bitcast i8 255 to i8
  ret i8 %X
}

; ASSERT EQ: i8 -1 = call i8 @bitcast_255()
