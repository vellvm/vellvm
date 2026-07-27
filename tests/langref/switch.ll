; Examples from the LLVM LangRef's 'switch' Instruction section.
; langref: switch-instruction sha1=9e7d56363fe2560a77378a31510b3b009e13a871
;
; LangRef 24.0.0git gives the following example(s):
;
; ; Emulate a conditional br instruction
; %Val = zext i1 %value to i32
; switch i32 %Val, label %truedest [ i32 0, label %falsedest ]
;
; ; Emulate an unconditional br instruction
; switch i32 0, label %dest [ ]
;
; ; Implement a jump table:
; switch i32 %val, label %otherwise [ i32 0, label %onzero
;                                     i32 1, label %onone
;                                     i32 2, label %ontwo ]

; Emulate a conditional br instruction.
define i32 @emulate_cond_br(i1 %value) {
  %Val = zext i1 %value to i32
  switch i32 %Val, label %truedest [ i32 0, label %falsedest ]
truedest:
  ret i32 1
falsedest:
  ret i32 0
}

; Emulate an unconditional br instruction.
define i32 @emulate_uncond_br() {
  switch i32 0, label %dest [ ]
dest:
  ret i32 7
}

; Implement a jump table.
define i32 @jump_table(i32 %val) {
  switch i32 %val, label %otherwise [ i32 0, label %onzero
                                      i32 1, label %onone
                                      i32 2, label %ontwo ]
onzero:
  ret i32 100
onone:
  ret i32 101
ontwo:
  ret i32 102
otherwise:
  ret i32 -1
}

; ASSERT EQ: i32 1 = call i32 @emulate_cond_br(i1 1)
; ASSERT EQ: i32 0 = call i32 @emulate_cond_br(i1 0)
; ASSERT EQ: i32 7 = call i32 @emulate_uncond_br()
; ASSERT EQ: i32 100 = call i32 @jump_table(i32 0)
; ASSERT EQ: i32 101 = call i32 @jump_table(i32 1)
; ASSERT EQ: i32 102 = call i32 @jump_table(i32 2)
; ASSERT EQ: i32 -1 = call i32 @jump_table(i32 3)
