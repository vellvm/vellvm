; Examples from the LLVM LangRef's 'freeze' Instruction section.
; langref: freeze-instruction sha1=313d92fe59f4b0c20580579e0f62d6b0785bc24c
;
; LangRef 24.0.0git gives the following example(s):
;
; %w = i32 undef
; %x = freeze i32 %w
; %y = add i32 %w, %w         ; undef
; %z = add i32 %x, %x         ; even number because all uses of %x observe
;                             ; the same value
; %x2 = freeze i32 %w
; %cmp = icmp eq i32 %x, %x2  ; can be true or false
;
; ; example with vectors
; %v = <2 x i32> <i32 undef, i32 poison>
; %a = extractelement <2 x i32> %v, i64 0    ; undef
; %b = extractelement <2 x i32> %v, i64 1    ; poison
; %add = add i32 %a, %a                      ; undef
;
; %v.fr = freeze <2 x i32> %v                ; element-wise freeze
; %d = extractelement <2 x i32> %v.fr, i64 0 ; not undef
; %add.f = add i32 %d, %d                    ; even number
;
; %l = load b32, ptr %p                      ; may be uninitialized
; %f = freeze b32 %l                         ; freezes on a per-bit basis
;
; ; branching on frozen value
; %poison = add nsw i1 %k, undef   ; poison
; %c = freeze i1 %poison
; br i1 %c, label %foo, label %bar ; non-deterministic branch to %foo or %bar

; LangRef's examples are mostly about non-determinism, which a single
; ASSERT EQ cannot pin down. What is deterministic is that freeze turns
; poison and undef into *some* fixed value: two uses of one freeze always
; observe the same bits, so %x - %x is 0 and %x == %x is true.

; %z = add i32 %x, %x -- an even number, because both uses of %x observe the
; same value. Subtracting instead gives the sharper, target-independent 0.
define i32 @frozen_is_stable() {
  %w = add i32 undef, 0
  %x = freeze i32 %w
  %z = sub i32 %x, %x
  ret i32 %z
}

; Without the freeze the two uses need not agree, so this is left unasserted:
;   %y = add i32 %w, %w         ; undef

; %cmp = icmp eq i32 %x, %x2 -- can be true or false, since %x and %x2 are two
; independent freezes of the same undef. Comparing one freeze against itself
; is instead always true.
define i1 @frozen_eq_self() {
  %w = add i32 undef, 0
  %x = freeze i32 %w
  %cmp = icmp eq i32 %x, %x
  ret i1 %cmp
}

; freeze of poison is likewise an ordinary value: it is no longer poison, so
; arithmetic on it does not propagate poison.
define i1 @freeze_kills_poison() {
  %poison = shl i32 1, 32
  %c = freeze i32 %poison
  %d = icmp eq i32 %c, %c
  ret i1 %d
}

; ASSERT EQ: i32 0 = call i32 @frozen_is_stable()
; ASSERT EQ: i1 1 = call i1 @frozen_eq_self()
; ASSERT EQ: i1 1 = call i1 @freeze_kills_poison()
