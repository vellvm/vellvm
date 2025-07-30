define void @foo() {
  %X = call i32 asm "bswap $0", "=r,r"(i32 0)
  call void asm sideeffect "eieio", ""()
  call void asm alignstack "eieio", ""()
  call void asm unwind "call func", ""()
  ret void
}
