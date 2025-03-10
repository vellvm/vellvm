# extractvalue wrong vector bug
This bug is confirmed in this [bug report](https://bugs.llvm.org/show_bug.cgi?id=49942)

`extractelement1.ll` provides an example of this bug. 
```
@g0 = global <7 x i1> <i1 false, i1 false, i1 false, i1 true, i1 false, i1 true, i1 false>

define i8 @main() {
b11:
  %v46 = load <7 x i1>, <7 x i1>* @g0, align 1
  %v47 = extractelement <7 x i1> %v46, i32 6
  %v49 = ashr i8 -2, 6
  %common.ret.op = select i1 %v47, i8 %v49, i8 -6
  ret i8 %common.ret.op
}
```
This program first fetch an element from the vector, then branching to select the corresponding value. In this case, we would hope the code to output 255 (-1), but clang will produce 250 (-6).

When compiled down to RISC-V using Clang-13, we get the following assembly:
```
main:
	.cfi_startproc
	addi	sp, sp, -16
	.cfi_def_cfa_offset 16
	lui	a0, %hi(g0)
	lb	a0, %lo(g0)(a0)
	srli	a0, a0, 3
	andi	a0, a0, 1
	addi	a1, zero, -6
	sd	a1, 0(sp)
	addi	a2, zero, -1
	mv	a1, zero
	sd	a2, 8(sp)
	bne	a0, a1, .LBB0_2
	ld	a0, 0(sp)
	sd	a0, 8(sp)
.LBB0_2:
	ld	a0, 8(sp)
	addi	sp, sp, 16
	ret
...	
	.type	g0,@object
	.section	.sdata,"aw",@progbits
	.globl	g0
	.p2align	3
g0:
	.byte	0
	.byte	0
	.byte	0
	.byte	1
	.byte	0
	.byte	1
	.byte	0
	.zero	1
	.size	g0, 8
```

What seems to cause the problem is the third instruction (i.e., `srli a0, a0, 3`). This instruction shift the value stored in the address by `3`. Because the bytes are either `0` or `1`, `0` will be returned, and will always caused the code to select the first branch. This [file](./extractelement3.ll) demonstrates that. In this file, we switched the index `3` with `2`, and vellvm and clang exhibits the same behavior (-6).


This bug exists in the following configuration:
```
Homebrew clang version 13.0.1
Target: x86_64-apple-darwin21.6.0
Thread model: posix
InstalledDir: /usr/local/opt/llvm@13/bin
```

It can no longer be reproduced in the following configuration:
```
Homebrew clang version 19.1.7
Target: x86_64-apple-darwin21.6.0
Thread model: posix
InstalledDir: /usr/local/Cellar/llvm/19.1.7/bin
Configuration file: /usr/local/etc/clang/x86_64-apple-darwin21.cfg
```
This is mainly due to the fact that the assembly code is optimized away.
