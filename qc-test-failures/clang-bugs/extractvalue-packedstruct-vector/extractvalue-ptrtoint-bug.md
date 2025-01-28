# extractvalue with packed struct with vector bug?

This bug was initially discovered in this [issue](https://github.com/vellvm/vellvm/issues/283)

We believe there is an off-by-one error with code generation for the
extractvalue instruction when a vector is contained within a packed
structure. We have two example programs, one which exhibits what we
believe to be a miscompilation that uses a `<{<3 x i8>, i8}>`
structure, and one where we have replaced the vector with an array
type instead, and miscompilation does not occur.

- [ptrtoint2.ll](https://github.com/vellvm/vellvm/blob/dev/qc-test-failures/ptrtoint-roundtrip/ptrtoint2.ll), which uses `<{<3 x i8>, i8}>`. This one we believe miscompiles.
- [ptrtoint7.ll](https://github.com/vellvm/vellvm/blob/dev/qc-test-failures/ptrtoint-roundtrip/ptrtoint7.ll), which uses `<{[3 x i8], i8}>`. This gives us the behavior we expect.

The program which we believe miscompiles is as follows:

```
define  i8 @main() {
    %v0 = alloca i32
    store i32 0, i32* %v0, align 1
    %v1 = ptrtoint i32* %v0 to i64
    %v2 = inttoptr i64 %v1 to <{<3 x i8>, i8}>*
    %v3 = load <{<3 x i8>, i8}>, <{<3 x i8>, i8}>* %v2, align 1
    %v4 = extractvalue <{<3 x i8>, i8}> %v3, 1
    ret i8 %v4
}
```

We expect this to return 0, because we are essentially bitcasting a
32-bit 0 value to this 32-bit packed structure, and fetching the last
byte of it (which should be 0). After compiling this on an intel mac,
and an intel linux machine we get a different return value instead
(e.g., 46 is returned instead of 0 on the mac).

If we replace the vector with an array:

```
define  i8 @main() {
    %v0 = alloca i32
    store i32 0, i32* %v0, align 1
    %v1 = ptrtoint i32* %v0 to i64
    %v2 = inttoptr i64 %v1 to <{[3 x i8], i8}>*
    %v3 = load <{[3 x i8], i8}>, <{[3 x i8], i8}>* %v2, align 1
    %v4 = extractvalue <{[3 x i8], i8}> %v3, 1
    ret i8 %v4
}
```

We get the expected value of 0 on all platforms we've tried.

We believe that this is caused by an off-by-one error somewhere in the
code generation for extractvalue. For instance, we tried generating
RISC-V assembly code to see what code was generated for both of these
programs. Both the vector and array versions compile to identical
assembly language *except* for the load of the return value.

The vector version:

```
	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p1_m2p0_a2p1_c2p0_zmmul1p0"
	.file	"ptrtoint2.ll"
	.globl	main                            # -- Begin function main
	.p2align	1
	.type	main,@function
main:                                   # @main
	.cfi_startproc
# %bb.0:
	addi	sp, sp, -16
	.cfi_def_cfa_offset 16
	li	a0, 0
	sb	a0, 15(sp)
	sb	a0, 14(sp)
	sb	a0, 13(sp)
	sb	a0, 12(sp)
	lbu	a0, 16(sp)
	addi	sp, sp, 16
	ret
.Lfunc_end0:
	.size	main, .Lfunc_end0-main
	.cfi_endproc
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
	.addrsig
```

The array version:

```
	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p1_m2p0_a2p1_c2p0_zmmul1p0"
	.file	"ptrtoint7.ll"
	.globl	main                            # -- Begin function main
	.p2align	1
	.type	main,@function
main:                                   # @main
	.cfi_startproc
# %bb.0:
	addi	sp, sp, -16
	.cfi_def_cfa_offset 16
	li	a0, 0
	sb	a0, 15(sp)
	sb	a0, 14(sp)
	sb	a0, 13(sp)
	sb	a0, 12(sp)
	lbu	a0, 15(sp)
	addi	sp, sp, 16
	ret
.Lfunc_end0:
	.size	main, .Lfunc_end0-main
	.cfi_endproc
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
	.addrsig
```

In the vector version the instruction `lbu a0, 16(sp)` should be `lbu
a0, 15(sp)`, as in the array version. A similar issue can be seen in
the ARM code that's generated as well. Presumably something similar
happens in x86 as well, but there are larger differences between the
assembly files generated between the two files as well.

This test was ran using the following machines
- Clang 13
```
Homebrew clang version 13.0.1
Target: x86_64-apple-darwin21.6.0
Thread model: posix
InstalledDir: /usr/local/opt/llvm@13/bin
```
- Clang 19
```
Homebrew clang version 19.1.7
Target: x86_64-apple-darwin21.6.0
Thread model: posix
InstalledDir: /usr/local/Cellar/llvm/19.1.7/bin
Configuration file: /usr/local/etc/clang/x86_64-apple-darwin21.cfg
```

We believe that the structure in both of the examples should be of the same size as the `i32` value because of the following statements from the LLVM Language Reference:
- "In general vector elements are laid out in memory in the same way as array types. Such an analogy works fine as long as the vector elements are byte sized"
- "Structures may optionally be 'packed' structures, which indicate that the alignment of the struct is one byte, and that there is no padding between the elements."

Notice the following
- It is true that, according to this [mail](https://lists.llvm.org/pipermail/llvm-dev/2011-December/046257.html), that "`extractvalue` does not work on vectors, [and one] needs to use `extractelement` for them". However, the example in that code was directly extracting the element from the vector inside the packed struct using a single `extractvalue` call. This example is different, and is similar to the first few instructions of the example in the [mail](https://lists.llvm.org/pipermail/llvm-dev/2011-December/046257.html): our example does not directly load value from the vector inside the packed struct, but other elements inside the packed struct.
