# extractvalue with packed struct with vector bug?

This bug is reflected on this [issue](https://github.com/vellvm/vellvm/issues/283)

The files that most intuitively reflected the bug are `ptrtoint2.ll`, which uses `<{<3 x i8>, i8}>`, and `ptrtoint7.ll`, which uses `<{[3 x i8], i8}>`.

Here we state the program from `ptrtoint2.ll`. `ptrtoint7.ll` is almost identical, except the aforementioned difference.

```
declare i32 @puts(i8*)

define  i8 @main() {
    %v0 = alloca i32
    store i32 0, i32* %v0, align 1
    %v1 = ptrtoint i32* %v0 to i64
    %v2 = inttoptr i64 %v1 to <{<3 x i8>, i8}>*
    %v3 = load <{<3 x i8>, i8}>, <{<3 x i8>, i8}>* %v2, align 1
    %v4 = extractvalue <{<3 x i8>, i8}> %v3, 1
    %v5 = alloca i8
    store i8 %v4, i8* %v5, align 1
    %result = call i32 @puts(i8* %v5)
    ret i8 %v4
}
```

The bug can be roughly described as follows.
- `bitcast` an `i32` value into an packed struct with the same size (i.e., 32-bit), where the first few bytes are in vector form.
- load the last byte of the packed struct using `extractvalue`

Here, we uses an external function `puts` just so that we can visually see the difference between `ptrtoint2.ll` and `ptrtoint7.ll`. One can also use other ways to "unzero" the other memory address to see the difference.

When running these two examples, we can get the following output
- `ptrtoint2.ll`
    - clang: 46 (or some random value)
	- vellvm: 0
- `ptrtoint7.ll`
    - clang: 0
	- vellvm: 0
	
One can observe the error by compiling these two programs into assembly, ideally `RISC-V`. The code in `RISC-V`, as suggested in the issue, suggests an off-by-one error for `extractvalue` with packed struct with vector:

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
	addi	sp, sp, -32
	.cfi_def_cfa_offset 32
	sd	ra, 24(sp)                      # 8-byte Folded Spill
	.cfi_offset ra, -8
	li	a0, 0
	sb	a0, 23(sp)
	sb	a0, 22(sp)
	sb	a0, 21(sp)
	sb	a0, 20(sp)
	lbu	a0, 24(sp)
	sd	a0, 8(sp)                       # 8-byte Folded Spill
	sb	a0, 19(sp)
	addi	a0, sp, 19
	call	puts
                                        # kill: def $x11 killed $x10
	ld	a0, 8(sp)                       # 8-byte Folded Reload
	ld	ra, 24(sp)                      # 8-byte Folded Reload
	addi	sp, sp, 32
	ret
.Lfunc_end0:
	.size	main, .Lfunc_end0-main
	.cfi_endproc
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym puts
```
specifically, the instruction `lbu a0, 24(sp)` should be incorrect. Instead, we want `lbu a0, 23(sp)`, which we can get from `ptrtoint7.ll`.

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

The struct in the example should be of the same size as the `i32` value because of the following hints on the LLVM Language Reference
- "In general vector elements are laid out in memory in the same way as array types. Such an analogy works fine as long as the vector elements are byte sized"
- "Structures may optionally be 'packed' structures, which indicate that the alignment of the struct is one byte, and that there is no padding between the elements."

Notice the following
- It is true that, according to this [mail](https://lists.llvm.org/pipermail/llvm-dev/2011-December/046257.html), that "`extractvalue` does not work on vectors, [and one] needs to use `extractelemen` for them". However, the example in that code was directly extracting the element from the vector inside the packed struct using a single `extractvalue` call. However, this example is different, and is similar to the first few instructions of the example in the [mail](https://lists.llvm.org/pipermail/llvm-dev/2011-December/046257.html): our example does not directly load value from the vector inside the packed struct, but other elements inside the packed struct. Therefore, one should
