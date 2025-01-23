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
