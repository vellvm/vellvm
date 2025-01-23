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
	addi	sp, sp, -32
	.cfi_def_cfa_offset 32
	sd	ra, 24(sp)                      # 8-byte Folded Spill
	.cfi_offset ra, -8
	li	a0, 0
	sb	a0, 23(sp)
	sb	a0, 22(sp)
	sb	a0, 21(sp)
	sb	a0, 20(sp)
	lbu	a0, 23(sp)
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
