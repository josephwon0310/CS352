.text
#if (__APPLE__)
	.global _entry_point

_entry_point:
#else
	.global entry_point

entry_point:
#endif
	push %rbp	# save stack frame for C convention
	mov %rsp, %rbp

	# beginning generated code
	movq $3, %rbx
	movq %rbx, %rax
	movq $0, %rdx
	movq $2, %rcx
	idivq %rcx
	movq %rax, %rbx
	movq $4, %rcx
	addq %rcx, %rbx
	movq %rbx, %rax
	# end generated code
	# %rax contains the result

	mov %rbp, %rsp	# reset frame
	pop %rbp
	ret



