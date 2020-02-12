.text
#if(__APPLE__)
	.global _entry_point

_entry_point:
#else
	.global entry_point

entry_point:
#endif
	push %rbp	# save stack frame for C convention
	mov %rsp, %rbp

	# beginning generated code
	movq $1, %rbx
	movq $2, %rcx
	cmpq %rcx, %rbx
	je if1
	movq $2, %rbx
	jmp end2
	if1:
	movq $1, %rbx
	end2:
	movq %rbx, %rax
	# end generated code
	# %rax contains the result

	mov %rbp, %rsp	# reset frame
	pop %rbp
	ret



