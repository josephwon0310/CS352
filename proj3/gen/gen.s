.text
.global putchar, getchar, entry_point

################# FUNCTIONS #####################
#################################################


###################### MAIN #####################
entry_point:
	pushq %rbp	# save stack frame for calling convention
	movq %rsp, %rbp
	movq %rdi, heap(%rip)
	movq $2, %rdi
	movq $0, %rsi
	jmp loop1_cond
loop1_body:
	movq %rdi, %rdx
	movq %rdi, %rcx
	imul %rcx, %rdx
	movq %rdx, %rdi
	movq %rsi, %rcx
	movq $1, %r8
	addq %r8, %rcx
	movq %rcx, %rsi
	movq %r8, %rcx
	movq %rcx, %rdx
loop1_cond:
	movq %rsi, %rdx
	movq $3, %rcx
	cmp %rcx, %rdx
	setl %al
	movzbq %al, %rdx
	movq $1, %rcx
	cmp %rdx, %rcx
	je if2_then
	movq %rsi, %rdx
	movq $4, %rcx
	cmp %rcx, %rdx
	setl %al
	movzbq %al, %rdx
	jmp if2_end
if2_then:
	movq $1, %rdx
if2_end:
	movq $1, %rcx
	cmp %rdx, %rcx
	je loop1_body
	movq %rdi, %rdx
	movq %rdx, %rsi
	movq %rsi, %rdi
	movq %rdi, %rax
	movq %rbp, %rsp	# reset frame
	popq %rbp
	ret
#################################################


#################### DATA #######################

.data
heap:	.quad 0
#################################################
