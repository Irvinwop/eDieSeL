/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Derived from sequential-arithmetic64-probe.S. Single-threaded, non-reentrant.
 * NO stack access while the arbitrary modeled RSP is installed. MOV and JMP
 * leave flags alone; restore host RSP BEFORE PUSHFQ. All windows are owned. */
.text
.globl edsl_sub64_probe
.type edsl_sub64_probe,@function
edsl_sub64_probe:
    movq %rsp, edsl_sub64_host_rsp(%rip)
    pushfq
    popq edsl_sub64_host_flags(%rip)
    movq %rbx, edsl_sub64_host_saved(%rip)
    movq %rbp, edsl_sub64_host_saved+8(%rip)
    movq %r12, edsl_sub64_host_saved+16(%rip)
    movq %r13, edsl_sub64_host_saved+24(%rip)
    movq %r14, edsl_sub64_host_saved+32(%rip)
    movq %r15, edsl_sub64_host_saved+40(%rip)
    movq %rdi, edsl_sub64_function(%rip)
    pushq edsl_sub64_input+128(%rip)
    popfq
    pushfq
    popq edsl_sub64_effective_flags(%rip)
    movq edsl_sub64_input+0(%rip), %rax
    movq edsl_sub64_input+8(%rip), %rcx
    movq edsl_sub64_input+16(%rip), %rdx
    movq edsl_sub64_input+24(%rip), %rbx
    movq edsl_sub64_input+32(%rip), %rsp
    movq edsl_sub64_input+40(%rip), %rbp
    movq edsl_sub64_input+48(%rip), %rsi
    movq edsl_sub64_input+56(%rip), %rdi
    movq edsl_sub64_input+64(%rip), %r8
    movq edsl_sub64_input+72(%rip), %r9
    movq edsl_sub64_input+80(%rip), %r10
    movq edsl_sub64_input+88(%rip), %r11
    movq edsl_sub64_input+96(%rip), %r12
    movq edsl_sub64_input+104(%rip), %r13
    movq edsl_sub64_input+112(%rip), %r14
    movq edsl_sub64_input+120(%rip), %r15
    jmp *edsl_sub64_function(%rip)
.size edsl_sub64_probe,.-edsl_sub64_probe

.type edsl_sub64_capture,@function
edsl_sub64_capture:
    movq %rax, edsl_sub64_output+0(%rip)
    movq %rcx, edsl_sub64_output+8(%rip)
    movq %rdx, edsl_sub64_output+16(%rip)
    movq %rbx, edsl_sub64_output+24(%rip)
    movq %rsp, edsl_sub64_output+32(%rip)
    movq %rbp, edsl_sub64_output+40(%rip)
    movq %rsi, edsl_sub64_output+48(%rip)
    movq %rdi, edsl_sub64_output+56(%rip)
    movq %r8, edsl_sub64_output+64(%rip)
    movq %r9, edsl_sub64_output+72(%rip)
    movq %r10, edsl_sub64_output+80(%rip)
    movq %r11, edsl_sub64_output+88(%rip)
    movq %r12, edsl_sub64_output+96(%rip)
    movq %r13, edsl_sub64_output+104(%rip)
    movq %r14, edsl_sub64_output+112(%rip)
    movq %r15, edsl_sub64_output+120(%rip)
    movq edsl_sub64_host_rsp(%rip), %rsp
    pushfq
    popq edsl_sub64_output+128(%rip)
    cld
    incq edsl_sub64_probe_count(%rip)
    movq edsl_sub64_host_saved(%rip), %rbx
    movq edsl_sub64_host_saved+8(%rip), %rbp
    movq edsl_sub64_host_saved+16(%rip), %r12
    movq edsl_sub64_host_saved+24(%rip), %r13
    movq edsl_sub64_host_saved+32(%rip), %r14
    movq edsl_sub64_host_saved+40(%rip), %r15
    pushq edsl_sub64_host_flags(%rip)
    popfq
    ret
.size edsl_sub64_capture,.-edsl_sub64_capture

.bss
.balign 8
edsl_sub64_host_rsp: .zero 8
edsl_sub64_host_flags: .zero 8
edsl_sub64_host_saved: .zero 48
edsl_sub64_function: .zero 8

.section .edsl_sub64,"ax",@progbits
.globl edsl_sub64_section_start
edsl_sub64_section_start:
.macro PROBE name, bytes:vararg
.globl edsl_sub64_\name
.globl edsl_sub64_\name\()_end
.type edsl_sub64_\name,@function
edsl_sub64_\name:
.byte \bytes
edsl_sub64_\name\()_end:
    jmp edsl_sub64_capture
.size edsl_sub64_\name,.-edsl_sub64_\name
.endm
.macro SUB29 name,destination,source
    PROBE \name,(0x48 | ((\source >> 3) << 2) | (\destination >> 3)),0x29,(0xc0 | ((\source & 7) << 3) | (\destination & 7))
.endm
.macro SUB2B name,destination,source
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | (\source >> 3)),0x2b,(0xc0 | ((\destination & 7) << 3) | (\source & 7))
.endm
SUB29 r29_0,0,1
SUB29 r29_1,1,10
SUB29 r29_2,2,3
SUB29 r29_3,3,12
SUB29 r29_4,4,5
SUB29 r29_5,5,14
SUB29 r29_6,6,7
SUB29 r29_7,7,8
SUB29 r29_8,8,9
SUB29 r29_9,9,2
SUB29 r29_10,10,11
SUB29 r29_11,11,4
SUB29 r29_12,12,13
SUB29 r29_13,13,6
SUB29 r29_14,14,15
SUB29 r29_15,15,0
SUB2B r2b_0,0,15
SUB2B r2b_1,1,0
SUB2B r2b_2,2,9
SUB2B r2b_3,3,2
SUB2B r2b_4,4,11
SUB2B r2b_5,5,4
SUB2B r2b_6,6,13
SUB2B r2b_7,7,6
SUB2B r2b_8,8,7
SUB2B r2b_9,9,8
SUB2B r2b_10,10,1
SUB2B r2b_11,11,10
SUB2B r2b_12,12,3
SUB2B r2b_13,13,12
SUB2B r2b_14,14,5
SUB2B r2b_15,15,14
SUB29 alias0,0,0
SUB2B alias3,3,3
SUB29 alias4,4,4
SUB2B alias7,7,7
SUB29 alias8,8,8
SUB2B alias11,11,11
SUB29 alias12,12,12
SUB2B alias15,15,15
/* X ignored, every R/B combination, both opcode directions. */
PROBE x29_0,0x4a,0x29,0xd8
PROBE x29_1,0x4b,0x29,0xd8
PROBE x29_2,0x4e,0x29,0xd8
PROBE x29_3,0x4f,0x29,0xd8
PROBE x2b_0,0x4a,0x2b,0xd8
PROBE x2b_1,0x4b,0x2b,0xd8
PROBE x2b_2,0x4e,0x2b,0xd8
PROBE x2b_3,0x4f,0x2b,0xd8
.macro SUBI name,destination,immediate
    PROBE \name,(0x48 | (\destination >> 3)),0x83,(0xe8 | (\destination & 7)),(\immediate & 255)
.endm
SUBI imm0,0,-128
SUBI imm1,1,-1
SUBI imm2,2,0
SUBI imm3,3,1
SUBI imm4,4,127
SUBI imm5,5,-128
SUBI imm6,6,-1
SUBI imm7,7,0
SUBI imm8,8,1
SUBI imm9,9,127
SUBI imm10,10,-128
SUBI imm11,11,-1
SUBI imm12,12,0
SUBI imm13,13,1
SUBI imm14,14,127
SUBI imm15,15,-128
SUBI rsp_min,4,-128
SUBI rsp_neg1,4,-1
SUBI r12_one,12,1
SUBI r12_max,12,127
/* Safe owned register-only mutations, excluded from positive replay. */
PROBE mutant_source,0x48,0x29,0xd0
PROBE mutant_direction,0x48,0x2b,0xc8
PROBE mutant_width,0x29,0xc8
PROBE mutant_add,0x48,0x01,0xc8
PROBE mutant_no_write,0x48,0x39,0xc8
PROBE mutant_carry,0x48,0x29,0xc8,0xf8
PROBE mutant_zero_extend,0x48,0x81,0xe8,0xff,0x00,0x00,0x00
PROBE mutant_bank,0x48,0x83,0xe8,0xff
.globl edsl_sub64_section_end
edsl_sub64_section_end:
.section .note.GNU-stack,"",@progbits
