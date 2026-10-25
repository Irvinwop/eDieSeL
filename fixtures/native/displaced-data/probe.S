/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Single-threaded owned windows. Recovery uses only RIP-relative storage, so
 * no GPR hides a recovery pointer and RSP may be an arbitrary input or result.
 * The entire executable section, including harness and jumps, is authenticated
 * against the supplied final-ELF extraction before the first probe. */
.section .edsl_disp8,"ax",@progbits
.globl edsl_disp8_section_start
edsl_disp8_section_start:

.macro SNAPSHOT name
    movq %rax, \name+0(%rip)
    movq %rcx, \name+8(%rip)
    movq %rdx, \name+16(%rip)
    movq %rbx, \name+24(%rip)
    movq %rsp, \name+32(%rip)
    movq %rbp, \name+40(%rip)
    movq %rsi, \name+48(%rip)
    movq %rdi, \name+56(%rip)
    movq %r8, \name+64(%rip)
    movq %r9, \name+72(%rip)
    movq %r10, \name+80(%rip)
    movq %r11, \name+88(%rip)
    movq %r12, \name+96(%rip)
    movq %r13, \name+104(%rip)
    movq %r14, \name+112(%rip)
    movq %r15, \name+120(%rip)
.endm
.globl edsl_disp8_probe
.type edsl_disp8_probe,@function
edsl_disp8_probe:
    movq %rsp, host_rsp(%rip)
    movq %rbx, host_saved(%rip)
    movq %rbp, host_saved+8(%rip)
    movq %r12, host_saved+16(%rip)
    movq %r13, host_saved+24(%rip)
    movq %r14, host_saved+32(%rip)
    movq %r15, host_saved+40(%rip)
    movq %rdi, window(%rip)
    pushfq
    popq host_flags(%rip)
    pushq edsl_disp8_input+128(%rip)
    popfq
    pushfq
    popq edsl_disp8_initial+128(%rip)
    movq edsl_disp8_input+0(%rip), %rax
    movq edsl_disp8_input+8(%rip), %rcx
    movq edsl_disp8_input+16(%rip), %rdx
    movq edsl_disp8_input+24(%rip), %rbx
    movq edsl_disp8_input+32(%rip), %rsp
    movq edsl_disp8_input+40(%rip), %rbp
    movq edsl_disp8_input+48(%rip), %rsi
    movq edsl_disp8_input+56(%rip), %rdi
    movq edsl_disp8_input+64(%rip), %r8
    movq edsl_disp8_input+72(%rip), %r9
    movq edsl_disp8_input+80(%rip), %r10
    movq edsl_disp8_input+88(%rip), %r11
    movq edsl_disp8_input+96(%rip), %r12
    movq edsl_disp8_input+104(%rip), %r13
    movq edsl_disp8_input+112(%rip), %r14
    movq edsl_disp8_input+120(%rip), %r15
    SNAPSHOT edsl_disp8_initial
    jmp *window(%rip)
.size edsl_disp8_probe,.-edsl_disp8_probe

.type capture,@function
capture:
    SNAPSHOT edsl_disp8_output
    /* MOV restores the real CALL stack before PUSHFQ. No stack access has
     * occurred since installing the arbitrary RSP, even for ADD RSP,[...]. */
    movq host_rsp(%rip), %rsp
    pushfq
    popq edsl_disp8_output+128(%rip)
    pushq host_flags(%rip)
    popfq
    movq host_saved(%rip), %rbx
    movq host_saved+8(%rip), %rbp
    movq host_saved+16(%rip), %r12
    movq host_saved+24(%rip), %r13
    movq host_saved+32(%rip), %r14
    movq host_saved+40(%rip), %r15
    ret
.size capture,.-capture

.macro BEGIN name
.globl edsl_disp8_\name
.globl edsl_disp8_\name\()_end
.type edsl_disp8_\name,@function
edsl_disp8_\name:
.endm
.macro END name
edsl_disp8_\name\()_end:
    jmp capture
.size edsl_disp8_\name,.-edsl_disp8_\name
.endm
.macro PROBE name, bytes:vararg
    BEGIN \name
    .byte \bytes
    END \name
.endm
.macro BASE name,destination,base
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | (\base >> 3)),0x03,(((\destination & 7) << 3) | (\base & 7))
.endm
.macro INDEX name,destination,base,index,scale
    PROBE \name,(0x48 | ((\destination >> 3) << 2) | ((\index >> 3) << 1) | (\base >> 3)),0x03,(((\destination & 7) << 3) | 4),((\scale << 6) | ((\index & 7) << 3) | (\base & 7))
.endm
PROBE load32,0x8b,0x4f,0x4
PROBE store32,0x89,0x4f,0xfc
PROBE load64,0x48,0x8b,0x47,0x8
PROBE store64,0x48,0x89,0x47,0xf8
PROBE add32,0x3,0x4f,0x4
PROBE add64,0x48,0x3,0x47,0x10
PROBE cmp8imm,0x80,0x7c,0x7,0x1,0x0
PROBE cmp8left,0x38,0x4f,0x4
PROBE cmp32,0x39,0x4f,0x4
PROBE cmp8right,0x3a,0x4f,0x4
PROBE cmp8rex,0x44,0x3a,0x47,0x4
PROBE movzx,0xf,0xb6,0x4f,0x4
PROBE movzxlong,0x47,0xf,0xb6,0x64,0xa5,0x80
PROBE r13zero,0x4d,0x8b,0x6d,0x0
PROBE rspzero,0x48,0x8b,0x44,0x24,0x0
PROBE rexindex,0x4f,0x8b,0x64,0xa5,0x80
PROBE noindex,0x4d,0x8b,0x64,0xa5,0x80
PROBE scale0,0x4f,0x8b,0x64,0x25,0x7f
PROBE scale1,0x4f,0x8b,0x64,0x65,0xff
PROBE scale3,0x4f,0x8b,0x64,0xe5,0x0
PROBE mutant_width,0x8b,0x47,8
PROBE mutant_disp,0x48,0x8b,0x47,0x18
PROBE mutant_bank,0x4c,0x8b,0x47,8
PROBE mutant_scale,0x4f,0x8b,0x64,0x65,0x80
.globl edsl_disp8_section_end
edsl_disp8_section_end:

.bss
.balign 8
host_rsp: .zero 8
host_flags: .zero 8
host_saved: .zero 48
window: .zero 8
scratch: .zero 8
.section .note.GNU-stack,"",@progbits
