/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* No stack access while arbitrary modeled RSP is installed; every owned
 * register-only window jumps directly to RIP-relative snapshot capture. */
.text
.globl edsl_logical_probe
.type edsl_logical_probe,@function
edsl_logical_probe:
    movq %rsp, edsl_logical_host_rsp(%rip)
    movq %rbx, edsl_logical_host_saved(%rip)
    movq %rbp, edsl_logical_host_saved+8(%rip)
    movq %r12, edsl_logical_host_saved+16(%rip)
    movq %r13, edsl_logical_host_saved+24(%rip)
    movq %r14, edsl_logical_host_saved+32(%rip)
    movq %r15, edsl_logical_host_saved+40(%rip)
    movq %rdi, edsl_logical_function(%rip)
    pushq edsl_logical_input+128(%rip)
    popfq
    pushfq
    popq edsl_logical_effective_flags(%rip)
    movq edsl_logical_input+0(%rip), %rax
    movq edsl_logical_input+8(%rip), %rcx
    movq edsl_logical_input+16(%rip), %rdx
    movq edsl_logical_input+24(%rip), %rbx
    movq edsl_logical_input+32(%rip), %rsp
    movq edsl_logical_input+40(%rip), %rbp
    movq edsl_logical_input+48(%rip), %rsi
    movq edsl_logical_input+56(%rip), %rdi
    movq edsl_logical_input+64(%rip), %r8
    movq edsl_logical_input+72(%rip), %r9
    movq edsl_logical_input+80(%rip), %r10
    movq edsl_logical_input+88(%rip), %r11
    movq edsl_logical_input+96(%rip), %r12
    movq edsl_logical_input+104(%rip), %r13
    movq edsl_logical_input+112(%rip), %r14
    movq edsl_logical_input+120(%rip), %r15
    jmp *edsl_logical_function(%rip)
.size edsl_logical_probe,.-edsl_logical_probe

.type edsl_logical_capture,@function
edsl_logical_capture:
    movq %rax, edsl_logical_output+0(%rip)
    movq %rcx, edsl_logical_output+8(%rip)
    movq %rdx, edsl_logical_output+16(%rip)
    movq %rbx, edsl_logical_output+24(%rip)
    movq %rsp, edsl_logical_output+32(%rip)
    movq %rbp, edsl_logical_output+40(%rip)
    movq %rsi, edsl_logical_output+48(%rip)
    movq %rdi, edsl_logical_output+56(%rip)
    movq %r8, edsl_logical_output+64(%rip)
    movq %r9, edsl_logical_output+72(%rip)
    movq %r10, edsl_logical_output+80(%rip)
    movq %r11, edsl_logical_output+88(%rip)
    movq %r12, edsl_logical_output+96(%rip)
    movq %r13, edsl_logical_output+104(%rip)
    movq %r14, edsl_logical_output+112(%rip)
    movq %r15, edsl_logical_output+120(%rip)
    movq edsl_logical_host_rsp(%rip), %rsp
    pushfq
    popq edsl_logical_output+128(%rip)
    cld
    movq edsl_logical_host_saved(%rip), %rbx
    movq edsl_logical_host_saved+8(%rip), %rbp
    movq edsl_logical_host_saved+16(%rip), %r12
    movq edsl_logical_host_saved+24(%rip), %r13
    movq edsl_logical_host_saved+32(%rip), %r14
    movq edsl_logical_host_saved+40(%rip), %r15
    ret
.size edsl_logical_capture,.-edsl_logical_capture

.bss
.balign 8
edsl_logical_host_rsp: .zero 8
edsl_logical_host_saved: .zero 48
edsl_logical_function: .zero 8

.section .edsl_logical64,"ax",@progbits
.globl edsl_logical_section_start
edsl_logical_section_start:
.macro PROBE name, bytes:vararg
.globl edsl_logical_\name
.globl edsl_logical_\name\()_end
.type edsl_logical_\name,@function
edsl_logical_\name:
.byte \bytes
edsl_logical_\name\()_end:
    jmp edsl_logical_capture
.size edsl_logical_\name,.-edsl_logical_\name
.endm
PROBE bank0,0x48,0x83,0xe0,0xf8
PROBE bank1,0x48,0x83,0xe1,0xf8
PROBE bank2,0x48,0x83,0xe2,0xf8
PROBE bank3,0x48,0x83,0xe3,0xf8
PROBE bank4,0x48,0x83,0xe4,0xf8
PROBE bank5,0x48,0x83,0xe5,0xf8
PROBE bank6,0x48,0x83,0xe6,0xf8
PROBE bank7,0x48,0x83,0xe7,0xf8
PROBE bank8,0x49,0x83,0xe0,0xf8
PROBE bank9,0x49,0x83,0xe1,0xf8
PROBE bank10,0x49,0x83,0xe2,0xf8
PROBE bank11,0x49,0x83,0xe3,0xf8
PROBE bank12,0x49,0x83,0xe4,0xf8
PROBE bank13,0x49,0x83,0xe5,0xf8
PROBE bank14,0x49,0x83,0xe6,0xf8
PROBE bank15,0x49,0x83,0xe7,0xf8
PROBE minus4,0x48,0x83,0xe1,0xfc
PROBE minus2,0x48,0x83,0xe2,0xfe
PROBE rsi_minus4,0x48,0x83,0xe6,0xfc
PROBE positive,0x48,0x83,0xe0,0x7f
PROBE negative,0x48,0x83,0xe0,0x80
PROBE identity,0x48,0x83,0xe0,0xff
PROBE zero,0x48,0x83,0xe0,0x0
PROBE one,0x48,0x83,0xe0,0x1
PROBE low3,0x48,0x83,0xe0,0x7
PROBE bad_width,0x83,0xe0,0xf8
PROBE bad_sign,0x48,0x81,0xe0,0xf8,0x00,0x00,0x00
PROBE bad_dest,0x48,0x83,0xe1,0xf8
PROBE bad_flags,0x48,0x83,0xe0,0xf8,0xf9
PROBE bad_op,0x48,0x83,0xc8,0xf8
.globl edsl_logical_section_end
edsl_logical_section_end:
.section .note.GNU-stack,"",@progbits
