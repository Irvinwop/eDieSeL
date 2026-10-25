/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
/* Owned synthetic probes.
 * All executable assembly, including recovery and dispatch, is in one section.
 * No scratch/recovery GPR is reserved. No stack use with a guest RSP. */
.section .rex32_native,"ax",@progbits
.globl rex32_section_begin
rex32_section_begin:
.macro SNAPSHOT target
 movq %rax, \target+0(%rip)
 movq %rcx, \target+8(%rip)
 movq %rdx, \target+16(%rip)
 movq %rbx, \target+24(%rip)
 movq %rsp, \target+32(%rip)
 movq %rbp, \target+40(%rip)
 movq %rsi, \target+48(%rip)
 movq %rdi, \target+56(%rip)
 movq %r8, \target+64(%rip)
 movq %r9, \target+72(%rip)
 movq %r10, \target+80(%rip)
 movq %r11, \target+88(%rip)
 movq %r12, \target+96(%rip)
 movq %r13, \target+104(%rip)
 movq %r14, \target+112(%rip)
 movq %r15, \target+120(%rip)
.endm
.globl rex32_run
.type rex32_run,@function
rex32_run:
 movq %rsp, rex32_host_rsp(%rip)
 movq %rbx, rex32_host_saved(%rip)
 movq %rbp, rex32_host_saved+8(%rip)
 movq %r12, rex32_host_saved+16(%rip)
 movq %r13, rex32_host_saved+24(%rip)
 movq %r14, rex32_host_saved+32(%rip)
 movq %r15, rex32_host_saved+40(%rip)
 movq %rdi, rex32_window(%rip)
 pushfq
 popq rex32_host_flags(%rip)
 pushq rex32_input+128(%rip)
 popfq
 pushfq
 popq rex32_before+128(%rip)
 movq rex32_input+0(%rip), %rax
 movq rex32_input+8(%rip), %rcx
 movq rex32_input+16(%rip), %rdx
 movq rex32_input+24(%rip), %rbx
 movq rex32_input+32(%rip), %rsp
 movq rex32_input+40(%rip), %rbp
 movq rex32_input+48(%rip), %rsi
 movq rex32_input+56(%rip), %rdi
 movq rex32_input+64(%rip), %r8
 movq rex32_input+72(%rip), %r9
 movq rex32_input+80(%rip), %r10
 movq rex32_input+88(%rip), %r11
 movq rex32_input+96(%rip), %r12
 movq rex32_input+104(%rip), %r13
 movq rex32_input+112(%rip), %r14
 movq rex32_input+120(%rip), %r15
 SNAPSHOT rex32_before
 jmp *rex32_window(%rip)
.globl rex32_run_end
rex32_run_end:
.size rex32_run,.-rex32_run
.globl rex32_capture
.type rex32_capture,@function
rex32_capture:
 SNAPSHOT rex32_after
 /* Save measured guest RSP above, restore host stack before PUSHFQ. */
 movq rex32_host_rsp(%rip), %rsp
 pushfq
 popq rex32_after+128(%rip)
 pushq rex32_host_flags(%rip)
 popfq
 movq rex32_host_saved(%rip), %rbx
 movq rex32_host_saved+8(%rip), %rbp
 movq rex32_host_saved+16(%rip), %r12
 movq rex32_host_saved+24(%rip), %r13
 movq rex32_host_saved+32(%rip), %r14
 movq rex32_host_saved+40(%rip), %r15
 ret
.globl rex32_capture_end
rex32_capture_end:
.size rex32_capture,.-rex32_capture
.macro PROBE name,bytes:vararg
.globl rex32_\name
.globl rex32_\name\()_end
.globl rex32_\name\()_return_end
.type rex32_\name,@function
rex32_\name:
 .byte \bytes
rex32_\name\()_end:
 jmp rex32_capture
rex32_\name\()_return_end:
.size rex32_\name,.-rex32_\name
.endm
PROBE gcc29,0x44,0x8b,0x0c,0x86
PROBE gcc33,0x44,0x8b,0x04,0x87
PROBE clang39,0x41,0x8b,0x06
PROBE bank40,0x40,0x8b,0x07
PROBE bank41,0x41,0x8b,0x07
PROBE bank44,0x44,0x8b,0x07
PROBE bank45,0x45,0x8b,0x07
PROBE bank42,0x42,0x8b,0x04,0x27
PROBE bank43,0x43,0x8b,0x04,0x27
PROBE bank46,0x46,0x8b,0x04,0x27
PROBE bank47,0x47,0x8b,0x04,0x27
PROBE ignored_x42,0x42,0x8b,0x07
PROBE ignored_x43,0x43,0x8b,0x07
PROBE ignored_x46,0x46,0x8b,0x07
PROBE ignored_x47,0x47,0x8b,0x07
PROBE scale0,0x47,0x8b,0x64,0x25,0x7f
PROBE scale1,0x47,0x8b,0x64,0x65,0xff
PROBE scale2,0x47,0x8b,0x64,0xa5,0x80
PROBE scale3,0x47,0x8b,0x64,0xe5,0x00
PROBE rbpzero,0x40,0x8b,0x6d,0x00
PROBE r13zero,0x45,0x8b,0x6d,0x00
PROBE sibnoindex,0x45,0x8b,0x64,0xa5,0x80
PROBE noindex0,0x40,0x8b,0x44,0x24,0x00
PROBE noindex1,0x44,0x8b,0x4c,0x64,0xff
PROBE noindex3,0x45,0x8b,0x54,0xe5,0x7f
PROBE rspdest,0x40,0x8b,0x67,0x00
PROBE r12base,0x41,0x8b,0x44,0x24,0x00
PROBE basealias,0x45,0x8b,0x7f,0x00
PROBE indexalias,0x46,0x8b,0x0c,0x8f
PROBE allalias,0x40,0x8b,0x04,0x40
PROBE disp80,0x45,0x8b,0x47,0x80
PROBE dispff,0x45,0x8b,0x47,0xff
PROBE disp00,0x45,0x8b,0x47,0x00
PROBE disp7f,0x45,0x8b,0x47,0x7f
PROBE rspindex,0x42,0x8b,0x04,0x24
PROBE destbase,0x40,0x8b,0x34,0x86
PROBE destindex,0x40,0x8b,0x04,0x87
PROBE mut_direction,0x44,0x89,0x0c,0x86
PROBE mut_r,0x40,0x8b,0x0c,0x86
PROBE mut_b,0x40,0x8b,0x06
PROBE mut_x,0x45,0x8b,0x04,0x27
PROBE mut_width,0x4c,0x8b,0x0c,0x86
PROBE mut_scale,0x44,0x8b,0x0c,0x46
PROBE mut_disp,0x47,0x8b,0x64,0xa5,0x7f
PROBE mut_addr32,0x67,0x44,0x8b,0x0c,0x86
PROBE mut_word,0x66,0x44,0x8b,0x0c,0x86
PROBE mut_sign,0x4c,0x63,0x0c,0x86
PROBE mut_noindex,0x47,0x8b,0x64,0xa5,0x80
PROBE mut_guard8,0x49,0x8b,0x06
PROBE mut_rostore,0x41,0x89,0x06
PROBE mut_byte,0x41,0x0f,0xb6,0x06
PROBE mut_half,0x41,0x0f,0xb7,0x06
PROBE mut_norex,0x8b,0x0c,0x86
.globl rex32_section_end
rex32_section_end:
.bss
.balign 8
rex32_host_rsp: .zero 8
rex32_host_flags: .zero 8
rex32_host_saved: .zero 48
rex32_window: .zero 8
.section .note.GNU-stack,"",@progbits
