/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { register_count = 16, vectors = 10, positive_windows = 68 };
struct snapshot { uint64_t registers[register_count]; uint64_t flags; };
_Static_assert(offsetof(struct snapshot, flags) == 128 && sizeof(struct snapshot) == 136,
    "Assembly snapshot ABI changed");
struct snapshot edsl_sub64_input, edsl_sub64_output;
uint64_t edsl_sub64_effective_flags, edsl_sub64_probe_count;
extern void edsl_sub64_probe(const unsigned char *);
extern const unsigned char edsl_sub64_section_start[], edsl_sub64_section_end[];

enum operation { subtract_register, subtract_immediate };
struct request {
    const char *name;
    const unsigned char *code, *end;
    enum operation operation;
    unsigned int destination, source;
    int immediate;
};
/* Independently authored requests. NO opcode/REX/ModRM decoder is used by the
 * oracle, value selection, expected states, or expected flags. These numbers
 * name architectural registers in the snapshot ABI, not byte-derived fields. */
#define REQUESTS(X) \
    X(r29_0,subtract_register,0,1,0) \
    X(r29_1,subtract_register,1,10,0) \
    X(r29_2,subtract_register,2,3,0) \
    X(r29_3,subtract_register,3,12,0) \
    X(r29_4,subtract_register,4,5,0) \
    X(r29_5,subtract_register,5,14,0) \
    X(r29_6,subtract_register,6,7,0) \
    X(r29_7,subtract_register,7,8,0) \
    X(r29_8,subtract_register,8,9,0) \
    X(r29_9,subtract_register,9,2,0) \
    X(r29_10,subtract_register,10,11,0) \
    X(r29_11,subtract_register,11,4,0) \
    X(r29_12,subtract_register,12,13,0) \
    X(r29_13,subtract_register,13,6,0) \
    X(r29_14,subtract_register,14,15,0) \
    X(r29_15,subtract_register,15,0,0) \
    X(r2b_0,subtract_register,0,15,0) \
    X(r2b_1,subtract_register,1,0,0) \
    X(r2b_2,subtract_register,2,9,0) \
    X(r2b_3,subtract_register,3,2,0) \
    X(r2b_4,subtract_register,4,11,0) \
    X(r2b_5,subtract_register,5,4,0) \
    X(r2b_6,subtract_register,6,13,0) \
    X(r2b_7,subtract_register,7,6,0) \
    X(r2b_8,subtract_register,8,7,0) \
    X(r2b_9,subtract_register,9,8,0) \
    X(r2b_10,subtract_register,10,1,0) \
    X(r2b_11,subtract_register,11,10,0) \
    X(r2b_12,subtract_register,12,3,0) \
    X(r2b_13,subtract_register,13,12,0) \
    X(r2b_14,subtract_register,14,5,0) \
    X(r2b_15,subtract_register,15,14,0) \
    X(alias0,subtract_register,0,0,0) \
    X(alias3,subtract_register,3,3,0) \
    X(alias4,subtract_register,4,4,0) \
    X(alias7,subtract_register,7,7,0) \
    X(alias8,subtract_register,8,8,0) \
    X(alias11,subtract_register,11,11,0) \
    X(alias12,subtract_register,12,12,0) \
    X(alias15,subtract_register,15,15,0) \
    X(x29_0,subtract_register,0,3,0) \
    X(x29_1,subtract_register,8,3,0) \
    X(x29_2,subtract_register,0,11,0) \
    X(x29_3,subtract_register,8,11,0) \
    X(x2b_0,subtract_register,3,0,0) \
    X(x2b_1,subtract_register,3,8,0) \
    X(x2b_2,subtract_register,11,0,0) \
    X(x2b_3,subtract_register,11,8,0) \
    X(imm0,subtract_immediate,0,0,-128) \
    X(imm1,subtract_immediate,1,0,-1) \
    X(imm2,subtract_immediate,2,0,0) \
    X(imm3,subtract_immediate,3,0,1) \
    X(imm4,subtract_immediate,4,0,127) \
    X(imm5,subtract_immediate,5,0,-128) \
    X(imm6,subtract_immediate,6,0,-1) \
    X(imm7,subtract_immediate,7,0,0) \
    X(imm8,subtract_immediate,8,0,1) \
    X(imm9,subtract_immediate,9,0,127) \
    X(imm10,subtract_immediate,10,0,-128) \
    X(imm11,subtract_immediate,11,0,-1) \
    X(imm12,subtract_immediate,12,0,0) \
    X(imm13,subtract_immediate,13,0,1) \
    X(imm14,subtract_immediate,14,0,127) \
    X(imm15,subtract_immediate,15,0,-128) \
    X(rsp_min,subtract_immediate,4,0,-128) \
    X(rsp_neg1,subtract_immediate,4,0,-1) \
    X(r12_one,subtract_immediate,12,0,1) \
    X(r12_max,subtract_immediate,12,0,127)
#define MUTANTS(X) \
    X(mutant_source,subtract_register,0,1,0) \
    X(mutant_direction,subtract_register,0,1,0) \
    X(mutant_width,subtract_register,0,1,0) \
    X(mutant_add,subtract_register,0,1,0) \
    X(mutant_no_write,subtract_register,0,1,0) \
    X(mutant_carry,subtract_register,0,1,0) \
    X(mutant_zero_extend,subtract_immediate,0,0,-1) \
    X(mutant_bank,subtract_immediate,8,0,-1)
#define DECLARE(N,K,D,S,I) extern const unsigned char edsl_sub64_##N[], edsl_sub64_##N##_end[];
REQUESTS(DECLARE)
MUTANTS(DECLARE)
#define INITIALIZE(N,K,D,S,I) {#N,edsl_sub64_##N,edsl_sub64_##N##_end,K,D,S,I},
static const struct request requests[] = { REQUESTS(INITIALIZE) };
static const struct request mutants[] = { MUTANTS(INITIALIZE) };
_Static_assert(sizeof requests / sizeof requests[0] == positive_windows, "Window bound changed");

/* 65-bit nonnegative modular difference, unsigned borrow, nibble borrow,
 * population count, and an independent signed mathematical interval for OF.
 * No host signed overflow or implementation-defined unsigned-to-signed cast. */
static uint64_t subtract_flags(uint64_t old, uint64_t left, uint64_t right, uint64_t *value)
{
    const __uint128_t modulus = (__uint128_t)1 << 64;
    uint64_t result = (uint64_t)((__uint128_t)left + modulus - (__uint128_t)right);
    __int128 signed_left = (__int128)left - (left > INT64_MAX ? (__int128)modulus : 0);
    __int128 signed_right = (__int128)right - (right > INT64_MAX ? (__int128)modulus : 0);
    __int128 difference = signed_left - signed_right;
    unsigned int population = 0;
    for (unsigned int bit = 0; bit < 8; ++bit) population += (unsigned int)((result >> bit) & 1);
    uint64_t flags = old & ~UINT64_C(0x8d5);
    if (left < right) flags |= UINT64_C(1);
    if (population % 2 == 0) flags |= UINT64_C(4);
    if (left % 16 < right % 16) flags |= UINT64_C(0x10);
    if (result == 0) flags |= UINT64_C(0x40);
    if (result > INT64_MAX) flags |= UINT64_C(0x80);
    if (difference < -((__int128)1 << 63) || difference > INT64_MAX) flags |= UINT64_C(0x800);
    *value = result;
    return flags;
}

struct observation { struct snapshot before, after; uint64_t effective_flags; };
static struct observation observations[positive_windows][vectors];
static int run_case(const struct request *request, unsigned int vector, struct observation *record)
{
    static const uint64_t left[vectors] = {
        0, 0, UINT64_C(0x8000000000000000), INT64_MAX, 0x10, 0x10,
        UINT64_C(0x100000000), UINT64_C(0xfeedface89abcdef), UINT64_MAX, 1
    };
    static const uint64_t right[vectors] = {
        0, 1, 1, UINT64_MAX, 1, 0xf,
        UINT64_C(0xffffffff), UINT64_C(0x1122334455667788), 0, 2
    };
    static const uint64_t immediate_left[vectors] = {
        0, 1, UINT64_C(0x8000000000000000), INT64_MAX, 0x10, 0xf,
        UINT64_C(0x100000000), UINT64_C(0xfeedface89abcdef), UINT64_MAX, 0x80
    };
    for (unsigned int i = 0; i < register_count; ++i)
        edsl_sub64_input.registers[i] = (vector % 2 ? UINT64_C(0x8000000000000001)
            : UINT64_C(0x100000001)) + i * UINT64_C(0x0101010101010111);
    edsl_sub64_input.registers[request->destination] = request->operation == subtract_immediate
        ? immediate_left[vector] : left[vector];
    if (request->operation == subtract_register && request->source != request->destination)
        edsl_sub64_input.registers[request->source] = right[vector];
    edsl_sub64_input.flags = vector % 2 ? 0xed7 : 0x202;
    struct snapshot expected = edsl_sub64_input;
    uint64_t before_left = edsl_sub64_input.registers[request->destination];
    uint64_t before_right = request->operation == subtract_immediate
        ? (uint64_t)(int64_t)request->immediate : edsl_sub64_input.registers[request->source];
    struct snapshot before = edsl_sub64_input;
    edsl_sub64_probe(request->code);
    expected.flags = subtract_flags(edsl_sub64_effective_flags, before_left, before_right,
        &expected.registers[request->destination]);
    if (record) *record = (struct observation){ before, edsl_sub64_output, edsl_sub64_effective_flags };
    return memcmp(expected.registers, edsl_sub64_output.registers, sizeof expected.registers) == 0 &&
        expected.flags == edsl_sub64_output.flags;
}

static void words(FILE *file, const uint64_t *values, size_t count, int quoted)
{
    fputc('[',file);
    for (size_t i = 0; i < count; ++i)
        fprintf(file,quoted ? "%s\"%" PRIu64 "\"" : "%s%" PRIu64,i ? "," : "",values[i]);
    fputc(']',file);
}
static void bytes(FILE *file, const unsigned char *values, size_t count)
{
    fputc('[',file);
    for (size_t i = 0; i < count; ++i) fprintf(file,"%s%u",i ? "," : "",(unsigned int)values[i]);
    fputc(']',file);
}
static void emit_header(void)
{
    puts("/- Finite CPU snapshots; independently checked C requests, not universal ISA evidence. -/\n"
        "import EDSL.X86.Sequential.MachineChoices\nimport EDSL.Audit\n"
        "set_option autoImplicit false\nset_option warningAsError true\n"
        "set_option maxHeartbeats 300000\nset_option maxRecDepth 128\n"
        "namespace EDSL.Tests.NativeSequentialSub64\nopen EDSL.X86\n"
        "def allRegisters : List Register := [.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,"
        ".r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]\n"
        "def entry (code : List Byte) (pc : Word) (registers : List Word) (flags : Word) : State where\n"
        "  registers r := registers.getD (allRegisters.idxOf r) 0\n  rip := pc\n  flags := flags\n"
        "  memory := {\n"
        "    read := fun a => if pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length\n"
        "      then code[a.toNat - pc.toNat]? else none\n"
        "    executable := fun a => decide (pc.toNat ≤ a.toNat ∧ a.toNat < pc.toNat + code.length)\n"
        "    writable := fun _ => false }\n"
        "def observe (initial : State) : Option (List Word × Word × Word × List Sequential.Read) := do\n"
        "  let observation ← (Sequential.stepWith ⟨true,false,true,false,true,false⟩ initial).toOption\n"
        "  match observation.result with\n"
        "  | .next final => return (allRegisters.map final.registers,final.flags,final.rip,observation.reads)\n"
        "  | _ => none\n-- BEGIN OBSERVATIONS");
}
static void emit_observation(FILE *json, const struct request *request, unsigned int vector,
    const struct observation *record)
{
    size_t length = (size_t)((uintptr_t)request->end - (uintptr_t)request->code);
    printf("theorem observed_%s_%u : observe (entry ",request->name,vector);
    bytes(stdout,request->code,length);
    printf(" %" PRIuPTR " ",(uintptr_t)request->code);
    words(stdout,record->before.registers,register_count,0);
    printf(" %" PRIu64 ") = some (",record->effective_flags);
    words(stdout,record->after.registers,register_count,0);
    printf(",%" PRIu64 ",%" PRIuPTR ",[]) := by decide\n",record->after.flags,(uintptr_t)request->end);
    fprintf(json,"{\"name\":\"%s\",\"vector\":%u,\"operation\":\"%s\",\"destination\":%u,"
        "\"source\":%u,\"immediate\":%d,\"pc\":\"%" PRIuPTR "\",\"end\":\"%" PRIuPTR "\",\"bytes\":",
        request->name,vector,request->operation==subtract_register ? "register" : "immediate",
        request->destination,request->source,request->immediate,(uintptr_t)request->code,(uintptr_t)request->end);
    bytes(json,request->code,length);
    fputs(",\"before\":",json); words(json,record->before.registers,register_count,1);
    fputs(",\"after\":",json); words(json,record->after.registers,register_count,1);
    fprintf(json,",\"requestedFlags\":\"%" PRIu64 "\",\"effectiveFlags\":\"%" PRIu64
        "\",\"afterFlags\":\"%" PRIu64 "\"}\n",
        record->before.flags,record->effective_flags,record->after.flags);
}

int main(int argc, char **argv)
{
    if (argc != 3) return 2;
    FILE *file = fopen(argv[1],"rb");
    if (!file) return 2;
    size_t size = (size_t)((uintptr_t)edsl_sub64_section_end - (uintptr_t)edsl_sub64_section_start);
    unsigned char *extracted = malloc(size + 1);
    if (!extracted) { fclose(file); return 2; }
    size_t amount = fread(extracted,1,size+1,file);
    int failed = ferror(file);
    fclose(file);
    if (failed || amount != size || memcmp(extracted,edsl_sub64_section_start,size) != 0) {
        fprintf(stderr,"Final ELF section extraction differs from executed bytes (probes=%" PRIu64
            "; observations=0)\n",edsl_sub64_probe_count);
        free(extracted); return 2;
    }
    free(extracted);
    /* No Lean/JSON output and no probes before this exact-section gate. */
    sigset_t blocked, old_mask;
    if (sigfillset(&blocked) || sigprocmask(SIG_BLOCK,&blocked,&old_mask)) return 2;
    for (size_t i = 0; i < positive_windows; ++i)
        for (unsigned int v = 0; v < vectors; ++v)
            if (!run_case(&requests[i],v,&observations[i][v])) {
                fprintf(stderr,"Independent native contract failed: %s/%u\n",requests[i].name,v);
                return 1;
            }
    for (size_t i = 0; i < sizeof mutants / sizeof mutants[0]; ++i) {
        unsigned int v;
        for (v=0; v<vectors; ++v) if (!run_case(&mutants[i],v,NULL)) break;
        if (v==vectors) { fprintf(stderr,"Owned mutant unexpectedly accepted: %s\n",mutants[i].name); return 1; }
        fprintf(stderr,"REJECTED owned mutant: %s (vector %u)\n",mutants[i].name,v);
    }
    if (sigprocmask(SIG_SETMASK,&old_mask,NULL)) return 2;
    FILE *json = fopen(argv[2],"wx");
    if (!json) return 2;
    emit_header();
    for (size_t i = 0; i < positive_windows; ++i)
        for (unsigned int v = 0; v < vectors; ++v) emit_observation(json,&requests[i],v,&observations[i][v]);
    puts("-- END OBSERVATIONS\nend EDSL.Tests.NativeSequentialSub64\n#audit_edsl");
    if (fclose(json) || fflush(stdout) || ferror(stdout)) return 2;
    fprintf(stderr,"Checked 680 positive CPU observations across 68 windows; rejected 8 owned mutants; "
        "total probes=%" PRIu64 "; full final ELF section matched (%zu bytes)\n",edsl_sub64_probe_count,size);
    return 0;
}
