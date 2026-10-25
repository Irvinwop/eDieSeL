/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct snapshot { uint64_t registers[16],flags; };
_Static_assert(sizeof(struct snapshot)==136 && offsetof(struct snapshot,flags)==128,"snapshot ABI");
struct snapshot edsl_logical_input,edsl_logical_output;
uint64_t edsl_logical_effective_flags;
extern void edsl_logical_probe(const unsigned char *);
extern const unsigned char edsl_logical_section_start[],edsl_logical_section_end[];
struct contract { const char *name;const unsigned char *code,*end; unsigned destination,immediate; };
#include "cases.h"
/* Assembly labels are separate declarations: compare their linked integer
 * addresses instead of subtracting unrelated C pointers. Linux x86-64 uses
 * flat uintptr_t code addresses and size_t can represent their difference. */
_Static_assert(sizeof(size_t)>=sizeof(uintptr_t),"linked address size");
static size_t window_length(const unsigned char *first,const unsigned char *last) {
    uintptr_t start=(uintptr_t)first,end=(uintptr_t)last;
    if(end<start || end-start==SIZE_MAX)exit(2);
    return (size_t)(end-start);
}
static uint64_t result_for(uint64_t old,unsigned byte) {
    uint64_t result=0;
    for(unsigned k=0;k<64;k++) {
        unsigned mask_bit=k<8 ? (byte>>k)%2 : byte>=128;
        if((old>>k)%2 && mask_bit)result+=UINT64_C(1)<<k;
    }
    return result;
}
static uint64_t flags_for(uint64_t old,uint64_t result) {
    uint64_t flags=old&~UINT64_C(0x8d5);unsigned pop=0;
    for(unsigned k=0;k<8;k++)pop+=(result>>k)%2;
    if(pop%2==0)flags|=4;
    if(result==0)flags|=0x40;
    if(result>INT64_MAX)flags|=0x80;
    return flags;
}
static void words(const uint64_t *p,unsigned n) {printf("[");for(unsigned i=0;i<n;i++)printf("%s%"PRIu64,i?",":"",p[i]);printf("]");}
static int probe(const struct contract *c,unsigned v,int emit) {
    static const uint64_t old[]={UINT64_MAX,UINT64_C(0x800000010000000f),7,UINT64_C(0x100000008)};
    for(unsigned k=0;k<16;k++)edsl_logical_input.registers[k]=UINT64_C(0xfeed000100000001)+k*UINT64_C(0x10101010101);
    edsl_logical_input.registers[c->destination]=old[v];
    edsl_logical_input.flags=v%2?0xed7:0x202;
    struct snapshot expected=edsl_logical_input;
    uint64_t result=result_for(expected.registers[c->destination],c->immediate);
    expected.registers[c->destination]=result;
    edsl_logical_probe(c->code);
    expected.flags=flags_for(edsl_logical_effective_flags,result);
    int ok=memcmp(expected.registers,edsl_logical_output.registers,128)==0 &&
       (expected.flags&~UINT64_C(0x10))==(edsl_logical_output.flags&~UINT64_C(0x10));
    if(!emit)return ok;
    if(!ok){fprintf(stderr,"FAIL %s/%u\n",c->name,v);return 0;}
    printf("{\"name\":\"%s_%u\",\"bytes\":[",c->name,v);
    for(size_t i=0;i<window_length(c->code,c->end);i++)printf("%s%u",i?",":"",c->code[i]);
    printf("],\"pc\":%"PRIuPTR",\"next\":%"PRIuPTR",\"requestedFlags\":%"PRIu64",\"effectiveFlags\":%"PRIu64",\"requestedInstalledGPRs\":",(uintptr_t)c->code,(uintptr_t)c->end,edsl_logical_input.flags,edsl_logical_effective_flags);
    words(edsl_logical_input.registers,16);printf(",\"measuredPostGPRs\":");words(edsl_logical_output.registers,16);
    printf(",\"measuredPostFlags\":%"PRIu64"}\n",edsl_logical_output.flags);return 1;
}
int main(int argc,char **argv) {
    if(argc!=2)return 2;
    FILE *f=fopen(argv[1],"rb");if(!f)return 2;
    size_t n=window_length(edsl_logical_section_start,edsl_logical_section_end);unsigned char *bytes=malloc(n+1);if(!bytes)return 2;
    size_t got=fread(bytes,1,n+1,f);int bad=ferror(f);fclose(f);
    if(bad||got!=n||memcmp(bytes,edsl_logical_section_start,n)){fputs("linked extraction mismatch\n",stderr);return 2;}free(bytes);
    for(size_t i=0;i<sizeof positives/sizeof positives[0];i++)for(unsigned v=0;v<4;v++)if(!probe(&positives[i],v,1))return 1;
    for(size_t i=0;i<sizeof mutants/sizeof mutants[0];i++){unsigned v=0;for(;v<4;v++)if(!probe(&mutants[i],v,0))break;if(v==4)return 1;fprintf(stderr,"REJECTED %s vector %u\n",mutants[i].name,v);}
    fprintf(stderr,"PASS 100 selected observations; all 16 GPRs, effective defined flags, nonarithmetic flag frame; only AF masked\n");return 0;
}
