/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

struct capture { uint64_t gpr[16]; uint64_t flags; };
struct capture edsl_disp8_input, edsl_disp8_initial, edsl_disp8_output;
extern void edsl_disp8_probe(void (*)(void));
extern const unsigned char edsl_disp8_section_start[],edsl_disp8_section_end[];
#define DECLARE(n) extern void edsl_disp8_##n(void); extern const unsigned char edsl_disp8_##n##_end[];
DECLARE(load32) DECLARE(store32) DECLARE(load64) DECLARE(store64)
DECLARE(add32) DECLARE(add64) DECLARE(cmp8imm) DECLARE(cmp8left)
DECLARE(cmp32) DECLARE(cmp8right) DECLARE(cmp8rex) DECLARE(movzx)
DECLARE(movzxlong) DECLARE(r13zero) DECLARE(rspzero) DECLARE(rexindex)
DECLARE(noindex) DECLARE(scale0) DECLARE(scale1) DECLARE(scale3)
DECLARE(mutant_width) DECLARE(mutant_disp) DECLARE(mutant_bank) DECLARE(mutant_scale)
enum op {LOAD,STORE,ADD,CMPLEFT,CMPRIGHT,CMPI,MOVZX};
struct spec {const char *name; void (*start)(void); const unsigned char *end;
 enum op operation; unsigned width,destination,base; int index; unsigned scale; int disp;};
#define S(n,o,w,d,b,i,s,x) {#n,edsl_disp8_##n,edsl_disp8_##n##_end,o,w,d,b,i,s,x}
static const struct spec specs[]={
 S(load32,LOAD,4,1,7,-1,0,4), S(store32,STORE,4,1,7,-1,0,-4),
 S(load64,LOAD,8,0,7,-1,0,8), S(store64,STORE,8,0,7,-1,0,-8),
 S(add32,ADD,4,1,7,-1,0,4), S(add64,ADD,8,0,7,-1,0,16),
 S(cmp8imm,CMPI,1,0,7,0,0,1), S(cmp8left,CMPLEFT,1,1,7,-1,0,4),
 S(cmp32,CMPLEFT,4,1,7,-1,0,4), S(cmp8right,CMPRIGHT,1,1,7,-1,0,4),
 S(cmp8rex,CMPRIGHT,1,8,7,-1,0,4), S(movzx,MOVZX,1,1,7,-1,0,4),
 S(movzxlong,MOVZX,1,12,13,12,2,-128), S(r13zero,LOAD,8,13,13,-1,0,0),
 S(rspzero,LOAD,8,0,4,-1,0,0), S(rexindex,LOAD,8,12,13,12,2,-128),
 S(noindex,LOAD,8,12,13,-1,2,-128), S(scale0,LOAD,8,12,13,12,0,127),
 S(scale1,LOAD,8,12,13,12,1,-1), S(scale3,LOAD,8,12,13,12,3,0)};
static uint64_t mask(unsigned w){return w==8?UINT64_MAX:((UINT64_C(1)<<(w*8))-1);}
static uint64_t arithmetic(uint64_t old,uint64_t a,uint64_t b,unsigned width,int add){
 const unsigned bits=width*8; const uint64_t m=mask(width),sign=UINT64_C(1)<<(bits-1);
 a&=m;b&=m;uint64_t r=(add?a+b:a-b)&m;uint64_t f=old&~UINT64_C(0x8d5);
 int carry=add?(((__uint128_t)a+b)>m):(a<b);int overflow=add?((~(a^b)&(a^r)&sign)!=0):(((a^b)&(a^r)&sign)!=0);
 int parity=0;for(unsigned i=0;i<8;i++)parity^=(r>>i)&1;
 f|=(uint64_t)carry;f|=(uint64_t)!parity<<2;f|=(uint64_t)(((a^b^r)&16)!=0)<<4;
 f|=(uint64_t)(r==0)<<6;f|=(uint64_t)((r&sign)!=0)<<7;f|=(uint64_t)overflow<<11;return f;
}
/* Assembly labels identify addresses in this Linux x86-64 image. Bound integer
 * spans before converting to a length; the labels are separate C declarations. */
static int label_span(uintptr_t begin,uintptr_t end,size_t limit,size_t *length){
 if(end<=begin||end-begin>limit)return 0;*length=(size_t)(end-begin);return 1;
}
static int authenticate(const char *name){FILE *f=fopen(name,"rb");if(!f)return 0;
 size_t n;if(!label_span((uintptr_t)edsl_disp8_section_start,(uintptr_t)edsl_disp8_section_end,1048576,&n)){fclose(f);return 0;}unsigned char *p=malloc(n+1);if(!p){fclose(f);return 0;}size_t got=fread(p,1,n+1,f);int okay=got==n&&!ferror(f)&&memcmp(p,edsl_disp8_section_start,n)==0;fclose(f);free(p);return okay;}
static int observation(const struct spec *s,void (*actual)(void),unsigned seed,unsigned profile,unsigned char *page,size_t pageSize,int output){
 for(size_t i=0;i<pageSize;i++)page[i]=(unsigned char)(i*37+seed*61+19);
 unsigned char before[65536];if(pageSize>sizeof before)return 0;
 const size_t off=profile?pageSize-s->width:137;unsigned char *target=page+off;
 for(unsigned i=0;i<16;i++)edsl_disp8_input.gpr[i]=UINT64_C(0xa500000000000003)+i*UINT64_C(0x1111111111111)+seed;
 edsl_disp8_input.flags=0x602|((seed&1)?0x8d5:0)|((seed&2)?0x400:0);
 if(s->index>=0)edsl_disp8_input.gpr[s->index]=actual!=s->start?3:(seed?UINT64_C(0x100000003):UINT64_MAX);
 edsl_disp8_input.gpr[s->base]=(uint64_t)(uintptr_t)target-(int64_t)s->disp-
    (s->index>=0?(edsl_disp8_input.gpr[s->index]<<s->scale):0);
 if(s->operation==ADD)edsl_disp8_input.gpr[s->destination]=seed?UINT64_MAX:UINT64_C(0x7fffffffffffffff);
 /* Addition destinations never alias an address register in this bounded matrix. */
 if(s->operation==CMPI){target[0]=(seed&1)?0:0x80;}
 if(s->operation==ADD){for(unsigned i=0;i<s->width;i++)target[i]=(i==0)?1:0;}
 unsigned char original[24];memcpy(original,target-8,s->width+8);
 memcpy(before,page,pageSize);uint64_t operand=0;for(unsigned i=0;i<s->width;i++)operand|=(uint64_t)target[i]<<(8*i);
 int store=s->operation==STORE;if(!store&&mprotect(page,pageSize,PROT_READ)!=0)return 0;
 edsl_disp8_probe(actual);if(!store&&mprotect(page,pageSize,PROT_READ|PROT_WRITE)!=0)return 0;
 if(memcmp(edsl_disp8_initial.gpr,edsl_disp8_input.gpr,sizeof edsl_disp8_input.gpr)!=0){fprintf(stderr,"initial GPR mismatch\n");return 0;}
 uint64_t want[16];memcpy(want,edsl_disp8_initial.gpr,sizeof want);uint64_t flags=edsl_disp8_initial.flags;
 if(s->operation==LOAD||s->operation==MOVZX)want[s->destination]=operand;
 if(s->operation==STORE)for(unsigned i=0;i<s->width;i++)before[off+i]=(unsigned char)(want[s->destination]>>(8*i));
 if(s->operation==ADD){flags=arithmetic(flags,want[s->destination],operand,s->width,1);want[s->destination]=(want[s->destination]+operand)&mask(s->width);}
 if(s->operation==CMPLEFT)flags=arithmetic(flags,operand,want[s->destination],s->width,0);
 if(s->operation==CMPRIGHT)flags=arithmetic(flags,want[s->destination],operand,s->width,0);
 if(s->operation==CMPI)flags=arithmetic(flags,operand,0,1,0);
 int okay=memcmp(want,edsl_disp8_output.gpr,sizeof want)==0&&edsl_disp8_output.flags==flags&&memcmp(before,page,pageSize)==0;
 if(!okay){if(output)fprintf(stderr,"oracle mismatch %s/%u/%u\n",s->name,seed,profile);return 0;}
 if(output){size_t length;if(!label_span((uintptr_t)s->start,(uintptr_t)s->end,15,&length))return 0;
  printf("OBS %s %u %u %zu %"PRIu64" %u ",s->name,seed,profile,length,(uint64_t)(uintptr_t)target,s->width);
  for(size_t i=0;i<length;i++)printf("%02x",((const unsigned char*)(uintptr_t)s->start)[i]);
  for(unsigned i=0;i<16;i++)printf(" %"PRIu64,edsl_disp8_initial.gpr[i]);printf(" %"PRIu64,edsl_disp8_initial.flags);
  for(unsigned i=0;i<16;i++)printf(" %"PRIu64,edsl_disp8_output.gpr[i]);printf(" %"PRIu64,edsl_disp8_output.flags);
  printf(" ");for(unsigned i=0;i<s->width;i++)printf("%02x",(s->operation==STORE)?(unsigned char)(operand>>(8*i)):target[i]);
  printf(" ");for(unsigned i=0;i<s->width+8;i++)printf("%02x",original[i]);
  printf(" ");for(int i=-8;i<(int)s->width;i++)printf("%02x",target[i]);
  printf("\n");}
 return 1;
}
int main(int argc,char **argv){setvbuf(stdout,NULL,_IOLBF,0);if(argc!=2||!authenticate(argv[1])){fprintf(stderr,"linked-section extraction mismatch\n");return 2;}
 long p=sysconf(_SC_PAGESIZE);if(p<4096||p>65536)return 2;size_t ps=(size_t)p;
 unsigned char *mapping=mmap(NULL,ps*3,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);if(mapping==MAP_FAILED)return 2;
 unsigned char *page=mapping+ps;if(mprotect(page,ps,PROT_READ|PROT_WRITE)!=0)return 2;
 puts("EDSL-DISP8-V1");unsigned count=0;for(size_t i=0;i<sizeof specs/sizeof *specs;i++)for(unsigned seed=0;seed<2;seed++)for(unsigned profile=0;profile<2;profile++){
   if(!observation(&specs[i],specs[i].start,seed,profile,page,ps,1))return 1;count++;}
 unsigned rejected=0;void (*mutants[])(void)={edsl_disp8_mutant_width,edsl_disp8_mutant_disp,edsl_disp8_mutant_bank,edsl_disp8_mutant_scale};
 for(unsigned i=0;i<4;i++){const struct spec *s=&specs[i==3?15:2];if(observation(s,mutants[i],1,0,page,ps,0))return 1;rejected++;}
 printf("END %u %u\n",count,rejected);munmap(mapping,ps*3);return 0;}
