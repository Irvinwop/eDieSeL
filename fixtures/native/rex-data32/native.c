/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include "common.h"

struct capture rex32_input,rex32_before,rex32_after;
static unsigned char *pages[MAP_COUNT];
static struct capture *planned_capture;

static void map_pages(void){
 if(sysconf(_SC_PAGESIZE)!=PAGE_BYTES)fail("host page size must be 4096");
 for(unsigned j=0;j<MAP_COUNT;j++){
  void *want=(void *)(page_addresses[j]-PAGE_BYTES);
  void *p=mmap(want,PAGE_BYTES*3,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED_NOREPLACE,-1,0);
  if(p==MAP_FAILED || p!=want)fail("fixed owned operand/decoy mapping");
  pages[j]=(unsigned char *)p+PAGE_BYTES;
  if(mprotect(pages[j],PAGE_BYTES,PROT_READ|PROT_WRITE))fail("operand mapping writable initialization");
 }
 if(page_addresses[0]<=UINT32_MAX || (uint32_t)page_addresses[0]!=page_addresses[1])fail("above-4GiB/low32 decoy witness");
}
static unsigned permissions(uintptr_t address){
 FILE *f=fopen("/proc/self/maps","r");if(!f)fail("read actual mapping permissions");
 char line[1024],perms[5];unsigned long a,b;unsigned result=UINT_MAX,found=0;
 while(fgets(line,sizeof line,f)){
  if(sscanf(line,"%lx-%lx %4s",&a,&b,perms)==3 && address>=a && address<b){
   result=(perms[0]=='r'?1u:0u)|(perms[1]=='w'?2u:0u)|(perms[2]=='x'?4u:0u);found++;
  }
 }if(ferror(f) || fclose(f) || found!=1)fail("actual mapping permission lookup");return result;
}
static void protect_pages(unsigned operand_permission){
 for(unsigned j=0;j<MAP_COUNT;j++){
  unsigned perm=j?PROT_READ:operand_permission;
  if(mprotect(pages[j],PAGE_BYTES,(int)perm))fail("set operand/decoy permissions");
  if(permissions(page_addresses[j])!=perm || permissions(page_addresses[j]-PAGE_BYTES)!=0 || permissions(page_addresses[j]+PAGE_BYTES)!=0)fail("operand/decoy page or guard permission");
 }
}
static uint64_t inverse_odd(uint64_t n){
 /* Only used to arrange the input of the base=index=destination case. */
 uint64_t x=1;for(unsigned i=0;i<6;i++)x*=2-n*x;return x;
}
static uintptr_t arrange(const struct spec *s,unsigned seed,unsigned profile,int control){
 size_t off=profile?PAGE_BYTES-4:1027+32*seed;uintptr_t target=page_addresses[0]+off;
 const uint32_t values[2]={UINT32_C(0xe19b37a5),UINT32_C(0x8c62d4f1)};
 for(unsigned j=0;j<MAP_COUNT;j++){
  if(mprotect(pages[j],PAGE_BYTES,PROT_READ|PROT_WRITE))fail("reset page initialization permission");
  for(size_t i=0;i<PAGE_BYTES;i++)pages[j][i]=(unsigned char)((i*37+(i/32)*71+seed*61+j*83+19)^(i/257));
  uint32_t word=j==0?values[seed]:j==1?UINT32_C(0x6d2ca781):UINT32_C(0x7253b6e8);
  memcpy(pages[j]+off,&word,sizeof word);
  if(off+8<=PAGE_BYTES){uint32_t high=UINT32_C(0x5a1fc3d8);memcpy(pages[j]+off+4,&high,4);}
 }
 for(unsigned i=0;i<16;i++)rex32_input.gpr[i]=UINT64_C(0xa501030507090b0d)+i*UINT64_C(0x01020304050607)+seed;
 rex32_input.flags=UINT64_C(0x202)|(seed?STATUS_MASK:0);
 if(s->index>=0 && s->base==(unsigned)s->index){
  uint64_t factor=1+(UINT64_C(1)<<s->scale);
  rex32_input.gpr[s->base]=(target-(uint64_t)(int64_t)s->disp)*inverse_odd(factor);
 }else{
  uint64_t index=control?3:UINT64_C(0x100000003)+seed*UINT64_C(0x100000002);
  if(s->index>=0)rex32_input.gpr[s->index]=index;
  uint64_t term=s->index<0?0:index<<s->scale;
  rex32_input.gpr[s->base]=target-(uint64_t)(int64_t)s->disp-term;
  unsigned partner=s->base^8;
  if(s->index<0 || partner!=(unsigned)s->index)rex32_input.gpr[partner]=page_addresses[2]+off-(uint64_t)(int64_t)s->disp-term;
  if(s->index>=0){
   unsigned other=(unsigned)s->index^8;
   if(other!=s->base && other!=s->dest && other!=partner)rex32_input.gpr[other]=index+5;
  }
 }
 if(control && !strcmp(s->name,"sibnoindex"))rex32_input.gpr[12]=3;
 return target;
}
static unsigned observe(struct record *r,size_t expected,size_t actual,unsigned seed,unsigned profile,int writable,int control){
 const struct spec *s=&specs[expected],*a=&specs[actual];memset(r,0,sizeof *r);
 uintptr_t target=arrange(s,seed,profile,control);
 r->f[F_CASE]=expected;r->f[F_ACTUAL]=actual;r->f[F_SEED]=seed;r->f[F_PROFILE]=profile;
 size_t length;if(!span((uintptr_t)a->start,(uintptr_t)a->end,15,&length))fail("actual integer probe span");
 r->f[F_LENGTH]=length;r->f[F_START]=(uintptr_t)a->start;r->f[F_END]=(uintptr_t)a->end;
 r->f[F_DEST]=s->dest;r->f[F_BASE]=s->base;r->f[F_INDEX]=(uint64_t)(int64_t)s->index;r->f[F_SCALE]=s->scale;r->f[F_DISP]=(uint64_t)(int64_t)s->disp;
 r->f[F_OPERAND]=target;r->f[F_REQUESTED]=rex32_input.flags;r->f[F_SUCCESSOR]=(uintptr_t)a->end;
 unsigned char code[8]={0};memcpy(code,(void *)(uintptr_t)a->start,length);r->f[F_CODE]=get64(code);
 for(unsigned j=0;j<MAP_COUNT;j++){
  r->f[F_MAP0+j]=page_addresses[j];r->f[F_PERM0+j]=j?PROT_READ:writable?(PROT_READ|PROT_WRITE):PROT_READ;
  memcpy(r->before[j],pages[j],PAGE_BYTES);
 }
 protect_pages(writable?(PROT_READ|PROT_WRITE):PROT_READ);
 if(planned_capture)*planned_capture=rex32_input;
 rex32_run(a->start);
 /* Snapshot output pages while they retain their observed access permissions. */
 for(unsigned j=0;j<MAP_COUNT;j++)memcpy(r->after[j],pages[j],PAGE_BYTES);
 memcpy(r->f+F_PRE,rex32_before.gpr,sizeof rex32_before.gpr);
 memcpy(r->f+F_POST,rex32_after.gpr,sizeof rex32_after.gpr);
 r->f[F_FLAGS_BEFORE]=rex32_before.flags;r->f[F_FLAGS_AFTER]=rex32_after.flags;r->f[F_READY]=1;
 unsigned mismatch=oracle(r,s->dest,target);
 if(memcmp(rex32_before.gpr,rex32_input.gpr,sizeof rex32_input.gpr) || ((rex32_before.flags^rex32_input.flags)&STATUS_MASK))mismatch|=8;
 for(unsigned j=0;j<MAP_COUNT;j++)if(mprotect(pages[j],PAGE_BYTES,PROT_READ|PROT_WRITE))fail("reset page permission after capture");
 return mismatch;
}
static void trailer(unsigned char *p,uint64_t n){memcpy(p,"ENDR32V1",8);put64(p+8,n);}
void capture_all(const char *path){
 map_pages();size_t n=HEADER_BYTES+RECORD_COUNT*RECORD_BYTES+16;
 unsigned char *out=calloc(1,n);if(!out)fail("capture allocation");make_header(out,RECORD_COUNT);
 struct record r;unsigned ord=0;
 for(size_t i=0;i<POSITIVES;i++)for(unsigned seed=0;seed<2;seed++)for(unsigned profile=0;profile<2;profile++){
  unsigned mismatch=observe(&r,i,i,seed,profile,0,0);r.f[F_ORD]=ord;
  encode_record(out+HEADER_BYTES+ord*RECORD_BYTES,&r);
  if(mismatch){char path_failure[128];snprintf(path_failure,sizeof path_failure,"failures/positive-%u.bin",ord);write_file(path_failure,out,HEADER_BYTES+(ord+1)*RECORD_BYTES);fprintf(stderr,"positive oracle mismatch %s/%u/%u mask=%u\n",specs[i].name,seed,profile,mismatch);fail("positive native oracle");}
  ord++;
 }
 trailer(out+n-16,ord);write_file(path,out,n);unsigned char sha[32];digest(out,n,sha);free(out);
 printf("Captured %u native observations; all 16 GPRs, full measured flags, three complete page frames; SHA256=",ord);hex_print(stdout,sha,32);puts("");
}
static size_t find_spec(const char *name){for(size_t i=0;i<spec_count;i++)if(!strcmp(specs[i].name,name))return i;fail("unknown control probe");return 0;}
struct shared_control {struct record record;struct capture planned;unsigned mismatch;};
void native_controls(void){
 map_pages();
 static const struct control {const char *mutant,*expected;unsigned profile,writable;int signal_expected;} controls[]={
  {"mut_direction","gcc29",0,1,0},{"mut_r","gcc29",0,0,0},
  {"mut_b","clang39",0,0,0},{"mut_x","bank47",0,0,0},
  {"mut_width","gcc29",0,0,0},{"mut_scale","gcc29",0,0,0},
  {"mut_disp","scale2",0,0,0},{"mut_addr32","gcc29",0,0,0},
  {"mut_word","gcc29",0,0,0},{"mut_sign","gcc29",0,0,0},
  {"mut_noindex","sibnoindex",0,0,0},{"mut_guard8","clang39",1,0,SIGSEGV},
  {"mut_rostore","clang39",0,0,SIGSEGV},{"mut_byte","clang39",0,0,0},
  {"mut_half","clang39",0,0,0},{"mut_norex","gcc29",0,0,0}
 };
 FILE *json=fopen("NATIVE-CONTROLS.json","w");if(!json)fail("native controls output");fputs("[\n",json);
 for(size_t i=0;i<sizeof controls/sizeof *controls;i++){
  const struct control *c=&controls[i];size_t expected=find_spec(c->expected),actual=find_spec(c->mutant);
  struct shared_control *shared=mmap(NULL,sizeof *shared,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);
  if(shared==MAP_FAILED)fail("control shared record");
  memset(shared,0,sizeof *shared);
  pid_t pid=fork();if(pid<0)fail("native control fork");
  if(!pid){
   /* Deliberate faults use default signal termination in this child. There is
    * no user signal handler, parent recovery, or handler stack using guest RSP. */
   if(signal(SIGSEGV,SIG_DFL)==SIG_ERR || signal(SIGBUS,SIG_DFL)==SIG_ERR || signal(SIGILL,SIG_DFL)==SIG_ERR || signal(SIGFPE,SIG_DFL)==SIG_ERR)_exit(90);
   planned_capture=&shared->planned;
   shared->mismatch=observe(&shared->record,expected,actual,1,c->profile,(int)c->writable,1);
   _exit(shared->mismatch?1:0);
  }
  int status=0;if(waitpid(pid,&status,0)!=pid)fail("native control waitpid");
  int sig=WIFSIGNALED(status)?WTERMSIG(status):0;
  int exit_code=WIFEXITED(status)?WEXITSTATUS(status):-1;
  if(c->signal_expected){if(sig!=c->signal_expected || shared->record.f[F_READY]!=0)fail("native fault control unexpected result");}
  else if(sig || exit_code!=1 || !shared->mismatch || shared->record.f[F_READY]!=1)fail("native semantic mutant accepted or failed unexpectedly");
  char evidence[160];
  if(sig){
   snprintf(evidence,sizeof evidence,"failures/%s.before-pages.bin",c->mutant);write_file(evidence,shared->record.before,sizeof shared->record.before);
  }else{
   snprintf(evidence,sizeof evidence,"failures/%s.capture.bin",c->mutant);size_t n=HEADER_BYTES+RECORD_BYTES+16;unsigned char *p=calloc(1,n);if(!p)fail("control evidence allocation");make_header(p,1);encode_record(p+HEADER_BYTES,&shared->record);trailer(p+n-16,1);write_file(evidence,p,n);free(p);
  }
  fprintf(json," {\"name\":\"%s\",\"expected_contract\":\"%s\",\"literal_bytes\":\"%s\",\"profile\":%u,\"operand_writable\":%s,\"rejected\":true,\"signal\":%d,\"exit\":%d,\"mismatch_mask\":%u,\"capture_complete\":%s,\"evidence\":\"%s\",\"planned_input_gprs\":[",c->mutant,c->expected,specs[actual].hex,c->profile,c->writable?"true":"false",sig,exit_code,shared->mismatch,sig?"false":"true",evidence);
  for(unsigned j=0;j<16;j++)fprintf(json,"%s\"0x%016"PRIx64"\"",j?",":"",shared->planned.gpr[j]);
  fprintf(json,"],\"requested_flags\":\"0x%"PRIx64"\",\"fault_measured_before\":null,\"fault_measured_after\":null}%s\n",shared->planned.flags,i+1==sizeof controls/sizeof *controls?"":",");
  if(munmap(shared,sizeof *shared))fail("control unmap");
 }
 fputs("]\n",json);if(fclose(json))fail("native controls close");puts("Rejected 16 actual native mutants, including 2 isolated SIGSEGV controls");
}
