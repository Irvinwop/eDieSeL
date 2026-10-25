/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include "common.h"

#define P(n,h,d,b,i,s,x,a) {#n,h,rex32_##n,rex32_##n##_end,rex32_##n##_return_end,d,b,i,s,x,a},
const struct spec specs[]={
#include "contracts.h"
};
#undef P
const size_t spec_count=sizeof specs/sizeof *specs;
const uintptr_t page_addresses[MAP_COUNT]={UINT64_C(0x120001000),UINT64_C(0x20001000),UINT64_C(0x130001000)};
struct auth binding;

void fail(const char *s){fprintf(stderr,"REJECT: %s\n",s);exit(2);}
int span(uintptr_t begin,uintptr_t end,size_t limit,size_t *n){
 if(end<=begin || end-begin>limit)return 0;
 *n=(size_t)(end-begin);return 1;
}
unsigned char *read_file(const char *path,size_t *n){
 FILE *f=fopen(path,"rb");if(!f)fail("open input");
 if(fseek(f,0,SEEK_END))fail("seek input");
 long z=ftell(f);if(z<0 || (unsigned long)z>MAX_FILE_BYTES)fail("input size");
 rewind(f);unsigned char *p=malloc((size_t)z+1);if(!p)fail("allocation");
 if(fread(p,1,(size_t)z,f)!=(size_t)z || ferror(f) || fclose(f))fail("read input");
 *n=(size_t)z;return p;
}
void write_file(const char *path,const void *p,size_t n){
 FILE *f=fopen(path,"wb");if(!f)fail("open output");
 if(fwrite(p,1,n,f)!=n || fclose(f))fail("write output");
}
void digest(const void *p,size_t n,unsigned char out[32]){
 unsigned z=0;if(!EVP_Digest(p,n,out,&z,EVP_sha256(),NULL) || z!=32)fail("SHA256");
}
void hex_print(FILE *f,const void *v,size_t n){
 const unsigned char *p=v;for(size_t i=0;i<n;i++)fprintf(f,"%02x",p[i]);
}
int unhex(const char *s,unsigned char *p,size_t n){
 if(strlen(s)!=2*n)return 0;
 for(size_t i=0;i<n;i++){
  unsigned v=0;for(unsigned j=0;j<2;j++){
   unsigned c=(unsigned char)s[2*i+j],x;
   if(c>='0' && c<='9')x=c-'0';else if(c>='a' && c<='f')x=c-'a'+10;else return 0;
   v=v*16+x;
  }p[i]=(unsigned char)v;
 }return 1;
}
uint64_t get64(const unsigned char *p){uint64_t v=0;for(unsigned i=0;i<8;i++)v|=(uint64_t)p[i]<<(8*i);return v;}
void put64(unsigned char *p,uint64_t v){for(unsigned i=0;i<8;i++)p[i]=(unsigned char)(v>>(8*i));}
size_t probe_bytes(const struct spec *s,unsigned char b[8]){
 size_t n=strlen(s->hex)/2;
 if(n<2 || n>8 || !unhex(s->hex,b,n))fail("literal contract");
 return n;
}
void metadata(FILE *f){
 fprintf(f,"{\n \"format\":\"rex-data32-native-v1\",\n \"register_order\":[\"rax\",\"rcx\",\"rdx\",\"rbx\",\"rsp\",\"rbp\",\"rsi\",\"rdi\",\"r8\",\"r9\",\"r10\",\"r11\",\"r12\",\"r13\",\"r14\",\"r15\"],\n");
 fprintf(f," \"section\":{\"name\":\".rex32_native\",\"begin\":\"0x%"PRIxPTR"\",\"end\":\"0x%"PRIxPTR"\"},\n",(uintptr_t)rex32_section_begin,(uintptr_t)rex32_section_end);
 fprintf(f," \"capture_harness\":{\"run_begin\":\"0x%"PRIxPTR"\",\"run_end\":\"0x%"PRIxPTR"\",\"capture_begin\":\"0x%"PRIxPTR"\",\"capture_end\":\"0x%"PRIxPTR"\"},\n",(uintptr_t)rex32_run,(uintptr_t)rex32_run_end,(uintptr_t)rex32_capture,(uintptr_t)rex32_capture_end);
 fprintf(f," \"probes\":[\n");
 for(size_t i=0;i<spec_count;i++){
  const struct spec *s=&specs[i];size_t n;unsigned char b[8];size_t lit=probe_bytes(s,b);
  if(!span((uintptr_t)s->start,(uintptr_t)s->end,15,&n) || n!=lit || memcmp(b,(void *)(uintptr_t)s->start,n))fail("literal symbol span");
  fprintf(f,"  {\"id\":%zu,\"name\":\"%s\",\"symbol\":\"rex32_%s\",\"start\":\"0x%"PRIxPTR"\",\"end\":\"0x%"PRIxPTR"\",\"return_end\":\"0x%"PRIxPTR"\",\"bytes_hex\":\"%s\",\"length\":%zu,\"destination\":%u,\"base\":%u,\"index\":%d,\"scale\":%u,\"signed_disp8\":%d,\"positive\":%s}%s\n",i,s->name,s->name,(uintptr_t)s->start,(uintptr_t)s->end,(uintptr_t)s->return_end,s->hex,n,s->dest,s->base,s->index,s->scale,s->disp,s->accepted?"true":"false",i+1==spec_count?"":",");
 }fprintf(f," ]\n}\n");
}
static int in_file(size_t n,uint64_t off,uint64_t len){return off<=n && len<=n-off;}
static Elf64_Shdr section_header(const unsigned char *p,size_t n,const Elf64_Ehdr *e,size_t i){
 Elf64_Shdr s;if(i>=e->e_shnum || !in_file(n,e->e_shoff+i*sizeof s,sizeof s))fail("ELF section table bounds");
 memcpy(&s,p+e->e_shoff+i*sizeof s,sizeof s);return s;
}
static const char *elf_string(const unsigned char *p,size_t n,Elf64_Shdr t,uint64_t off){
 if(!in_file(n,t.sh_offset,t.sh_size) || off>=t.sh_size || !memchr(p+t.sh_offset+off,0,(size_t)(t.sh_size-off)))fail("ELF string bounds");
 return (const char *)(p+t.sh_offset+off);
}
static Elf64_Sym symbol(const unsigned char *p,size_t n,Elf64_Shdr sy,Elf64_Shdr st,const char *name){
 if(sy.sh_entsize!=sizeof(Elf64_Sym) || sy.sh_size%sizeof(Elf64_Sym) || !in_file(n,sy.sh_offset,sy.sh_size))fail("ELF symbol table");
 Elf64_Sym answer={0};unsigned found=0;
 for(size_t i=0;i<sy.sh_size/sizeof(Elf64_Sym);i++){
  Elf64_Sym x;memcpy(&x,p+sy.sh_offset+i*sizeof x,sizeof x);
  if(!strcmp(elf_string(p,n,st,x.st_name),name)){answer=x;found++;}
 }if(found!=1)fail("missing/duplicate ELF symbol");return answer;
}
static void check_symbol(const unsigned char *p,size_t n,Elf64_Shdr sy,Elf64_Shdr st,size_t sec,const char *name,uintptr_t address,uint64_t size,int function){
 Elf64_Sym x=symbol(p,n,sy,st,name);
 if(x.st_shndx!=sec || x.st_value!=address || x.st_size!=size || ELF64_ST_BIND(x.st_info)!=STB_GLOBAL || ELF64_ST_TYPE(x.st_info)!=(function?STT_FUNC:STT_NOTYPE))fail("ELF symbol binding");
}
void authenticate(const char *elf,const char *section,const char *meta){
 size_t n,z;unsigned char *p=read_file(elf,&n),*self=read_file("/proc/self/exe",&z);
 if(z!=n || memcmp(p,self,n))fail("supplied ELF differs from running executable");
 free(self);
 digest(p,n,binding.elf);
 if(n<sizeof(Elf64_Ehdr))fail("ELF header size");
 Elf64_Ehdr e;memcpy(&e,p,sizeof e);
 if(memcmp(e.e_ident,ELFMAG,SELFMAG) || e.e_ident[EI_CLASS]!=ELFCLASS64 || e.e_ident[EI_DATA]!=ELFDATA2LSB || e.e_ident[EI_VERSION]!=EV_CURRENT || e.e_type!=ET_EXEC || e.e_machine!=EM_X86_64 || e.e_ehsize!=sizeof e || e.e_shentsize!=sizeof(Elf64_Shdr) || e.e_phentsize!=sizeof(Elf64_Phdr) || e.e_shstrndx>=e.e_shnum)fail("ELF identity");
 Elf64_Shdr names=section_header(p,n,&e,e.e_shstrndx),sec={0},sy={0};size_t sec_id=0;unsigned sec_found=0,sy_found=0;
 for(size_t i=0;i<e.e_shnum;i++){
  Elf64_Shdr s=section_header(p,n,&e,i);const char *name=elf_string(p,n,names,s.sh_name);
  if(!strcmp(name,".rex32_native")){sec=s;sec_id=i;sec_found++;}
  if(s.sh_type==SHT_SYMTAB){sy=s;sy_found++;}
 }
 size_t length;if(sec_found!=1 || sy_found!=1 || sec.sh_type!=SHT_PROGBITS || sec.sh_flags!=(SHF_ALLOC|SHF_EXECINSTR) || !span((uintptr_t)rex32_section_begin,(uintptr_t)rex32_section_end,65536,&length) || sec.sh_addr!=(uintptr_t)rex32_section_begin || sec.sh_size!=length || !in_file(n,sec.sh_offset,sec.sh_size) || memcmp(p+sec.sh_offset,rex32_section_begin,length))fail("whole linked executable section");
 unsigned executable=0;
 for(size_t i=0;i<e.e_phnum;i++){
  Elf64_Phdr ph;if(!in_file(n,e.e_phoff+i*sizeof ph,sizeof ph))fail("ELF program table bounds");memcpy(&ph,p+e.e_phoff+i*sizeof ph,sizeof ph);
  if(ph.p_type==PT_LOAD && sec.sh_addr>=ph.p_vaddr && sec.sh_addr-ph.p_vaddr<=ph.p_filesz && sec.sh_size<=ph.p_filesz-(sec.sh_addr-ph.p_vaddr) && ph.p_offset<=UINT64_MAX-(sec.sh_addr-ph.p_vaddr) && ph.p_offset+sec.sh_addr-ph.p_vaddr==sec.sh_offset && (ph.p_flags&(PF_X|PF_R|PF_W))==(PF_X|PF_R))executable++;
 }if(executable!=1)fail("ELF executable load segment");
 Elf64_Shdr strings=section_header(p,n,&e,sy.sh_link);
#define CS(name,addr,size,fn) check_symbol(p,n,sy,strings,sec_id,name,(uintptr_t)(addr),(size),(fn))
 CS("rex32_section_begin",rex32_section_begin,0,0);CS("rex32_section_end",rex32_section_end,0,0);
 if((uintptr_t)rex32_run!=(uintptr_t)rex32_section_begin || (uintptr_t)rex32_run_end!=(uintptr_t)rex32_capture)fail("harness section order");
 size_t run_n,cap_n;if(!span((uintptr_t)rex32_run,(uintptr_t)rex32_run_end,length,&run_n) || !span((uintptr_t)rex32_capture,(uintptr_t)rex32_capture_end,length,&cap_n))fail("harness integer span");
 CS("rex32_run",rex32_run,run_n,1);CS("rex32_run_end",rex32_run_end,0,0);
 CS("rex32_capture",rex32_capture,cap_n,1);CS("rex32_capture_end",rex32_capture_end,0,0);
 uintptr_t cursor=(uintptr_t)rex32_capture_end;
 unsigned positive=0;
 for(size_t i=0;i<spec_count;i++){
  const struct spec *s=&specs[i];size_t lit,body,full;unsigned char b[8];char label[128];
  lit=probe_bytes(s,b);
  if((uintptr_t)s->start!=cursor || !span(cursor,(uintptr_t)s->end,15,&body) || body!=lit || !span(cursor,(uintptr_t)s->return_end,32,&full) || (uintptr_t)s->return_end>(uintptr_t)rex32_section_end || memcmp(b,(void *)cursor,lit))fail("probe literal/full symbol span");
  snprintf(label,sizeof label,"rex32_%s",s->name);CS(label,s->start,full,1);
  snprintf(label,sizeof label,"rex32_%s_end",s->name);CS(label,s->end,0,0);
  snprintf(label,sizeof label,"rex32_%s_return_end",s->name);CS(label,s->return_end,0,0);
  cursor=(uintptr_t)s->return_end;
  if(s->accepted){if(i!=positive || s->dest>15 || s->base>15 || s->index>15 || s->index< -1 || s->scale>3 || s->disp< -128 || s->disp>127)fail("literal contract metadata");positive++;}
 }
 if(cursor!=(uintptr_t)rex32_section_end || positive!=POSITIVES)fail("unaccounted executable section bytes");
#undef CS
 unsigned char *extracted=read_file(section,&z);
 if(z!=length || memcmp(extracted,p+sec.sh_offset,length))fail("final ELF extraction mismatch");
 digest(extracted,z,binding.section);free(extracted);free(p);
 if(meta){char *generated=NULL;size_t m=0;FILE *f=open_memstream(&generated,&m);if(!f)fail("metadata stream");metadata(f);if(fclose(f))fail("metadata close");unsigned char *actual=read_file(meta,&z);if(z!=m || memcmp(generated,actual,m))fail("metadata differs from literal/symbol contracts");digest(actual,z,binding.metadata);free(actual);free(generated);}
}
void make_header(unsigned char h[HEADER_BYTES],uint64_t count){
 memset(h,0,HEADER_BYTES);memcpy(h,"REX32-DATA4-V1",14);
 put64(h+16,1);put64(h+24,count);put64(h+32,PAGE_BYTES);put64(h+40,MAP_COUNT);
 memcpy(h+48,binding.elf,32);memcpy(h+80,binding.section,32);memcpy(h+112,binding.metadata,32);
 put64(h+144,(uintptr_t)rex32_section_begin);put64(h+152,(uintptr_t)rex32_section_end);
}
void encode_record(unsigned char *p,const struct record *r){
 for(unsigned i=0;i<FIELD_COUNT;i++)put64(p+8*i,r->f[i]);
 memcpy(p+8*FIELD_COUNT,r->before,sizeof r->before);memcpy(p+8*FIELD_COUNT+sizeof r->before,r->after,sizeof r->after);
}
void decode_record(struct record *r,const unsigned char *p){
 for(unsigned i=0;i<FIELD_COUNT;i++)r->f[i]=get64(p+8*i);
 memcpy(r->before,p+8*FIELD_COUNT,sizeof r->before);memcpy(r->after,p+8*FIELD_COUNT+sizeof r->before,sizeof r->after);
}
