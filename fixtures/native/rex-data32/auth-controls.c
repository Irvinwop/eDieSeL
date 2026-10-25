/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include "common.h"

/* These children execute only the authenticated owned checker. Modified ELF
 * files are data arguments, never program images. Authentication precedes any
 * probe execution and must reject before parsing the capture. */
static int rejected_child(const char *runner,const char *elf,const char *section,const char *meta,const char *capture,const char *hash,const char *log){
 pid_t pid=fork();if(pid<0)fail("authentication control fork");
 if(!pid){
  int fd=open(log,O_WRONLY|O_CREAT|O_TRUNC,0600);if(fd<0 || dup2(fd,STDERR_FILENO)<0)_exit(90);
  close(fd);int null=open("/dev/null",O_WRONLY);if(null<0 || dup2(null,STDOUT_FILENO)<0)_exit(90);close(null);
  execl(runner,runner,"verify",elf,section,meta,capture,hash,(char *)NULL);_exit(91);
 }
 int status=0;if(waitpid(pid,&status,0)!=pid)fail("authentication control wait");
 return WIFEXITED(status) && WEXITSTATUS(status)==2;
}
void auth_controls(const char *elf,const char *section,const char *meta,const char *captures,const char *hash){
 size_t section_n,meta_n,elf_n;unsigned char *s=read_file(section,&section_n),*m=read_file(meta,&meta_n),*e=read_file(elf,&elf_n);
 const char *names[]={"section_dispatch_harness_changed","section_capture_harness_changed","section_probe_changed","section_truncated","section_extra_byte","section_missing","metadata_destination_changed","metadata_span_changed","metadata_truncated","metadata_duplicate_probe","metadata_missing_probe","metadata_missing","ELF_changed","ELF_truncated","ELF_missing"};
 FILE *json=fopen("AUTH-CONTROLS.json","w");if(!json)fail("authentication control output");fputs("[\n",json);
 unsigned char *scratch=malloc(MAX_FILE_BYTES);if(!scratch)fail("authentication control allocation");
 for(unsigned i=0;i<sizeof names/sizeof *names;i++){
  char path[160],log[160];snprintf(path,sizeof path,"failures/%s.input",names[i]);snprintf(log,sizeof log,"failures/%s.log",names[i]);
  const char *changed_elf=elf,*changed_section=section,*changed_meta=meta;size_t changed_n=0;int exists=1;
  if(i<=5){
   memcpy(scratch,s,section_n);changed_n=section_n;changed_section=path;
   if(i==0)scratch[0]^=1;
   if(i==1)scratch[(uintptr_t)rex32_capture-(uintptr_t)rex32_section_begin]^=1;
   if(i==2)scratch[(uintptr_t)specs[0].start-(uintptr_t)rex32_section_begin]^=1;
   if(i==3)changed_n--;
   if(i==4)scratch[changed_n++]=0;
   if(i==5)exists=0;
  }else if(i<=11){
   memcpy(scratch,m,meta_n);scratch[meta_n]=0;changed_n=meta_n;changed_meta=path;
   char *dest=strstr((char *)scratch,"\"destination\":9");char *length=strstr((char *)scratch,"\"length\":4");
   char *first=strstr((char *)scratch,"  {\"id\":0,");char *end=first?strchr(first,'\n'):NULL;
   if(!dest || !length || !first || !end)fail("metadata control input");
   if(i==6)dest[strlen("\"destination\":")]='8';
   if(i==7)length[strlen("\"length\":")]='3';
   if(i==8)changed_n-=10;
   if(i==9){size_t start=(size_t)(first-(char *)scratch),line=(size_t)(end-first)+1;memmove(scratch+start+line,scratch+start,meta_n-start);memcpy(scratch+start,first+line,line);changed_n+=line;}
   if(i==10){size_t start=(size_t)(first-(char *)scratch),line=(size_t)(end-first)+1;memmove(scratch+start,scratch+start+line,meta_n-start-line);changed_n-=line;}
   if(i==11)exists=0;
  }else{
   memcpy(scratch,e,elf_n);changed_n=elf_n;changed_elf=path;
   if(i==12)scratch[0]^=1;
   if(i==13)changed_n--;
   if(i==14)exists=0;
  }
  if(exists)write_file(path,scratch,changed_n);
  if(!rejected_child(elf,changed_elf,changed_section,changed_meta,captures,hash,log))fail("authentication control accepted or unexpected failure");
  fprintf(json," {\"name\":\"%s\",\"rejected\":true,\"exit\":2,\"input\":\"%s\",\"input_exists\":%s,\"log\":\"%s\"}%s\n",names[i],path,exists?"true":"false",log,i+1==sizeof names/sizeof *names?"":",");
 }
 fputs("]\n",json);if(fclose(json))fail("authentication controls close");free(scratch);free(s);free(m);free(e);
 puts("Rejected 15 executable/whole-section/harness/symbol-metadata authentication controls");
}
