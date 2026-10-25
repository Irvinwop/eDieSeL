/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include "common.h"

static int reject(char *why,size_t n,const char *message){snprintf(why,n,"%s",message);return 0;}
int verify_blob(const unsigned char *p,size_t n,const unsigned char expected[32],char *why,size_t why_n){
 const size_t exact=HEADER_BYTES+RECORD_COUNT*RECORD_BYTES+16;
 if(n!=exact)return reject(why,why_n,"missing/truncated/extra capture bytes");
 unsigned char hash[32];digest(p,n,hash);
 if(memcmp(hash,expected,32))return reject(why,why_n,"capture SHA256 binding");
 unsigned char header[HEADER_BYTES];make_header(header,RECORD_COUNT);
 if(memcmp(p,header,HEADER_BYTES))return reject(why,why_n,"format/ELF/section/metadata header binding");
 if(memcmp(p+n-16,"ENDR32V1",8) || get64(p+n-8)!=RECORD_COUNT)return reject(why,why_n,"capture trailer");
 for(unsigned i=0;i<RECORD_COUNT;i++){
  struct record r;decode_record(&r,p+HEADER_BYTES+i*RECORD_BYTES);
  const uint64_t *f=r.f;unsigned k=i/4,seed=(i/2)%2,profile=i%2;const struct spec *s=&specs[k];
  if(f[F_ORD]!=i || f[F_CASE]!=k || f[F_ACTUAL]!=k || f[F_SEED]!=seed || f[F_PROFILE]!=profile)return reject(why,why_n,"missing/duplicate/reordered/wrong record identity");
  size_t length;unsigned char code[8]={0};size_t lit=probe_bytes(s,code);
  if(!span((uintptr_t)s->start,(uintptr_t)s->end,15,&length) || length!=lit || f[F_LENGTH]!=length || f[F_START]!=(uintptr_t)s->start || f[F_END]!=(uintptr_t)s->end || f[F_SUCCESSOR]!=(uintptr_t)s->end || f[F_CODE]!=get64(code))return reject(why,why_n,"literal bytes/authenticated label span/successor");
  if(f[F_DEST]!=s->dest || f[F_BASE]!=s->base || f[F_INDEX]!=(uint64_t)(int64_t)s->index || f[F_SCALE]!=s->scale || f[F_DISP]!=(uint64_t)(int64_t)s->disp)return reject(why,why_n,"independently declared destination/address contract");
  if(f[F_READY]!=1 || f[F_RESERVED0] || f[F_RESERVED1])return reject(why,why_n,"incomplete capture/reserved fields");
  for(unsigned j=0;j<MAP_COUNT;j++)if(f[F_MAP0+j]!=page_addresses[j] || f[F_PERM0+j]!=PROT_READ)return reject(why,why_n,"measured page address/read-only permission");
  const uintptr_t target=page_addresses[0]+(profile?PAGE_BYTES-4:1027+32*seed);
  if(f[F_OPERAND]!=target || target<=UINT32_MAX || (uint32_t)target!=page_addresses[1]+(target-page_addresses[0]))return reject(why,why_n,"full64 operand/low32 decoy address binding");
  /* A consistency check of the declared address expression, independent of
   * encoding bytes. It does not supply the C expected load value. */
  uint64_t address=f[F_PRE+s->base]+(uint64_t)(int64_t)s->disp;
  if(s->index>=0)address+=f[F_PRE+(unsigned)s->index]<<s->scale;
  if(address!=target)return reject(why,why_n,"measured full64 prestate address");
  if(f[F_REQUESTED]!=(UINT64_C(0x202)|(seed?STATUS_MASK:0)) || ((f[F_FLAGS_BEFORE]^f[F_REQUESTED])&STATUS_MASK))return reject(why,why_n,"measured writable status-flag pattern");
  if(!(f[F_PRE+s->dest]>>32))return reject(why,why_n,"zero-extension witness missing upper destination");
  if(oracle(&r,s->dest,target))return reject(why,why_n,"independent C DATA4/full-GPR/full-flags/whole-page oracle");
 }
 snprintf(why,why_n,"accepted");return 1;
}
void verify_file(const char *path,const char *hex){
 unsigned char expected[32];if(!unhex(hex,expected,32))fail("noncanonical SHA256 argument");
 size_t n;unsigned char *p=read_file(path,&n);char why[160];
 if(!verify_blob(p,n,expected,why,sizeof why))fail(why);
 unsigned char h[32];digest(p,n,h);free(p);
 FILE *f=fopen("BINDING.json","w");if(!f)fail("binding output");
 fprintf(f,"{\n \"format\":\"rex-data32-native-v1\",\n \"observations\":%u,\n \"positive_probes\":%u,\n \"capture_sha256\":\"",RECORD_COUNT,POSITIVES);hex_print(f,h,32);
 fputs("\",\n \"elf_sha256\":\"",f);hex_print(f,binding.elf,32);fputs("\",\n \"whole_probe_and_capture_section_sha256\":\"",f);hex_print(f,binding.section,32);fputs("\",\n \"literal_metadata_sha256\":\"",f);hex_print(f,binding.metadata,32);
 fputs("\",\n \"native_rip_sampled\":false,\n \"successor\":\"authenticated end label; no hardware RIP observation\",\n \"C_memory_evidence\":\"all 4096 bytes before/after of operand, low32 decoy and wrong-bank decoy pages\",\n \"future_Lean_memory_evidence\":\"replay neighborhood plus separate model frame of read/execute/write maps; not a physical whole-address-space observation\",\n \"claim\":\"finite owned native conformance only; no Lean replay, CPU refinement or universal concurrency claim\"\n}\n",f);
 if(fclose(f))fail("binding close");
 printf("Verified %u records against literal/symbol/ELF/section/SHA256 bindings and independent C oracle\n",RECORD_COUNT);
}
static size_t case_id(const char *name){for(size_t i=0;i<POSITIVES;i++)if(!strcmp(specs[i].name,name))return i;fail("parser control case");return 0;}
void parser_controls(const char *path){
 size_t n;unsigned char *original=read_file(path,&n),base_hash[32];digest(original,n,base_hash);
 char why[160];if(!verify_blob(original,n,base_hash,why,sizeof why))fail("parser controls baseline");
 enum mutation {CUT_LAST,CUT_HEADER,CUT_RECORD,EXTRA,VERSION,HEADER_ELF,HEADER_SECTION,HEADER_META,DUPLICATE,MISSING,ORDINAL,LEN_MINUS,LEN_PLUS,END_MINUS,END_PLUS,NEXT_OLD,REX_MISSING,WRONG_DIRECTION,WRONG_CODE,WRONG_DST,WRONG_BASE,WRONG_SCALE,WRONG_DISP,PRE_GPR,POST_GPR,PRE_FLAGS,POST_FLAGS,HIGH_FLAGS,BEFORE_RAM,AFTER_RAM,CANARY_RAM,DECOY_RAM,ENDIAN_ADDRESS,ENDIAN_WORD,LOW_ADDRESS,HIGH_DEST,SUFFIX,RESERVED,UNREADY,PERMISSIONS,BOUND_HASH};
 static const struct {const char *name;enum mutation mutation;} cases[]={
  {"truncated_trailer",CUT_LAST},{"truncated_header",CUT_HEADER},{"truncated_record_fields",CUT_RECORD},{"extra_byte",EXTRA},
  {"version",VERSION},{"ELF_digest",HEADER_ELF},{"whole_section_digest",HEADER_SECTION},{"literal_metadata_digest",HEADER_META},
  {"duplicate_record",DUPLICATE},{"missing_record",MISSING},{"record_ordinal",ORDINAL},
  {"declared_span_minus_one",LEN_MINUS},{"declared_span_plus_one",LEN_PLUS},{"end_label_minus_one",END_MINUS},{"end_label_plus_one",END_PLUS},{"old_2_plus_suffix_successor",NEXT_OLD},
  {"removed_REX_retained_span",REX_MISSING},{"wrong_direction_bytes",WRONG_DIRECTION},{"changed_fixed_code",WRONG_CODE},
  {"wrong_destination_bank",WRONG_DST},{"wrong_base_bank",WRONG_BASE},{"wrong_scale_metadata",WRONG_SCALE},{"unsigned_disp8_metadata",WRONG_DISP},
  {"before_GPR_tamper",PRE_GPR},{"after_GPR_tamper",POST_GPR},{"before_flags_tamper",PRE_FLAGS},{"after_flags_tamper",POST_FLAGS},{"high_flag_bit_tamper",HIGH_FLAGS},
  {"before_operand_RAM_tamper",BEFORE_RAM},{"after_operand_RAM_tamper",AFTER_RAM},{"far_page_canary_tamper",CANARY_RAM},{"wrong_address_decoy_page_tamper",DECOY_RAM},
  {"big_endian_address",ENDIAN_ADDRESS},{"big_endian_operand",ENDIAN_WORD},{"low32_address",LOW_ADDRESS},{"destination_upper32_preserved",HIGH_DEST},
  {"required_disp8_suffix_missing",SUFFIX},{"reserved_field",RESERVED},{"incomplete_measurement",UNREADY},{"operand_writable",PERMISSIONS},{"changed_capture_with_original_digest",BOUND_HASH}
 };
 FILE *f=fopen("PARSER-CONTROLS.json","w");if(!f)fail("parser controls output");fputs("[\n",f);
 unsigned char *p=malloc(n+1);if(!p)fail("parser control allocation");
 for(size_t i=0;i<sizeof cases/sizeof *cases;i++){
  memcpy(p,original,n);size_t changed_n=n,offset=0;unsigned char *r=p+HEADER_BYTES;enum mutation m=cases[i].mutation;
  if(m==WRONG_DISP || m==SUFFIX){r=p+HEADER_BYTES+case_id("scale2")*4*RECORD_BYTES;}
#define MUT_FIELD(field,value) do {offset=(size_t)(r-p)+(field)*8;put64(p+offset,(value));} while(0)
  switch(m){
   case CUT_LAST:changed_n=n-1;offset=n-1;break;
   case CUT_HEADER:changed_n=HEADER_BYTES-1;offset=changed_n;break;
   case CUT_RECORD:changed_n=HEADER_BYTES+FIELD_COUNT*8-1;offset=changed_n;break;
   case EXTRA:p[n]=0;changed_n=n+1;offset=n;break;
   case VERSION:offset=16;p[offset]^=1;break;
   case HEADER_ELF:offset=48;p[offset]^=1;break;
   case HEADER_SECTION:offset=80;p[offset]^=1;break;
   case HEADER_META:offset=112;p[offset]^=1;break;
   case DUPLICATE:offset=HEADER_BYTES+RECORD_BYTES;memcpy(p+offset,r,RECORD_BYTES);break;
   case MISSING:offset=HEADER_BYTES;memmove(p+offset,p+offset+RECORD_BYTES,n-offset-RECORD_BYTES);changed_n=n-RECORD_BYTES;break;
   case ORDINAL:MUT_FIELD(F_ORD,1);break;
   case LEN_MINUS:MUT_FIELD(F_LENGTH,get64(r+F_LENGTH*8)-1);break;
   case LEN_PLUS:MUT_FIELD(F_LENGTH,get64(r+F_LENGTH*8)+1);break;
   case END_MINUS:MUT_FIELD(F_END,get64(r+F_END*8)-1);break;
   case END_PLUS:MUT_FIELD(F_END,get64(r+F_END*8)+1);break;
   case NEXT_OLD:MUT_FIELD(F_SUCCESSOR,get64(r+F_SUCCESSOR*8)-1);break;
   case REX_MISSING:MUT_FIELD(F_CODE,get64(r+F_CODE*8)>>8);break;
   case WRONG_DIRECTION:offset=(size_t)(r-p)+F_CODE*8+1;p[offset]=0x89;break;
   case WRONG_CODE:offset=(size_t)(r-p)+F_CODE*8+3;p[offset]^=1;break;
   case WRONG_DST:MUT_FIELD(F_DEST,get64(r+F_DEST*8)^8);break;
   case WRONG_BASE:MUT_FIELD(F_BASE,get64(r+F_BASE*8)^8);break;
   case WRONG_SCALE:MUT_FIELD(F_SCALE,1);break;
   case WRONG_DISP:MUT_FIELD(F_DISP,128);break;
   case PRE_GPR:MUT_FIELD(F_PRE+2,get64(r+(F_PRE+2)*8)^1);break;
   case POST_GPR:MUT_FIELD(F_POST+2,get64(r+(F_POST+2)*8)^1);break;
   case PRE_FLAGS:MUT_FIELD(F_FLAGS_BEFORE,get64(r+F_FLAGS_BEFORE*8)^1);break;
   case POST_FLAGS:MUT_FIELD(F_FLAGS_AFTER,get64(r+F_FLAGS_AFTER*8)^1);break;
   case HIGH_FLAGS:MUT_FIELD(F_FLAGS_AFTER,get64(r+F_FLAGS_AFTER*8)^(UINT64_C(1)<<63));break;
   case BEFORE_RAM:offset=HEADER_BYTES+FIELD_COUNT*8+1027;p[offset]^=1;break;
   case AFTER_RAM:offset=HEADER_BYTES+FIELD_COUNT*8+MAP_COUNT*PAGE_BYTES+1027;p[offset]^=1;break;
   case CANARY_RAM:offset=HEADER_BYTES+FIELD_COUNT*8+MAP_COUNT*PAGE_BYTES+4000;p[offset]^=1;break;
   case DECOY_RAM:offset=HEADER_BYTES+FIELD_COUNT*8+(MAP_COUNT+1)*PAGE_BYTES+100;p[offset]^=1;break;
   case ENDIAN_ADDRESS:{offset=HEADER_BYTES+F_OPERAND*8;for(unsigned j=0;j<4;j++){unsigned char t=p[offset+j];p[offset+j]=p[offset+7-j];p[offset+7-j]=t;}break;}
   case ENDIAN_WORD:{offset=HEADER_BYTES+FIELD_COUNT*8+1027;for(unsigned j=0;j<2;j++){unsigned char t=p[offset+j];p[offset+j]=p[offset+3-j];p[offset+3-j]=t;}memcpy(p+offset+MAP_COUNT*PAGE_BYTES,p+offset,4);break;}
   case LOW_ADDRESS:MUT_FIELD(F_OPERAND,(uint32_t)get64(r+F_OPERAND*8));break;
   case HIGH_DEST:MUT_FIELD(F_POST+9,get64(r+(F_POST+9)*8)|UINT64_C(0xa501030500000000));break;
   case SUFFIX:offset=(size_t)(r-p)+F_CODE*8+4;p[offset]=0;break;
   case RESERVED:MUT_FIELD(F_RESERVED0,1);break;
   case UNREADY:MUT_FIELD(F_READY,0);break;
   case PERMISSIONS:MUT_FIELD(F_PERM0,3);break;
   case BOUND_HASH:offset=HEADER_BYTES+FIELD_COUNT*8+MAP_COUNT*PAGE_BYTES+4000;p[offset]^=1;break;
  }
#undef MUT_FIELD
  unsigned char changed_hash[32];digest(p,changed_n,changed_hash);
  const unsigned char *trusted=m==BOUND_HASH?base_hash:changed_hash;
  if(verify_blob(p,changed_n,trusted,why,sizeof why))fail("parser accepted negative control");
  fprintf(f," {\"name\":\"%s\",\"rejected\":true,\"reason\":\"%s\",\"first_mutation_offset\":%zu,\"size\":%zu,\"rehash_to_test_semantics\":%s,\"mutated_sha256\":\"",cases[i].name,why,offset,changed_n,m==BOUND_HASH?"false":"true");hex_print(f,changed_hash,32);fprintf(f,"\"}%s\n",i+1==sizeof cases/sizeof *cases?"":",");
 }
 fputs("]\n",f);if(fclose(f))fail("parser controls close");free(p);free(original);
 printf("Rejected %zu parser/semantic/binding controls\n",sizeof cases/sizeof *cases);
}
void dump_file(const char *path){
 size_t n;unsigned char *p=read_file(path,&n);(void)n;
 FILE *f=fopen("REPLAY-INPUTS.jsonl","w");if(!f)fail("replay input output");
 for(unsigned i=0;i<RECORD_COUNT;i++){
  struct record r;decode_record(&r,p+HEADER_BYTES+i*RECORD_BYTES);const struct spec *s=&specs[r.f[F_CASE]];
  const size_t off=(size_t)(r.f[F_OPERAND]-r.f[F_MAP0]);
  fprintf(f,"{\"ordinal\":%u,\"name\":\"%s\",\"seed\":%"PRIu64",\"profile\":%"PRIu64",\"constructor\":\"Instruction.loadMem32Rex\",\"bytes_hex\":\"%s\",\"length\":%"PRIu64",\"destination\":%u,\"base\":%u,\"index\":%d,\"scale\":%u,\"signed_disp8\":%d,\"operand_address\":\"0x%"PRIx64"\",\"authenticated_start_label\":\"0x%"PRIx64"\",\"authenticated_successor_label\":\"0x%"PRIx64"\",\"hardware_RIP\":null,\"model_relocation_entry\":4096,\"model_relocation_successor\":%"PRIu64",\"pre_gprs\":[",i,s->name,r.f[F_SEED],r.f[F_PROFILE],s->hex,r.f[F_LENGTH],s->dest,s->base,s->index,s->scale,s->disp,r.f[F_OPERAND],r.f[F_START],r.f[F_SUCCESSOR],4096+r.f[F_LENGTH]);
  for(unsigned j=0;j<16;j++)fprintf(f,"%s\"0x%016"PRIx64"\"",j?",":"",r.f[F_PRE+j]);
  fprintf(f,"],\"before_flags\":\"0x%016"PRIx64"\",\"requested_flags\":\"0x%016"PRIx64"\",\"post_gprs\":[",r.f[F_FLAGS_BEFORE],r.f[F_REQUESTED]);
  for(unsigned j=0;j<16;j++)fprintf(f,"%s\"0x%016"PRIx64"\"",j?",":"",r.f[F_POST+j]);
  fprintf(f,"],\"after_flags\":\"0x%016"PRIx64"\",\"ram_neighborhood_address\":\"0x%"PRIx64"\",\"ram_before_hex\":\"",r.f[F_FLAGS_AFTER],r.f[F_OPERAND]-8);hex_print(f,r.before[0]+off-8,12);fputs("\",\"ram_after_hex\":\"",f);hex_print(f,r.after[0]+off-8,12);
  fprintf(f,"\",\"modeled_operand_read\":{\"kind\":\"data\",\"address\":\"0x%"PRIx64"\",\"bytes\":4},\"page_digests\":[",r.f[F_OPERAND]);
  for(unsigned j=0;j<MAP_COUNT;j++){unsigned char a[32],b[32];digest(r.before[j],PAGE_BYTES,a);digest(r.after[j],PAGE_BYTES,b);fprintf(f,"%s{\"address\":\"0x%"PRIx64"\",\"before_sha256\":\"",j?",":"",r.f[F_MAP0+j]);hex_print(f,a,32);fputs("\",\"after_sha256\":\"",f);hex_print(f,b,32);fputs("\"}",f);}fputs("]}\n",f);
 }
 if(fclose(f))fail("replay input close");
 free(p);puts("Wrote replay input data only; no Lean invocation or proof");
}
