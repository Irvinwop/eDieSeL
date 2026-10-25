/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef REX32_COMMON_H
#define REX32_COMMON_H
#define _GNU_SOURCE
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <openssl/evp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#define PAGE_BYTES 4096u
#define MAP_COUNT 3u
#define HEADER_BYTES 160u
#define FIELD_COUNT 60u
#define RECORD_BYTES (FIELD_COUNT * 8u + MAP_COUNT * PAGE_BYTES * 2u)
#define MAX_FILE_BYTES (8u * 1024u * 1024u)
#define POSITIVES 37u
#define RECORD_COUNT (POSITIVES * 4u)
#define STATUS_MASK UINT64_C(0xcd5)
enum field {
 F_ORD, F_CASE, F_ACTUAL, F_SEED, F_PROFILE, F_LENGTH, F_START, F_END,
 F_DEST, F_BASE, F_INDEX, F_SCALE, F_DISP, F_OPERAND, F_REQUESTED,
 F_FLAGS_BEFORE, F_FLAGS_AFTER, F_SUCCESSOR, F_MAP0, F_MAP1, F_MAP2,
 F_PERM0, F_PERM1, F_PERM2, F_PRE, F_POST=F_PRE+16, F_CODE=F_POST+16,
 F_READY, F_RESERVED0, F_RESERVED1
};
_Static_assert(F_RESERVED1+1 == FIELD_COUNT,"wire field count");
struct capture { uint64_t gpr[16], flags; };
_Static_assert(sizeof(struct capture)==136,"assembly layout");
struct record {
 uint64_t f[FIELD_COUNT];
 unsigned char before[MAP_COUNT][PAGE_BYTES],after[MAP_COUNT][PAGE_BYTES];
};
_Static_assert(sizeof(struct record)==RECORD_BYTES,"in-memory layout");
extern struct capture rex32_input,rex32_before,rex32_after;
extern void rex32_run(void (*)(void));
extern const unsigned char rex32_section_begin[],rex32_section_end[];
extern const unsigned char rex32_run_end[],rex32_capture[],rex32_capture_end[];
#define P(n,h,d,b,i,s,x,a) extern void rex32_##n(void); \
 extern const unsigned char rex32_##n##_end[],rex32_##n##_return_end[];
#include "contracts.h"
#undef P
struct spec {
 const char *name,*hex;
 void (*start)(void);
 const unsigned char *end,*return_end;
 unsigned dest,base; int index; unsigned scale; int disp,accepted;
};
extern const struct spec specs[];
extern const size_t spec_count;
extern const uintptr_t page_addresses[MAP_COUNT];
struct auth { unsigned char elf[32],section[32],metadata[32]; };
extern struct auth binding;

_Noreturn void fail(const char *reason);
int span(uintptr_t begin,uintptr_t end,size_t limit,size_t *n);
unsigned char *read_file(const char *path,size_t *n);
void write_file(const char *path,const void *p,size_t n);
void digest(const void *p,size_t n,unsigned char out[32]);
void hex_print(FILE *f,const void *p,size_t n);
int unhex(const char *text,unsigned char *p,size_t n);
uint64_t get64(const unsigned char *p);
void put64(unsigned char *p,uint64_t v);
size_t probe_bytes(const struct spec *s,unsigned char bytes[8]);
void metadata(FILE *f);
void authenticate(const char *elf,const char *section,const char *meta);
void make_header(unsigned char h[HEADER_BYTES],uint64_t count);
void encode_record(unsigned char *p,const struct record *r);
void decode_record(struct record *r,const unsigned char *p);
unsigned oracle(const struct record *r,unsigned destination,uintptr_t target);
void capture_all(const char *path);
void native_controls(void);
void auth_controls(const char *elf,const char *section,const char *meta,const char *captures,const char *hash);
int verify_blob(const unsigned char *p,size_t n,const unsigned char expected[32],char *why,size_t why_n);
void verify_file(const char *path,const char *hash);
void parser_controls(const char *path);
void dump_file(const char *path);
#endif
