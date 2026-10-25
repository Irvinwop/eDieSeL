/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include "common.h"

/* Independent C DATA4 expectation. target and destination are separately
 * declared by the case, not decoded from bytes or produced by an address model.
 * Native fixture setup/address validation live elsewhere. This function copies
 * the measured prestate and changes exactly the declared destination, using
 * uint32_t memcpy, with the native x86 little-endian environment explicit. */
unsigned oracle(const struct record *r,unsigned destination,uintptr_t target){
 if(destination>=16 || target<r->f[F_MAP0] || target-r->f[F_MAP0]>PAGE_BYTES-4)return 16;
 const size_t off=(size_t)(target-r->f[F_MAP0]);uint32_t value;
 memcpy(&value,r->before[0]+off,sizeof value);
 uint64_t expected[16];memcpy(expected,r->f+F_PRE,sizeof expected);
 expected[destination]=(uint64_t)value;
 unsigned mismatch=0;
 if(memcmp(expected,r->f+F_POST,sizeof expected))mismatch|=1;
 if(r->f[F_FLAGS_BEFORE]!=r->f[F_FLAGS_AFTER])mismatch|=2;
 /* Complete operand and decoy page frames, including every canary byte. */
 if(memcmp(r->before,r->after,sizeof r->before))mismatch|=4;
 return mismatch;
}
