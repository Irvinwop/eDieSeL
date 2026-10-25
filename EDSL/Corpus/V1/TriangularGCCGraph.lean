/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0

Literal exact GCC graph checked against the sealed exact-NOP semantics.
-/
import EDSL.X86.Sequential.CFGVerification

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Corpus.V1.TriangularGCCGraph
open X86 X86.Sequential

/-- Exact original extent at VA 0x402ec0, file offset 11968, size 60.
External SHA256: a5a9161ea0eaf649bfcaf6c3964b08c48bfdd611307fe92c2b4acdedc13c7576.
These literals supply no semantic, ELF-binding or ownership evidence. -/
def bytes : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa,
  0x85, 0xff,
  0x74, 0x30,
  0x89, 0xff,
  0x31, 0xc0,
  0x48, 0x8d, 0x57, 0xff,
  0x40, 0xf6, 0xc7, 0x01,
  0x74, 0x12,
  0x48, 0x89, 0xf8,
  0x48, 0x89, 0xd7,
  0x48, 0x85, 0xd2,
  0x74, 0x1a,
  0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x8d, 0x44, 0x78, 0xff,
  0x48, 0x83, 0xef, 0x02,
  0x75, 0xf5,
  0xc3,
  0x0f, 0x1f, 0x40, 0x00,
  0x31, 0xc0,
  0xc3,
  0xc3
]

/-- Literal proposal checked by the production decoder: every byte and every original RET is retained.
Depth bounds only straight-line interiors. The cycle returns to cutpoint 13.
In particular 75 f5 is the production legacy JNZ constructor, not .jcc. -/
def graph : CFG.Graph where
  nodes := [
    ⟨0x00, .endbr64IbtDisabled, true, 12⟩,
    ⟨0x04, .test32 .rdi .rdi false, false, 11⟩,
    ⟨0x06, .je 0x30, false, 10⟩,
    ⟨0x08, .movReg32 .rdi .rdi, false, 9⟩,
    ⟨0x0a, .xorSelf32 .rax, false, 8⟩,
    ⟨0x0c, .lea64 .rdx (.baseDisp8 .rdi 0xff), false, 7⟩,
    ⟨0x10, .testImm8 .rdi 1 true, false, 6⟩,
    ⟨0x14, .je 0x12, false, 5⟩,
    ⟨0x16, .movReg64 .rax .rdi, false, 4⟩,
    ⟨0x19, .movReg64 .rdi .rdx, false, 3⟩,
    ⟨0x1c, .test64 .rdx .rdx, false, 2⟩,
    ⟨0x1f, .je 0x1a, false, 1⟩,
    ⟨0x21, .nop .seven, false, 0⟩,
    ⟨0x28, .lea64 .rax (.sibDisp8 .rax (some .rdi) 1 0xff), true, 3⟩,
    ⟨0x2d, .subImm64 .rdi 2, false, 2⟩,
    ⟨0x31, .legacy (.jnz 0xf5), false, 1⟩,
    ⟨0x33, .legacy .ret, false, 0⟩,
    ⟨0x34, .nop .four, false, 2⟩,
    ⟨0x38, .xorSelf32 .rax, false, 1⟩,
    ⟨0x3a, .legacy .ret, false, 0⟩,
    ⟨0x3b, .legacy .ret, false, 0⟩
  ]
  maxDepth := 12

abbrev entry : graph.Index := ⟨0, by decide⟩
abbrev loopHead : graph.Index := ⟨13, by decide⟩

/-- Checker invocation, not an already established GCC graph fact.
Uses the unchanged default 64-byte/32-node profile and production checker. -/
theorem valid : CFG.Valid bytes graph :=
  CFG.check_sound (by decide +kernel)

theorem cuts (node : graph.Index) (cut : graph.cutpoint node = true) :
    node = entry ∨ node = loopHead := by
  have finite : ∀ index : graph.Index,
      graph.cutpoint index = true → index = entry ∨ index = loopHead := by decide +kernel
  exact finite node cut

end EDSL.Corpus.V1.TriangularGCCGraph

#print axioms EDSL.Corpus.V1.TriangularGCCGraph.valid
