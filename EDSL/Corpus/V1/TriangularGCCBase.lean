/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0

Universal entry and loop contracts for the exact GCC graph.
-/
import EDSL.Arithmetic64.Triangular
import EDSL.WordMath.TriangularCountdown
import EDSL.PureCall.Frame
import EDSL.Corpus.V1.TriangularGCCGraph
import EDSL.X86.VCGen.CutpointsFlags
import EDSL.X86.Sequential.CountdownState
import EDSL.X86.VCGen.Tactics
import EDSL.X86.VCGen.ScratchFrame

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Corpus.V1.TriangularGCCBase
open X86 X86.Sequential X86.VCGen
open TriangularGCCGraph

abbrev spec := Arithmetic64.triangularModulo

def scratch : List Register := [.rax, .rdi, .rdx]

/-- RSP, every other GPR, full memory/permissions and every nonarithmetic flag
remain original at the loop head. Arithmetic flags are unrestricted there. -/
def LoopInvariant (input : PureCall.Invocation spec) (initial current : State) : Prop :=
  PureCall.ScratchFrame scratch initial current ∧
    WordMath.TriangularCountdown input.value.toNat
      (current.registers .rax).toNat (current.registers .rdi).toNat ∧
    0 < (current.registers .rdi).toNat

/-- Entry preserves the ENTIRE unrestricted initial state. No zero-extension
is asserted before the actual MOV EDI,EDI at +0x08. Only two cutpoints exist. -/
def invariant (input : PureCall.Invocation spec) (initial : State)
    (node : graph.Index) (current : State) : Prop :=
  if node.val = 0 then current = initial
  else if node.val = 13 then LoopInvariant input initial current
  else False

def rank (input : PureCall.Invocation spec) (node : graph.Index) (current : State) : Nat :=
  if node.val = 0 then input.value.toNat / 2 + 1
  else (current.registers .rdi).toNat / 2

/-- Universal entry obligation: all low32 values, arbitrary upper32 RDI,
scratch registers and incoming flags. Fuel 13 is a static block depth, not an
iteration bound. It covers all zero/even/odd/one paths and the real RETs. -/
def EntryBlockVC : Prop :=
  ∀ input initial, PureCall.Pre spec bytes input initial →
    Cutpoints.wp graph initial.rip (PureCall.Post spec input initial)
      (fun _ read => PureCall.RawRead initial read)
      (invariant input initial) (rank input) (rank input entry initial) 13 entry initial

/-- Universal loop obligation: the actual +0x28 LEA, +0x2d SUB and
+0x31 legacy JNZ, followed by either a lower-rank head or +0x33 actual RET.
The bound, permission, postcondition and real continuation remain in the WP. -/
def LoopBlockVC : Prop :=
  ∀ input initial, PureCall.Pre spec bytes input initial → ∀ current,
    CFG.At bytes graph initial.rip loopHead current →
    LoopInvariant input initial current →
    Cutpoints.wp graph initial.rip (PureCall.Post spec input initial)
      (fun _ read => PureCall.RawRead initial read)
      (invariant input initial) (rank input) (rank input loopHead current) 4 loopHead current


end EDSL.Corpus.V1.TriangularGCCBase
