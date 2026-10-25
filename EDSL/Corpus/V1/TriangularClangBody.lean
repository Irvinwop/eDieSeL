/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Arithmetic64.Triangular
import EDSL.WordMath.Triangular32
import EDSL.PureCall.Frame
import EDSL.X86.VCGen.TacticsWith
import EDSL.X86.VCGen.Sub64
import EDSL.X86.VCGen.PureCall
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

namespace EDSL.Corpus.V1.TriangularClangBody
open X86 X86.Sequential X86.VCGen

abbrev spec := Arithmetic64.triangularModulo

/-- All 37 original bytes at Clang c_triangular_mod64, including both RETs. -/
def bytes : List Byte :=
  [0x85,0xff,0x74,0x1e,0x89,0xf9,0x48,0x8d,0x41,0xff,0x8d,0x57,0xff,
   0x48,0x0f,0xaf,0xc2,0x83,0xc7,0xfe,0x48,0x0f,0xaf,0xfa,0x48,0xd1,
   0xef,0x48,0x01,0xc8,0x48,0x29,0xf8,0xc3,0x31,0xc0,0xc3]

/-- Literal untrusted data, authenticated by the production decoder/checker. -/
def graph : CFG.Graph :=
  ⟨[⟨0,.test32 .rdi .rdi false,true,12⟩,
    ⟨2,.je 0x1e,false,11⟩,
    ⟨4,.movReg32 .rcx .rdi,false,10⟩,
    ⟨6,.lea64 .rax (.baseDisp8 .rcx 0xff),false,9⟩,
    ⟨10,.lea32 .rdx (.baseDisp8 .rdi 0xff) false,false,8⟩,
    ⟨13,.imulReg64 .rax .rdx,false,7⟩,
    ⟨17,.addImm32 .rdi 0xfe false,false,6⟩,
    ⟨20,.imulReg64 .rdi .rdx,false,5⟩,
    ⟨24,.shrOne64 .rdi,false,4⟩,
    ⟨27,.addReg64 .rax .rcx,false,3⟩,
    ⟨30,.subReg64 .rax .rdi,false,2⟩,
    ⟨33,.legacy .ret,false,1⟩,
    ⟨34,.xorSelf32 .rax,false,2⟩,
    ⟨36,.legacy .ret,false,1⟩],12⟩

theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide +kernel)
abbrev entry : graph.Index := ⟨0,by decide +kernel⟩
@[simp] theorem entry_offset : (graph.node entry).offset = 0 := rfl

def scratch : List Register := [.rax,.rcx,.rdx,.rdi]
def retired (input : BitVec 32) : Nat := if input = 0 then 4 else 12
def stackRead (initial : State) : Read := ⟨.stack,initial.registers .rsp,8⟩

/-- Full result and caller frame, exact ordered read and modeled retirement. -/
def Observed (input : PureCall.Invocation spec) (initial : State) (result : Result) : Prop :=
  PureCall.Post spec input initial result.state ∧
    PureCall.ScratchFrame (.rsp :: scratch) initial result.state ∧
    result.instructions = retired input.value ∧ result.reads = [stackRead initial]

private theorem saved_protected :
    ∀ register ∈ PureCall.calleeSaved, register ≠ .rsp ∧ register ∉ scratch := by
  decide +kernel

private theorem observed_of_frame {input : PureCall.Invocation spec}
    {initial : State} {result : Result}
    (frame : PureCall.ScratchFrame (.rsp :: scratch) initial result.state)
    (correct : spec.result input.value (result.state.registers .rax))
    (returnAddress : result.state.rip = input.returnAddress)
    (stackPointer : result.state.registers .rsp = initial.registers .rsp + 8)
    (count : result.instructions = retired input.value)
    (reads : result.reads = [stackRead initial]) : Observed input initial result :=
  ⟨frame.post_return saved_protected correct returnAddress stackPointer,frame,count,reads⟩

private theorem minus_one : (0xff : Byte).signExtend 64 = -(1 : Word) := by decide +kernel

/-- Full64 arithmetic is evaluated before narrowing; its high bits are unrestricted. -/
private theorem low_pred (value : Word) :
    ((value + (0xff : Byte).signExtend 64).setWidth 32).setWidth 64 =
      ((value.setWidth 32) - 1).setWidth 64 := by
  rw [BitVec.setWidth_add _ _ (by decide : 32 ≤ 64)]
  have displacement : ((0xff : Byte).signExtend 64).setWidth 32 = -(1 : BitVec 32) := by
    decide +kernel
  rw [displacement,BitVec.add_neg_eq_sub]

private theorem wide_pred (value : BitVec 32) (nonzero : value ≠ 0) :
    value.setWidth 64 + (0xff : Byte).signExtend 64 = (value - 1).setWidth 64 := by
  have positive : 0 < value.toNat := by
    have nz : value.toNat ≠ 0 := by
      intro bad
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      simpa using bad
    omega
  rw [minus_one,BitVec.add_neg_eq_sub]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le,BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
    BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),BitVec.toNat_sub_of_le]
  · rfl
  · change (1 : Nat) ≤ value.toNat
    omega
  · change (1 : Nat) ≤ (value.setWidth 64).toNat
    rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
    omega

private theorem machine_expression_contract (value : Word) (input : BitVec 32)
    (bound : value.setWidth 32 = input) (nonzero : input ≠ 0) :
    WordMath.TriangularModulo input.toNat
      ((input.setWidth 64 + (0xff : Byte).signExtend 64) *
        (((value + (0xff : Byte).signExtend 64).setWidth 32).setWidth 64) +
        input.setWidth 64 -
        ((((value.setWidth 32 + (0xfe : Byte).signExtend 32).setWidth 64) *
          (((value + (0xff : Byte).signExtend 64).setWidth 32).setWidth 64)) >>> 1)) := by
  rw [wide_pred input nonzero,low_pred,bound,WordMath.add_negative_two32]
  simpa only [WordMath.reducedTriangular32,nonzero,↓reduceIte] using
    WordMath.reducedTriangular32_contract input

private theorem result_of_low32 (value : Word) (input : BitVec 32)
    (bound : value.setWidth 32 = input) (output : Word)
    (correct : WordMath.TriangularModulo (value.setWidth 32).toNat output) :
    spec.result input output := by
  cases bound
  exact correct

private theorem test_zero_bit (old : Word) (value : BitVec 32) (af : Bool) :
    (logicalFlags32 old value af)[6] = (value == 0) := by
  change (logicalFlags32 old value af).getLsbD 6 = (value == 0)
  exact logicalFlags32_zero old value af

/-- Universal production vector WP: arbitrary high input bits, scratch, flags,
and independent FlagChoices at every instruction. No signed IMUL fit premise. -/
theorem generated_vc (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) :
    wpWith graph initial.rip (PureCallAllowed initial) 12 entry initial
      (Observed input initial) := by
  have stack := pre.stack
  have target := pre.returnCanonical
  have argument := (Arithmetic64.triangularModulo_bound_iff input.value initial).mp pre.arguments
  have exitCanonical : canonical (initial.rip + BitVec.ofNat 64 34) = true :=
    code_canonical_offset pre.code 34 (by decide +kernel)
  by_cases zero : (initial.registers .rdi).setWidth 32 = (0 : BitVec 32)
  · vcgen_runWith graph entry simp [PureCallAllowed,PureCall.RawRead,zero,
      BitVec.add_assoc,test_zero_bit,exitCanonical,stack,target]
    vcgen_factor =>
      refine observed_of_frame ?_ ?_ rfl rfl ?_ rfl
      · constructor
        · rfl
        · simp only [Result.prepend,logicalFlags32_preserves]
        · intro register untouched
          simp only [scratch,List.mem_cons,not_or] at untouched
          rcases untouched with ⟨notSP,notA,_notC,_notD,_notDI⟩
          simp only [Result.prepend,notSP,notA,ite_false]
      · apply result_of_low32 (initial.registers .rdi) input.value argument
        change WordMath.TriangularModulo ((initial.registers .rdi).setWidth 32).toNat (0#64)
        simpa only [zero,WordMath.reducedTriangular32,↓reduceIte,BitVec.ofNat_eq_ofNat] using
          WordMath.reducedTriangular32_contract ((initial.registers .rdi).setWidth 32)
      · change 4 = retired input.value
        calc
          4 = retired ((initial.registers .rdi).setWidth 32) := by simp [retired,zero]
          _ = retired input.value := congrArg retired argument
  · simp only [BitVec.ofNat_eq_ofNat] at zero
    vcgen_runWith graph entry simp [PureCallAllowed,PureCall.RawRead,BitVec.and_self,
      BitVec.add_assoc,test_zero_bit,zero,stack,target,sub64State]
    vcgen_factor =>
      refine observed_of_frame ?_ ?_ rfl rfl ?_ rfl
      · constructor
        · rfl
        · simp only [Result.prepend,cmpFlags64_preserves,addFlags64_preserves,
            shrOneFlags64_preserves,imulFlags64_preserves,addFlags32_preserves,
            logicalFlags32_preserves]
        · intro register untouched
          simp only [scratch,List.mem_cons,not_or] at untouched
          rcases untouched with ⟨notSP,notA,notC,notD,notDI⟩
          simp only [Result.prepend,notSP,notA,notC,notD,notDI,ite_false]
      · apply result_of_low32 (initial.registers .rdi) input.value argument
        exact machine_expression_contract (initial.registers .rdi)
          ((initial.registers .rdi).setWidth 32) rfl zero
      · change 12 = retired input.value
        calc
          12 = retired ((initial.registers .rdi).setWidth 32) := by simp [retired,zero]
          _ = retired input.value := congrArg retired argument

theorem executes (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) (choices : ChoiceStream FlagChoices) :
    ∃ result, runWith choices 12 initial = .ok result ∧ Observed input initial result ∧
      CheckedTraceWith (PureCallAllowed initial) choices initial result := by
  obtain ⟨result,actual,observed,_,trace⟩ := run_soundWith valid pre.code
    (by simp) (generated_vc input initial pre) choices
  exact ⟨result,actual,observed,trace⟩

theorem semantics (input : PureCall.Invocation spec) (initial : State)
    (pre : PureCall.Pre spec bytes input initial) :
    AllExecutionsWith initial (Observed input initial) := by
  intro choices
  obtain ⟨result,actual,observed,_⟩ := executes input initial pre choices
  exact ⟨result,Engine.run_sound stepWith actual,observed⟩

theorem observations {input : PureCall.Invocation spec} {initial : State}
    (pre : PureCall.Pre spec bytes input initial) {choices : ChoiceStream FlagChoices}
    {result : Result} (execution : ExecutesWith choices initial result) :
    Observed input initial result := by
  obtain ⟨verified,actual,observed,_⟩ := executes input initial pre choices
  have same := Engine.Executes.fixed_choices_unique stepWith execution
    (Engine.run_sound stepWith actual)
  subst verified
  exact observed

#print axioms valid
#print axioms generated_vc
#print axioms executes
#print axioms semantics
#print axioms observations
end EDSL.Corpus.V1.TriangularClangBody
#audit_edsl
