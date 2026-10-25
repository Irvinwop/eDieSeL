/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Sub64
import EDSL.X86.VCGen.Effects
import EDSL.OS.CallResources.Domain
import EDSL.Audit
import tests.Support.ExceptDecidable

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.Sub64StoreAuthority
open X86 X86.Sequential OS OS.AddressSpace OS.CallResources
open scoped EDSL.Tests.Support

/- SUB RDI,8; MOV DWORD PTR [RDI],ESI; RET. The caller mapping is physically
writable but remains frozen by its live borrowing loan. This is synthetic code
and a newly declared modeled world, not a finding about an external binary. -/
def bytes : List Byte := [0x48,0x83,0xef,8,0x89,0x37,0xc3]

def supplied : Space where
  cells address :=
    if (⟨0x1000,bytes.length⟩ : Region).Contains address then
      (bytes[address.toNat - 0x1000]?).map fun byte => ⟨byte,readExecute⟩
    else if (⟨0x2008,8⟩ : Region).Contains address then
      some ⟨(0x3000 : Word).extractLsb' ((address.toNat - 0x2008) * 8) 8,readWrite⟩
    else none

def declared : Domain.Initial := ⟨supplied,17,29,41,0x1000,bytes,0x2008,0x3000⟩
def before : State := Domain.machine declared
  (fun register => if register = .rdi then 0x2010
    else if register = .rsi then 0x11223344 else 0xfedcba9876543210) 0xad7
def middle : State := sub64State before .rdi 8 4
def after : State :=
  { middle with
    memory := writeDWordUnchecked middle.memory 0x2008 0x11223344
    rip := middle.rip + 2 }

def graph : CFG.Graph :=
  ⟨[⟨0,.subImm64 .rdi 8,true,2⟩,⟨4,.legacy .storeEsiRdi,false,1⟩,
    ⟨6,.legacy .ret,false,0⟩],2⟩
def entry : graph.Index := ⟨0,by decide⟩
private def storeNode : graph.Index := ⟨1,by decide⟩

/-- Ordinary stores must pass the actual borrowing mutation gate using the
original caller owner's ticket. Raw writable memory is not that permission.
This private policy grants no mutable data resource or 64-bit store authority. -/
def policy : X86.VCGen.Effects.Policy where
  Current := Current (Domain.call declared) (Domain.shared declared)
  AllowedRead := fun _ read => ReadAllowed (Domain.call declared) (Domain.shared declared) read
  AllowedEffect state instruction _ :=
    match instruction.storeIntent state with
    | some (address,value) => ∃ evolved,
        Borrowing.mutate (Domain.shared declared) (.store 29 Domain.stackTicket address value) =
          .ok (evolved,none)
    | none => CFG.readOnly instruction = true

/-- A genuine SUB-derived pointer is used by a physically successful decoded
store. Its actual bytes change while executable text remains authenticated;
no memory failure or text-overlap check explains the ownership rejection. -/
theorem actual_sub_then_store (choices : ChoiceStream FlagChoices) :
    CFG.Structural.Valid bytes graph ∧ CodeAt before.memory 0x1000 bytes ∧
    Current (Domain.call declared) (Domain.shared declared) before ∧
    stepWith (choices 0) before = .ok ⟨.next middle,[]⟩ ∧
    Current (Domain.call declared) (Domain.shared declared) middle ∧
    middle.registers .rdi = 0x2008 ∧
    Sequential.decodeAt middle = .ok (.legacy .storeEsiRdi) ∧
    stepWith (choices 1) middle = .ok ⟨.next after,[]⟩ ∧
    readWord after.memory 0x2008 = .ok 0x11223344 ∧ CodeAt after.memory 0x1000 bytes := by
  have current : Current (Domain.call declared) (Domain.shared declared) before :=
    Domain.current (Domain.check_sound (by decide +kernel)) _ _
  have valid : CFG.Structural.Valid bytes graph := CFG.Structural.check_sound (by decide +kernel)
  have code : CodeAt before.memory 0x1000 bytes := by
    rw [current.coupled]
    exact current.contract.code
  have middleMemory : middle.memory = before.memory := (sub64State_contract before .rdi 8 4).memory
  have middlePC : middle.rip = 0x1004 := by
    change (sub64State before .rdi 8 4).rip = 0x1004
    rw [(sub64State_contract before .rdi 8 4).nextPC]
    change (0x1000 : Word) + 4 = 0x1004
    decide +kernel
  have pointer : middle.registers .rdi = 0x2008 := by
    change before.registers .rdi - 8 = 0x2008
    have operand : before.registers .rdi = 0x2010 := rfl
    rw [operand]
    decide +kernel
  have source : (middle.registers .rsi).setWidth 32 = 0x11223344 := by
    change ((sub64State before .rdi 8 4).registers .rsi).setWidth 32 = 0x11223344
    rw [(sub64State_contract before .rdi 8 4).registerFrame .rsi (by decide)]
    change (0x11223344 : Word).setWidth 32 = 0x11223344
    decide +kernel
  have subDecoded : Sequential.decodeAt before = .ok (.subImm64 .rdi 8) :=
    valid.decoded code entry before rfl (by rfl)
  have storeDecoded : Sequential.decodeAt middle = .ok (.legacy .storeEsiRdi) :=
    valid.decoded code storeNode middle middleMemory middlePC
  have first : stepWith (choices 0) before = .ok ⟨.next middle,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 0) subDecoded]
    simpa only [middle,show (8 : Byte).signExtend 64 = (8 : Word) from by decide +kernel]
      using executeWith_subImm64 before .rdi 8 (choices 0)
  have intent : (Sequential.Instruction.legacy .storeEsiRdi).storeIntent middle =
      some (0x2008,0x11223344) := by
    simp only [Sequential.Instruction.storeIntent,X86.Instruction.storeIntent,pointer,source]
  have writable : canStoreDWord middle.memory 0x2008 = true := by
    rw [middleMemory]
    change canStoreDWord (toMemory supplied) 0x2008 = true
    decide +kernel
  have second : stepWith (choices 1) middle = .ok ⟨.next after,[]⟩ := by
    rw [stepWith_eq_executeWith (choices 1) storeDecoded,
      executeWith_eq_execute middle (.legacy .storeEsiRdi) (choices 1) rfl,
      execute_storeIntent_checked _ intent,writable]
    rfl
  refine ⟨valid,code,current,first,current.sameMemory middleMemory,pointer,storeDecoded,second,?_,?_⟩
  · change readWord (writeDWordUnchecked middle.memory 0x2008 0x11223344) 0x2008 = _
    rw [middleMemory]
    change readWord (writeDWordUnchecked (toMemory supplied) 0x2008 0x11223344) 0x2008 = _
    decide +kernel
  · exact ELF.checkCode_sound _ _ _ (by decide +kernel)

private theorem borrowed_store_refused :
    Borrowing.mutate (Domain.shared declared)
      (.store 29 Domain.stackTicket 0x2008 0x11223344) = .error .borrowed := rfl

/-- The production effect WP composes the actual SUB and its real store
successor before enforcing current borrowing authority. Every fuel budget
and independent postcondition rejects, including True, despite the successful
machine store above. This is a rejection result, not an effect-trace safety
or OS-world evolution theorem for unauthorized machine execution. -/
theorem unauthorized_store_rejected (fuel : Nat) (Post : X86.VCGen.Effects.Contract) :
    ¬X86.VCGen.Effects.wp graph 0x1000 policy fuel entry before Post := by
  cases fuel with
  | zero => exact id
  | succ remaining =>
    intro vc
    have first := vc.2 (FlagChoices.uniform false)
    obtain ⟨next,_,binding,tail⟩ := first.2.2
    have unique : ∀ index : graph.Index,
        (0x1004 : Word) = 0x1000 + BitVec.ofNat 64 (graph.node index).offset →
          index = storeNode := by decide +kernel
    have same := unique next binding
    subst next
    cases remaining with
    | zero => exact tail
    | succ remaining =>
      have second := tail.2 (FlagChoices.uniform false)
      have authorized := second.2.1
      change ∃ evolved, Borrowing.mutate (Domain.shared declared)
        (.store 29 Domain.stackTicket 0x2008 0x11223344) = .ok (evolved,none) at authorized
      obtain ⟨_,impossible⟩ := authorized
      rw [borrowed_store_refused] at impossible
      cases impossible

end EDSL.Tests.Sub64StoreAuthority

#print axioms EDSL.Tests.Sub64StoreAuthority.actual_sub_then_store
#print axioms EDSL.Tests.Sub64StoreAuthority.unauthorized_store_rejected
#audit_edsl
