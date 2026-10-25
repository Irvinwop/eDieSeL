/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.Sub64
import EDSL.Audit
import tests.Support.ExceptDecidable

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.Tests.Sub64IntegrationCFG
open X86 X86.Sequential
open scoped EDSL.Tests.Support

/- Synthetic project-owned code. All graphs use the unchanged default profile.
SUB RDI,RSI; Jcc taken; MOV EAX,17; RET; taken: MOV EAX,34; RET.
The path marker does not overwrite the subtraction result in RDI. -/
def bytes (opcode : Byte) : List Byte :=
  [0x48,0x29,0xf7, opcode,0x06, 0xb8,0x11,0,0,0,0xc3, 0xb8,0x22,0,0,0,0xc3]

def graph (condition : Condition) : CFG.Graph :=
  ⟨[⟨0,.subReg64 .rdi .rsi,true,3⟩,
    ⟨3,.jcc condition 6,false,2⟩,
    ⟨5,.legacy (.mov32 .rax 17),false,1⟩,
    ⟨10,.legacy .ret,false,0⟩,
    ⟨11,.legacy (.mov32 .rax 34),false,1⟩,
    ⟨16,.legacy .ret,false,0⟩],3⟩

def start (condition : Condition) : (graph condition).Index := ⟨0,by change 0 < 6; decide⟩

/-- Literal architectural expectations, independent of flag/branch helpers.
Both overflow directions are used for each of JB, JL and JGE. -/
structure Scenario where
  opcode : Byte
  condition : Condition
  left : Word
  right : Word
  difference : Word
  marker : Word
  flags : Word
  successor : Word

private def minimumBelow : Scenario :=
  ⟨0x72,.below,0x8000000000000000,1,0x7fffffffffffffff,17,0xa16,0x1005⟩

def scenarios : List Scenario := [minimumBelow,
  ⟨0x7c,.less,0x8000000000000000,1,0x7fffffffffffffff,34,0xa16,0x100b⟩,
  ⟨0x7d,.greaterEqual,0x8000000000000000,1,0x7fffffffffffffff,17,0xa16,0x1005⟩,
  ⟨0x72,.below,0x7fffffffffffffff,0xffffffffffffffff,0x8000000000000000,34,0xa87,0x100b⟩,
  ⟨0x7c,.less,0x7fffffffffffffff,0xffffffffffffffff,0x8000000000000000,17,0xa87,0x1005⟩,
  ⟨0x7d,.greaterEqual,0x7fffffffffffffff,0xffffffffffffffff,0x8000000000000000,34,0xa87,0x100b⟩]

private def memory (code : List Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length then
      code[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0,0x30,0,0,0,0,0,0] : List Byte)[address.toNat - 0x2000]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length)

def initial (scenario : Scenario) : State where
  registers register :=
    if register = .rsp then 0x2000
    else if register = .rdi then scenario.left
    else if register = .rsi then scenario.right
    else 0xfedcba9876543210
  rip := 0x1000
  flags := 0xad7
  memory := memory (bytes scenario.opcode)

def Allowed (_ : State) (read : Read) : Prop := read = ⟨.stack,0x2000,8⟩

def Post (scenario : Scenario) (result : Result) : Prop :=
  result.state.registers .rdi = scenario.difference ∧
  result.state.registers .rax = scenario.marker ∧
  result.state.registers .rsp = 0x2008 ∧ result.state.rip = 0x3000 ∧
  result.state.flags = scenario.flags ∧ result.instructions = 4 ∧
  result.reads = [⟨.stack,0x2000,8⟩]

private instance (state : State) (read : Read) : Decidable (Allowed state read) :=
  inferInstanceAs (Decidable (read = ⟨.stack,0x2000,8⟩))

private instance (scenario : Scenario) : DecidablePred (Post scenario) := by
  intro result
  unfold Post
  infer_instance

private instance (cfg : CFG.Graph) (base : Word) (fuel : Nat)
    (node : cfg.Index) (state : State) (contract : X86.VCGen.Contract)
    [DecidablePred contract] :
    Decidable (X86.VCGen.wp cfg base Allowed fuel node state contract) :=
  X86.VCGen.decidableWP _ _ _ (fun _ _ => inferInstance) _ _ _ _ (fun _ => inferInstance)

def accepts (scenario : Scenario) : Bool :=
  X86.VCGen.certify (bytes scenario.opcode) (graph scenario.condition) 0x1000
    Allowed 4 (start scenario.condition) (initial scenario) (Post scenario)

/-- Complete admission checks the actual executable RAM, entry PC, decoded
CFG and generated production WP. Signed ordering must use SF xor OF: the
wrapped result has the opposite sign to the mathematical difference here. -/
theorem authenticated_overflow_paths : scenarios.all accepts = true := by
  decide +kernel

private def successorView (scenario : Scenario) : Except Error (Word × Word × Word × List Read) := do
  let first ← Sequential.step false (initial scenario)
  match first.result with
  | .next middle =>
    let second ← Sequential.step true middle
    match second.result with
    | .next after => return (after.rip,after.registers .rdi,after.flags,first.reads ++ second.reads)
    | _ => throw .unexpectedReturn
  | _ => throw .unexpectedReturn

/-- Observe RIP immediately after the branch, before either path marker or
RET. This catches an incorrect successor even if later paths reconverge. -/
theorem exact_dynamic_successors : scenarios.all (fun scenario => decide
    (successorView scenario = .ok (scenario.successor,scenario.difference,scenario.flags,[]))) = true := by
  decide +kernel

/-- Every listed case yields an actual decoded run and an authorized read
trace, for an arbitrary complete Bool choice stream; no successful execution
is an input premise. Exact retired cost and ordered reads are in Post. -/
theorem every_case_runs (scenario : Scenario) (listed : scenario ∈ scenarios) (choices : Choices) :
    ∃ result, Sequential.run choices 4 (initial scenario) = .ok result ∧ Post scenario result ∧
      result.instructions ≤ 4 ∧
      X86.VCGen.CheckedTrace Allowed choices (initial scenario) result := by
  have accepted : accepts scenario = true :=
    List.all_eq_true.mp authenticated_overflow_paths scenario listed
  exact X86.VCGen.certify_sound accepted choices

private def missingGraph : CFG.Graph :=
  { graph .below with nodes := (graph .below).nodes.filter fun node => node.offset != 3 }

private def missingStart : missingGraph.Index := ⟨0,by decide⟩

/-- Deleting the immediate SUB successor is rejected both structurally and
by the dynamic WP, even with a permissive postcondition and ample fuel. -/
theorem missing_successor_rejected :
    CFG.check (bytes 0x72) missingGraph = false ∧
    X86.VCGen.check missingGraph 0x1000 Allowed 4 missingStart (initial minimumBelow)
      (fun _ => True) = false := by
  letI := X86.VCGen.decidableWP missingGraph 0x1000 Allowed
    (fun _ _ => inferInstance) 4 missingStart (initial minimumBelow) (fun _ => True)
    (fun _ => inferInstance)
  refine ⟨by decide +kernel,?_⟩
  have rejected : ¬X86.VCGen.wp missingGraph 0x1000 Allowed 4 missingStart
      (initial minimumBelow) (fun _ => True) := by
    intro vc
    obtain ⟨next,binding,_⟩ :=
      (X86.VCGen.wp_subReg64_iff missingGraph 0x1000 Allowed 3 missingStart
        (initial minimumBelow) (fun _ => True) .rdi .rsi rfl).mp vc
    have absent : ∀ index : missingGraph.Index,
        (0x1003 : Word) ≠ 0x1000 + BitVec.ofNat 64 (missingGraph.node index).offset := by
      decide +kernel
    exact absent next binding
  simp only [X86.VCGen.check,decide_eq_false_iff_not]
  exact rejected

/-- Zero and three instructions cannot certify this four-instruction path.
An otherwise sufficient budget cannot certify the wrong exact retired count. -/
theorem fuel_and_retirement_rejected :
    X86.VCGen.certify (bytes 0x72) (graph .below) 0x1000 Allowed 0 (start .below)
      (initial minimumBelow) (Post minimumBelow) = false ∧
    X86.VCGen.certify (bytes 0x72) (graph .below) 0x1000 Allowed 3 (start .below)
      (initial minimumBelow) (Post minimumBelow) = false ∧
    X86.VCGen.certify (bytes 0x72) (graph .below) 0x1000 Allowed 4 (start .below)
      (initial minimumBelow) (fun result => result.instructions = 3) = false := by
  decide +kernel

/- A real SUB successor is now a cutpoint. The independent invariant demands
its wrapped result and retained original RSP; the natural rank must strictly
decrease from the initial unsigned magnitude. -/
private def cutGraph : CFG.Graph :=
  { graph .below with nodes := (graph .below).nodes.map fun node =>
      { node with cutpoint := node.cutpoint || decide (node.offset = 3) } }

private def cutStart : cutGraph.Index := ⟨0,by decide⟩

private def cutAccepts (expected : Word) (flat : Bool) : Bool :=
  let inv := fun (_ : cutGraph.Index) (state : State) =>
    state.registers .rdi = expected ∧ state.registers .rsp = 0x2000
  let rank := fun (_ : cutGraph.Index) (state : State) =>
    if flat then 0x8000000000000000 else (state.registers .rdi).toNat
  letI := X86.VCGen.Cutpoints.decidableWP cutGraph 0x1000 (fun _ => True) Allowed
    inv rank 0x8000000000000000 (fun _ => inferInstance) (fun _ _ => inferInstance)
    (fun _ _ => inferInstance) 1 cutStart (initial minimumBelow)
  decide (X86.VCGen.Cutpoints.wp cutGraph 0x1000 (fun _ => True) Allowed
    inv rank 0x8000000000000000 1 cutStart (initial minimumBelow))

/-- The positive control reaches the authenticated cutpoint. Retaining the
old destination as invariant, or making the rank equal to its budget, fails.
These failures concern SUB's actual successor, not a fabricated self-loop. -/
theorem cutpoint_controls :
    CFG.check (bytes 0x72) cutGraph = true ∧
    cutAccepts 0x7fffffffffffffff false = true ∧
    cutAccepts 0x8000000000000000 false = false ∧
    cutAccepts 0x7fffffffffffffff true = false := by
  refine ⟨by decide +kernel,?_,by decide +kernel,by decide +kernel⟩
  unfold cutAccepts
  simp only [decide_eq_true_eq]
  apply (X86.VCGen.Cutpoints.wp_subReg64_iff cutGraph 0x1000 (fun _ => True) Allowed
    (fun _ state => state.registers .rdi = 0x7fffffffffffffff ∧ state.registers .rsp = 0x2000)
    (fun _ state => (state.registers .rdi).toNat) 0x8000000000000000 0 cutStart
    (initial minimumBelow) .rdi .rsi rfl).mpr
  refine ⟨⟨1,by decide⟩,by decide +kernel,?_⟩
  simp only [show cutGraph.cutpoint ⟨1,by decide⟩ = true from rfl, ↓reduceIte]
  decide +kernel

end EDSL.Tests.Sub64IntegrationCFG

#print axioms EDSL.Tests.Sub64IntegrationCFG.authenticated_overflow_paths
#print axioms EDSL.Tests.Sub64IntegrationCFG.exact_dynamic_successors
#print axioms EDSL.Tests.Sub64IntegrationCFG.every_case_runs
#print axioms EDSL.Tests.Sub64IntegrationCFG.missing_successor_rejected
#print axioms EDSL.Tests.Sub64IntegrationCFG.fuel_and_retirement_rejected
#print axioms EDSL.Tests.Sub64IntegrationCFG.cutpoint_controls
#audit_edsl
