import EDSL.X86.VCGen.Tactics

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

namespace EDSL.X86.VCGen
open Sequential

deriving instance Lean.ToExpr for Register
deriving instance Lean.ToExpr for X86.Instruction
deriving instance Lean.ToExpr for Condition
deriving instance Lean.ToExpr for Address
deriving instance Lean.ToExpr for LogicalOp
deriving instance Lean.ToExpr for ShiftRightOp
deriving instance Lean.ToExpr for NopEncoding
deriving instance Lean.ToExpr for Sequential.Instruction
deriving instance Lean.ToExpr for CFG.Node
deriving instance Lean.ToExpr for CFG.Graph

syntax (name := vcgenProposal) "vcgen_proposal " term : term
syntax (name := vcgenCFGData) "vcgen_cfg_data " term : term

/-- Evaluate existing production discovery to propose finite graph data.
Evaluation and reification are untrusted: the client must independently prove
CFG.Valid against the unchanged bytes. This emits no proposition or proof and
adds no decoder, executor, instruction or semantic admission rule. -/
@[term_elab vcgenProposal] unsafe def elaborateProposal : Lean.Elab.Term.TermElab := fun stx _ => do
  let `(vcgen_proposal $bytes:term) := stx | Lean.Elab.throwUnsupportedSyntax
  let proposalSyntax ← `(Sequential.CFG.discover $bytes:term)
  let proposed ← Lean.Elab.Term.elabTerm proposalSyntax none
  let proposedType ← Lean.Meta.inferType proposed
  let result ← Lean.Meta.evalExpr (Option CFG.Graph) proposedType proposed
  let some graph := result |
    throwError "vcgen_proposal: production proposal failed"
  return Lean.toExpr graph

/-- Reify proposed annotations as shallow finite data. This remains untrusted
data, with every field independently checked by CFG.Valid at the consumer. -/
@[term_elab vcgenCFGData] unsafe def elaborateCFGData : Lean.Elab.Term.TermElab := fun stx _ => do
  let `(vcgen_cfg_data $data:term) := stx | Lean.Elab.throwUnsupportedSyntax
  let graph ← Lean.Elab.Term.evalTerm CFG.Graph (Lean.mkConst ``CFG.Graph) data
  return Lean.toExpr graph

end EDSL.X86.VCGen
