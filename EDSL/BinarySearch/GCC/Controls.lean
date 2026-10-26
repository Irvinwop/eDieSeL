import EDSL.BinarySearch.GCC.Layout

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

run_cmd do
  let options ← Lean.getOptions
  unless options.getBool `autoImplicit true == false &&
      options.getBool `warningAsError false == true &&
      options.getBool `Elab.async true == false &&
      options.get `maxHeartbeats (0 : Nat) == 300000 &&
      options.get `maxRecDepth (0 : Nat) == 128 do
    throwError "GCC graph stage: effective options differ from the required profile"
  Lean.logInfo "EFFECTIVE_OPTIONS autoImplicit=false warningAsError=true Elab.async=false maxHeartbeats=300000 maxRecDepth=128"

namespace EDSL.BinarySearch.GCC
open X86 X86.Sequential

/-- The public default refuses the actual full window before decoding. -/
theorem default_discovery_refuses : CFG.analyze bytes = .error .byteLimit := by
  have nonempty : bytes.isEmpty = false := by decide +kernel
  have oversize : bytes.length > CFG.defaultProfile.maxBytes := by decide +kernel
  simp [CFG.analyze, CFG.analyzeWith, CFG.proposeWith, nonempty, oversize]

theorem default_checker_refuses : CFG.check bytes layout = false := by decide +kernel

theorem default_valid_impossible : ¬ CFG.Valid bytes layout := by
  intro accepted
  have checked := CFG.check_iff.mpr accepted
  rw [default_checker_refuses] at checked
  contradiction

/-- Omitting unreachable padding must fail against the original unchanged
bytes: reachability is insufficient for complete-window admission. -/
def withoutPadding : CFG.Graph :=
  { layout with nodes := layout.nodes.filter (fun node => node.offset != 13) }

theorem missing_padding_refuses :
    CFG.checkWith fullWindowProfile bytes withoutPadding = false := by decide +kernel

/-- An implementation that stops at the sentinel immediate must also fail
against the original bytes, including the actual final RET. -/
def withoutRET : CFG.Graph :=
  { layout with nodes := layout.nodes.filter (fun node => node.offset != 66) }

theorem missing_ret_refuses :
    CFG.checkWith fullWindowProfile bytes withoutRET = false := by decide +kernel

/-- The same closure check also rejects an interior cycle without its loop cut. -/
def withoutLoopCut : CFG.Graph :=
  { layout with nodes := layout.nodes.map (fun node =>
      { node with cutpoint := decide (node.offset = 0) }) }

theorem missing_loop_cut_refuses :
    CFG.checkWith fullWindowProfile bytes withoutLoopCut = false := by decide +kernel

#print axioms default_discovery_refuses
#print axioms default_checker_refuses
#print axioms default_valid_impossible
#print axioms missing_padding_refuses
#print axioms missing_ret_refuses
#print axioms missing_loop_cut_refuses
end EDSL.BinarySearch.GCC
#audit_edsl
