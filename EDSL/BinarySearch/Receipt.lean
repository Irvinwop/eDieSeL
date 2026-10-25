import EDSL.BinarySearch.Clang.Resources
import EDSL.BinarySearch.Controls

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 128

#check @EDSL.BinarySearch.Clang.layout_valid
#check @EDSL.BinarySearch.Clang.generated
#check @EDSL.BinarySearch.Clang.raw
#check @EDSL.BinarySearch.Clang.semantics
#check @EDSL.BinarySearch.Clang.resources
#check @EDSL.BinarySearch.Clang.attached_resources
#check @EDSL.BinarySearch.sentinel_iff_absent
#print EDSL.BinarySearch.spec
#print EDSL.BinarySearch.Result
#print EDSL.BinarySearch.Input
#print axioms EDSL.BinarySearch.Clang.semantics
#print axioms EDSL.BinarySearch.Clang.attached_resources
#print axioms EDSL.BinarySearch.Controls.rejects_truncated_sentinel
#print axioms EDSL.BinarySearch.Controls.rejects_out_of_range
#print axioms EDSL.BinarySearch.Controls.rejects_false_absence
#print axioms EDSL.BinarySearch.Controls.empty_rejects_data
#print axioms EDSL.BinarySearch.Controls.rejects_omitted_padding
#print axioms EDSL.BinarySearch.Controls.rejects_omitted_final_ret
#audit_edsl
