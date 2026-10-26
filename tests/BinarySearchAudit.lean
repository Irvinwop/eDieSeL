/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.BinarySearch.Receipt
import EDSL.BinarySearch.Clang.CallableProperties
import EDSL.BinarySearch.Clang.NamedELFControls
import EDSL.BinarySearch.GCC.Resources
import EDSL.BinarySearch.GCC.Controls
import EDSL.X86.VCGen.BranchControls
import EDSL.Audit.Owners

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
set_option Elab.async false

-- Audit actual imported module owners, including private and generated names.
#audit_edsl_owners
