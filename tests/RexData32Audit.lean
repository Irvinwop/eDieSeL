/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import tests.RexData32Decode
import tests.RexData32Execute
import tests.RexData32Faults
import tests.RexData32CFG
import tests.RexData32Resources
import tests.RexData32TSO
import tests.DisplacedDataDecode
import tests.DisplacedDataExecute
import tests.DisplacedDataFaults
import tests.SequentialMoveResources
import tests.SequentialMemory64
import tests.SequentialMoves64
import EDSL.X86.Sequential.Literals
import EDSL.X86.Sequential.DisplacedData
import EDSL.OS.WordResources
import EDSL.X86.CallReturn.Facts
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.X86.VCGen.Choices
import EDSL.X86.VCGen.Effects
import EDSL.OS.TSO64.Model
import EDSL.X86.VCGen.ManagedRules
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 128
#print axioms EDSL.X86.Sequential.execute_loadMem32Rex_context
#print axioms EDSL.X86.Sequential.execute_loadMem32Rex_success_iff
#print axioms EDSL.X86.Sequential.decodeAt_transport
#print axioms EDSL.OS.WordResources.current_load32Rex_step
#print axioms EDSL.X86.CallReturn.execute_liftSequential
#print axioms EDSL.X86.VCGen.sound
#print axioms EDSL.Tests.RexData32CFG.checked_load_return
#print axioms EDSL.Tests.RexData32Resources.admitted_rsp
#print axioms EDSL.Tests.RexData32TSO.pending_load
#print axioms EDSL.X86.VCGen.Effects.sound
#print axioms EDSL.Tests.RexData32CFG.checked_vector_load_return
#print axioms EDSL.Tests.RexData32CFG.checked_effect_load_return
#print axioms EDSL.X86.VCGen.ManagedRules.issue_ordinary
#audit_edsl
