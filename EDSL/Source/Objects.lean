/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
-- Declared objects, finite programs and internal control share the expression
-- engine. Source mapping, memory representation and OS refinement remain open.
import EDSL.Source.Objects.Model
import EDSL.Source.Objects.Effects
import EDSL.Source.Objects.Access
import EDSL.Source.Objects.AccessContracts
import EDSL.Source.Objects.LifecycleContracts
import EDSL.Source.Objects.PureEmbedding
import EDSL.Source.Objects.StateSyntax
import EDSL.Source.Objects.ReadOrder
import EDSL.Source.Objects.StateEval
import EDSL.Source.Objects.Protocol
import EDSL.Source.Objects.StateVC
import EDSL.Source.Objects.BlockEval
import EDSL.Source.Objects.BlockVC
import EDSL.Source.Objects.BlockContracts
import EDSL.Source.Objects.BlockEquations
import EDSL.Source.Objects.ObjectWP
import EDSL.Source.Objects.ParameterContracts
import EDSL.Source.Objects.ExpressionReadOrder
import EDSL.Source.Objects.CopyIncrement
import EDSL.Source.Objects.ExpressionVC
import EDSL.Source.Objects.Control
