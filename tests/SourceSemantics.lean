/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
import EDSL.Source.Memory
import EDSL.Source.Syntax.Coverage
import EDSL.Source.Certificates
import EDSL.Source.VCGen
import EDSL.Source.Division
import EDSL.Source.ConversionContracts
import tests.SourceConversions
import EDSL.Source.PromotionContracts
import tests.SourcePromotions
import EDSL.Source.CastContracts
import tests.SourceCasts
import tests.SourceArithmetic
import tests.SourceConditions
import tests.SourceUnary
import tests.SourceExpressionVC
import tests.SourceObjects
import tests.SourceControl
import tests.SourceControlRules
import tests.SourceControlDivision
import tests.SourceControlVC
import tests.SourceControlDivisionVC
import tests.SourceFunctionVC
import tests.SourceFunctionFailures
import tests.SourceEntryBoundaries
import tests.SourceEntryQuota
import tests.SourceMemory
import tests.SourcePlaceEngine
import tests.SourcePlaceCoverage
import tests.SourceReadOrder
import tests.SourceExpressionCore
import EDSL.Source.GuardContracts
import EDSL.Source.ComparisonContracts
import EDSL.Source.UnaryContracts
import EDSL.Source.Objects
import EDSL.Source.ArithmeticContracts
import EDSL.Audit.Owners

set_option autoImplicit false
set_option warningAsError true

#print axioms EDSL.Source.Examples.add_verified
#print axioms EDSL.Source.Examples.add_certificate
#print axioms EDSL.Source.Examples.divideByZero_not_certified
#print axioms EDSL.Source.Examples.overflowingAdd_undefined
#print axioms EDSL.Source.Examples.underflowingAdd_undefined
#print axioms EDSL.Source.Examples.overflowingDiv_undefined
#print axioms EDSL.Source.Examples.negativeDiv_defined
#print axioms EDSL.Source.Examples.unsupportedReturn_not_certified
#print axioms EDSL.Source.no_certificate_for_empty_domain
#print axioms EDSL.Source.vcExpr_iff
#print axioms EDSL.Source.vc_iff_verifies
#print axioms EDSL.Source.certificate_of_vc
#print axioms EDSL.Source.Division.quotient_verified
#print axioms EDSL.Source.Division.quotient_certificate
#print axioms EDSL.Source.Division.quotient_noUB
#print axioms EDSL.Source.Division.wrappedIncrement_noUB
#print axioms EDSL.Source.Division.wrappedIncrement_counterexample_defined
#print axioms EDSL.Source.Division.counterexample_violates_contract
#print axioms EDSL.Source.Division.wrappedIncrement_not_verified
#print axioms EDSL.Source.Division.wrappedIncrement_not_certified
#print axioms EDSL.Source.IntegerConversions.unsignedToSigned_signedToUnsigned
#print axioms EDSL.Source.IntegerConversions.signedToUnsigned_unsignedToSigned
#print axioms EDSL.Source.ConversionContracts.toUnsigned_certificate
#print axioms EDSL.Source.ConversionContracts.toSigned_certificate
#print axioms EDSL.Source.ConversionContracts.roundTrip_certificate
#print axioms EDSL.Source.ConversionContracts.mixedAdd_certificate
#print axioms EDSL.Source.ConversionContracts.mixedDiv_certificate
#print axioms EDSL.Source.ConversionContracts.toUnsigned_noUB
#print axioms EDSL.Source.ConversionContracts.toSigned_noUB
#print axioms EDSL.Source.ConversionContracts.roundTrip_noUB
#print axioms EDSL.Source.ConversionContracts.mixedAdd_noUB
#print axioms EDSL.Source.ConversionContracts.mixedDiv_noUB
#print axioms EDSL.Source.IntegerPromotions.small_range_embeddable
#print axioms EDSL.Source.IntegerPromotions.promoteValue_toInt
#print axioms EDSL.Source.PromotionContracts.promoteReturn_certificate
#print axioms EDSL.Source.PromotionContracts.promoteReturn_noUB
#print axioms EDSL.Source.PromotionContracts.booleanAdd_certificate
#print axioms EDSL.Source.PromotionContracts.booleanAdd_noUB
#print axioms EDSL.Source.PromotionContracts.unsignedShortAdd32_certificate
#print axioms EDSL.Source.PromotionContracts.unsignedShortAdd16_certificate
#print axioms EDSL.Source.PromotionContracts.unsignedShortAdd32_noUB
#print axioms EDSL.Source.PromotionContracts.unsignedShortAdd16_noUB
#print axioms EDSL.Source.IntegerCasts.castValue_spec
#print axioms EDSL.Source.IntegerCasts.castValue_unique
#print axioms EDSL.Source.IntegerCasts.castValue_preserves
#print axioms EDSL.Source.IntegerCasts.castValue_self
#print axioms EDSL.Source.eval_sadd_defined
#print axioms EDSL.Source.CastContracts.castValue_result
#print axioms EDSL.Source.CastContracts.castReturn_certificate
#print axioms EDSL.Source.CastContracts.castReturn_noUB
#print axioms EDSL.Source.CastContracts.representableRoundTrip_certificate
#print axioms EDSL.Source.CastContracts.representableRoundTrip_noUB
#print axioms EDSL.Source.CastContracts.lowByteAdd_certificate
#print axioms EDSL.Source.CastContracts.lowByteAdd_noUB
#print axioms EDSL.Source.eval_promotedBinary
#print axioms EDSL.Source.eval_usualBinary
#print axioms EDSL.Source.eval_primitiveBinary_defined
#print axioms EDSL.Source.IntegerArithmetic.unsignedSub_spec
#print axioms EDSL.Source.IntegerArithmetic.unsignedMul_spec
#print axioms EDSL.Source.IntegerArithmetic.unsignedRem_spec
#print axioms EDSL.Source.IntegerArithmetic.signedDiv_quotient_fits_iff
#print axioms EDSL.Source.IntegerArithmetic.signedRem_defined_iff
#print axioms EDSL.Source.IntegerArithmetic.signedRem_overflow_iff
#print axioms EDSL.Source.ArithmeticContracts.unsignedReturn_certificate
#print axioms EDSL.Source.ArithmeticContracts.signedReturn_certificate
#print axioms EDSL.Source.ArithmeticContracts.unsignedReturn_noUB
#print axioms EDSL.Source.ArithmeticContracts.signedReturn_noUB
#print axioms EDSL.Source.ArithmeticContracts.subtractAdd_certificate
#print axioms EDSL.Source.ArithmeticContracts.subtractAdd_noUB
#print axioms EDSL.Source.ArithmeticContracts.byteProduct_certificate
#print axioms EDSL.Source.ArithmeticContracts.byteProduct_noUB
#print axioms EDSL.Source.ArithmeticContracts.signedRem_nonzero_not_verified
#print axioms EDSL.Source.ArithmeticContracts.signedRem_nonzero_not_certified
#print axioms EDSL.Source.compareValues_one_iff
#print axioms EDSL.Source.Dialect.logicalValue_toInt
#print axioms EDSL.Source.eval_defined_iff
#print axioms EDSL.Source.Certificate.supported
#print axioms EDSL.Source.Certificate.raw_verified
#print axioms EDSL.Source.no_certificate_with_unsupported
#print axioms EDSL.Source.certificate_iff_supported_useful_raw_vc
#print axioms EDSL.Source.eval_select_zero
#print axioms EDSL.Source.eval_select_nonzero
#print axioms EDSL.Source.eval_promotedCompare
#print axioms EDSL.Source.eval_usualCompare
#print axioms EDSL.Source.GuardContracts.unsignedGuard_observes
#print axioms EDSL.Source.GuardContracts.signedGuard_observes
#print axioms EDSL.Source.GuardContracts.unsignedGuard_branch_safe
#print axioms EDSL.Source.GuardContracts.signedGuard_branch_safe
#print axioms EDSL.Source.GuardContracts.guardedUnsigned_certificate
#print axioms EDSL.Source.GuardContracts.guardedSigned_certificate
#print axioms EDSL.Source.GuardContracts.guardedUnsigned_noUB
#print axioms EDSL.Source.GuardContracts.guardedSigned_noUB
#print axioms EDSL.Source.GuardContracts.nonzeroGuardedSigned_not_verified
#print axioms EDSL.Source.GuardContracts.nonzeroGuardedSigned_not_certified
#print axioms EDSL.Source.eval_logicalAnd
#print axioms EDSL.Source.eval_logicalOr
#print axioms EDSL.Source.conditionalType_c
#print axioms EDSL.Source.conditionalType_cpp_same
#print axioms EDSL.Source.conditionalType_cpp_distinct
#print axioms EDSL.Source.ComparisonContracts.compareReturn_certificate
#print axioms EDSL.Source.ComparisonContracts.compareReturn_noUB
#print axioms EDSL.Source.IntegerUnary.signedNegate_defined_iff
#print axioms EDSL.Source.IntegerUnary.signedNegate_overflow_iff
#print axioms EDSL.Source.IntegerUnary.unsignedComplement_eq_defined_iff
#print axioms EDSL.Source.IntegerUnary.signedComplement_eq_defined_iff
#print axioms EDSL.Source.ComplementBits.nat_sum_iff_bits
#print axioms EDSL.Source.ComplementBits.nat_bits_unique
#print axioms EDSL.Source.ComplementBits.int_sum_iff_bits
#print axioms EDSL.Source.ComplementBits.int_bits_unique
#print axioms EDSL.Source.Expr.firstUnsupported_unary
#print axioms EDSL.Source.eval_unaryMinus
#print axioms EDSL.Source.eval_unaryComplement
#print axioms EDSL.Source.eval_logicalNot_defined
#print axioms EDSL.Source.UnaryContracts.promotedComplement_spec
#print axioms EDSL.Source.UnaryContracts.unaryReturn_certificate
#print axioms EDSL.Source.UnaryContracts.unaryReturn_noUB
#print axioms EDSL.Source.UnaryContracts.unaryMinus_minimum_undefined
#print axioms EDSL.Source.UnaryContracts.signedMinus_all_inputs_not_certified
#print axioms EDSL.Source.ExpressionCore.evalCore_congr_get
#print axioms EDSL.Source.ExpressionCore.evalCore_map
#print axioms EDSL.Source.Objects.EffectM.bind_assoc
#print axioms EDSL.Source.Objects.EffectM.liftScalar_bind
#print axioms EDSL.Source.Objects.PureEmbedding.run_evalExpr
#print axioms EDSL.Source.Objects.PureEmbedding.run_evalProgram
#print axioms EDSL.Source.Objects.PureEmbedding.certificate_has_state
#print axioms EDSL.Source.Objects.load_success_iff
#print axioms EDSL.Source.Objects.store_success_iff
#print axioms EDSL.Source.Objects.store_preserves_wellFormed
#print axioms EDSL.Source.Objects.load_after_store
#print axioms EDSL.Source.Objects.load_other_after_store
#print axioms EDSL.Source.Objects.load_uninitialized_cpp26
#print axioms EDSL.Source.Objects.store_same_value_unauthorized
#print axioms EDSL.Source.Objects.LifecycleContracts.reserve_admission_iff
#print axioms EDSL.Source.Objects.LifecycleContracts.initialize_admission_iff
#print axioms EDSL.Source.Objects.LifecycleContracts.endLifetime_admission_iff
#print axioms EDSL.Source.Objects.LifecycleContracts.initialize_cpp_completion_before_begin
#print axioms EDSL.Source.Objects.LifecycleContracts.declarationCycle_preserves_wellFormed
#print axioms EDSL.Source.Objects.LifecycleContracts.reserve_after_cycle_no_reuse
#print axioms EDSL.Source.Objects.StateSyntax.Program.firstUnsupported_eq_none_iff
#print axioms EDSL.Source.Objects.StateSyntax.Env.get_injective
#print axioms EDSL.Source.Objects.ReadOrder.load_load_diamond
#print axioms EDSL.Source.Objects.CopyIncrement.certificate
#print axioms EDSL.Source.Objects.CopyIncrement.no_failure
#print axioms EDSL.Source.Objects.ObjectWP.wp_store
#print axioms EDSL.Source.Objects.ParameterContracts.enterParameters_contract
#print axioms EDSL.Source.Objects.ExpressionReadOrder.expression_pair_commutes
#print axioms EDSL.Source.Objects.ExpressionVC.vcExpr_iff_wp
#print axioms EDSL.Source.Objects.BlockVC.vcInitializer_iff_wp
#print axioms EDSL.Source.Objects.ExpressionVCChecks.currentObjects
#print axioms EDSL.Source.Objects.ExpressionVCChecks.currentObjectsActual
#print axioms EDSL.Source.Objects.ExpressionVCChecks.skippedUnknown
#print axioms EDSL.Source.Objects.ExpressionVCChecks.demandedUnknown
#print axioms EDSL.Source.Objects.ExpressionVCChecks.repeatedDemand
#print axioms EDSL.Source.Objects.ExpressionVCChecks.cUninitialized
#print axioms EDSL.Source.Objects.ExpressionVCChecks.cppUninitialized
#print axioms EDSL.Source.Objects.ExpressionVCChecks.rejectUninitialized
#print axioms EDSL.Source.Objects.ExpressionVCChecks.scalarFailure
#print axioms EDSL.Source.Objects.ExpressionVCChecks.rejectScalarFailure
#print axioms EDSL.Source.Objects.ExpressionVCChecks.skipUnsupported
#print axioms EDSL.Source.Objects.ExpressionVCChecks.rejectUnsupported
#print axioms EDSL.Source.Objects.ExpressionVCChecks.storeThenLoad
#audit_edsl_owners
