/- Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 -/
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
import EDSL.Source.GuardContracts
import EDSL.Source.ComparisonContracts
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
#audit_edsl_owners
