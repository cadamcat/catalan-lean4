import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticHilbertClassFieldReciprocity
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealDecompositionLaw
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CyclicPrimePowerFullDecomposition
import Catalan

#check @Catalan.cassels_coprime_power_factors
#check @Catalan.cassels_cyclo_exact_valuation
#check @Catalan.cassels_coeff_denominator
#check @Catalan.cassels_coeff_padicValRat
#check @Catalan.cassels_remainder_bound
#check @Catalan.cassels_p_dvd_y
#check @Catalan.cassels_q_dvd_x
#check @Catalan.cassels_factorization
#check @Catalan.ipow_principalIdeal
#check @Catalan.principal_of_integral_factorization

#print axioms Catalan.cassels_coprime_power_factors
#print axioms Catalan.cassels_cyclo_exact_valuation
#print axioms Catalan.cassels_coeff_denominator
#print axioms Catalan.cassels_coeff_padicValRat
#print axioms Catalan.cassels_power_taylor_bound
#print axioms Catalan.cassels_root_correction_bound
#print axioms Catalan.cassels_remainder_bound
#print axioms Catalan.cassels_p_dvd_y
#print axioms Catalan.cassels_q_dvd_x
#print axioms Catalan.cassels_factorization
#print axioms Catalan.ipow_add
#print axioms Catalan.ipow_mul
#print axioms Catalan.ipow_zsmul
#print axioms Catalan.ipow_principalIdeal
#print axioms Catalan.principal_of_integral_factorization

#check @Catalan.ζ_spec
#check @Catalan.σ_apply_ζ
#check @Catalan.weight_mul
#check @Catalan.size_mul_le
#check @Catalan.upow_mul
#check @Catalan.fractionalIdeal_prime_induction
#check @Catalan.prime_over_p_principal
#check @Catalan.DensityInput
#check @Catalan.A3.primitiveRoot_spec
#print axioms Catalan.ζ_spec
#print axioms Catalan.σ_apply_ζ
#print axioms Catalan.σ_mul
#print axioms Catalan.σ_bijective
#print axioms Catalan.weight_mul
#print axioms Catalan.size_mul_le
#print axioms Catalan.part_identities
#print axioms Catalan.max_part_size
#print axioms Catalan.aug_size_lt_two
#print axioms Catalan.aug_size_two_shape
#print axioms Catalan.finite_size_ball
#print axioms Catalan.upow_add
#print axioms Catalan.upow_pow
#print axioms Catalan.upow_mul
#print axioms Catalan.ipow_principalIdeal_upow
#print axioms Catalan.fractionalIdeal_prime_induction
#print axioms Catalan.prime_over_p_principal
#print axioms Catalan.DensityInput
#print axioms Catalan.A3.primitiveRoot_spec_of_exists
#print axioms Catalan.A3.primitiveRoot_spec
#print axioms Catalan.A3.zeta_residue_pos
#print axioms Catalan.A3.zeta_right_pole

#check @Catalan.lambda_integral_coprime_of_prime_dvd
#check @Catalan.ideal_pow_of_root_factor
#check @Catalan.lambda_ideal_pow
#print axioms Catalan.lambda_integral_coprime_of_prime_dvd
#print axioms Catalan.ideal_pow_of_root_factor
#print axioms Catalan.lambda_ideal_pow

#check @Catalan.hyyro_bound
#check @Catalan.x_sub_ζ_ne_zero
#check @Catalan.qtorsion_trivial
#check @Catalan.mihIdeal
#check @Catalan.mihAug
#check @Catalan.alpha_pow
#check @Catalan.alpha_add
#check @Catalan.prime_generator_away_two
#check @Catalan.exists_descended_gauss_quotient
#check @Catalan.stickelberger_from_away_generators
#print axioms Catalan.hyyro_factor_congruence
#print axioms Catalan.hyyro_two_pow_le_three
#print axioms Catalan.hyyro_small_negative_impossible
#print axioms Catalan.hyyro_bound
#print axioms Catalan.cyclotomic_degree
#print axioms Catalan.embedding_isComplex
#print axioms Catalan.norm_conj_zeta
#print axioms Catalan.x_sub_ζ_ne_zero
#print axioms Catalan.integral_conj_zeta
#print axioms Catalan.qtorsion_trivial
#print axioms Catalan.unit_pow_injective
#print axioms Catalan.map_upow
#print axioms Catalan.mihIdeal
#print axioms Catalan.mihAug
#print axioms Catalan.finite_aug_ball
#print axioms Catalan.alpha_pow
#print axioms Catalan.alpha_zero
#print axioms Catalan.alpha_add
#print axioms Catalan.alphaHom
#print axioms Catalan.alpha_neg
#print axioms Catalan.map_upow_xmζ
#print axioms Catalan.ΘS_zero
#print axioms Catalan.ΘS_p
#print axioms Catalan.ΘS_mod_decomposition
#print axioms Catalan.stickelberger_from_generators
#print axioms Catalan.stickelberger_from_away_generators
#print axioms Catalan.fractionalIdealUnit_pow_injective
#print axioms Catalan.principalIdeal_of_pow_eq
#print axioms Catalan.idealUnit_principal_of_isPrincipalIdealRing
#print axioms Catalan.isPrincipalIdealRing_cyclotomic_two
#print axioms Catalan.prime_generator_away_two
#print axioms Catalan.exists_descended_gauss_power
#print axioms Catalan.exists_descended_gauss_quotient
#print axioms Catalan.ipow_principal_of_descended_power

#check @Catalan.fractional_generator_of_primes_away_two_mul
#check @Catalan.stickelberger_from_primes_away_two_mul
#print axioms Catalan.exists_coprime_integralRepresentative
#print axioms Catalan.principalIdeal_of_class_eq_one
#print axioms Catalan.ipow_principal_of_class_eq
#print axioms Catalan.fractional_generator_of_coprime_integral
#print axioms Catalan.fractional_generator_of_coprime_primes
#print axioms Catalan.fractional_generator_of_primes_away_two_mul
#print axioms Catalan.stickelberger_from_primes_away_two_mul

#check @Catalan.ramifiedPrime_facts
#check @Catalan.difference_ideal
#check @Catalan.theta_identity
#check @Catalan.theta_principal_of_gauss_quotient
#check @Catalan.norm_x_sub_zeta
#check @Catalan.exists_other_prime_divisor_of_absNorm_gt
#check @Catalan.exists_cyclotomicTraceGaussSum_descended_power
#check @Catalan.exists_traceGaussSum_quotient_power
#check @Catalan.Stickelberger.enatValuation_eq_digitSum
#print axioms Catalan.ramifiedPrime_facts
#print axioms Catalan.difference_ideal
#print axioms Catalan.eq10
#print axioms Catalan.integerAut_mul
#print axioms Catalan.fractionalAut_mul
#print axioms Catalan.idealAct_comp
#print axioms Catalan.ipow_mul_single_int
#print axioms Catalan.ipow_exponent_mul
#print axioms Catalan.ipow_sub
#print axioms Catalan.theta_identity
#print axioms Catalan.theta_principal_of_gauss_quotient
#print axioms Catalan.norm_algebraMap_sub_powerBasis_gen
#print axioms Catalan.norm_x_sub_zeta
#print axioms Catalan.absNorm_span_x_sub_zeta
#print axioms Catalan.ideal_eq_prime_pow_of_prime_divisors
#print axioms Catalan.map_ramifiedPrime
#print axioms Catalan.exists_other_prime_divisor_of_absNorm_gt
#print axioms Catalan.order_upow
#print axioms Catalan.traceAddChar_primitive
#print axioms Catalan.gaussSum_aut_eq_mul
#print axioms Catalan.traceGaussSum_aut
#print axioms Catalan.traceGaussSum_ne_zero_any
#print axioms Catalan.exists_traceGaussSum_descended_power
#print axioms Catalan.exists_traceGaussSum_descended_quotient
#print axioms Catalan.traceGaussSum_lift
#print axioms Catalan.exists_traceGaussSum_quotient_power
#print axioms Catalan.exists_cyclotomicTraceGaussSum_descended_power
#print axioms Catalan.Stickelberger.digitSum_div
#print axioms Catalan.Stickelberger.digitSum_complement
#print axioms Catalan.Stickelberger.valuation_le_digitSum
#print axioms Catalan.Stickelberger.valuation_eq_digitSum
#print axioms Catalan.Stickelberger.enatValuation_le_digitSum
#print axioms Catalan.Stickelberger.enatValuation_eq_digitSum

#check @Catalan.cyclotomic_value_large
#check @Catalan.exists_other_prime_divisor
#print axioms Catalan.cyclotomic_pow_growth
#print axioms Catalan.cyclotomic_neg_sum_bound
#print axioms Catalan.cyclotomic_value_large
#print axioms Catalan.exists_other_prime_divisor

#check @Catalan.prime_dvd_residue_card_sub_one
#check @Catalan.exists_primeResidueGaussSum_descended_power
#print axioms Catalan.residueZeta_isPrimitiveRoot
#print axioms Catalan.prime_dvd_residue_card_sub_one
#print axioms Catalan.exists_primeResidueGaussSum_descended_power

#check @Catalan.exists_separating_orders
#check @Catalan.upow_eq_one_iff
#check @Catalan.alpha_ne_one
#check @Catalan.exists_cyclotomic_lift
#check @Catalan.exists_inverse_normalized_primeResidueGaussSum
#check @Catalan.Stickelberger.integralTraceGaussSum_emultiplicity_one
#check @Catalan.Stickelberger.exists_squareZero_residue_section
#print axioms Catalan.primeOrder
#print axioms Catalan.primeOrder_integral
#print axioms Catalan.primeOrder_integral_nonneg
#print axioms Catalan.primeOrder_integral_pos_iff
#print axioms Catalan.primeOrder_integral_eq_zero
#print axioms Catalan.other_prime_not_mem_conjugate
#print axioms Catalan.exists_separating_orders
#print axioms Catalan.upow_eq_one_iff
#print axioms Catalan.alpha_ne_one
#print axioms Catalan.cyclotomic_tower_mul
#print axioms Catalan.exists_cyclotomic_lift
#print axioms Catalan.exists_cyclotomic_lift_of_ne
#print axioms Catalan.exists_cyclotomicTraceGaussSum_quotient_power
#print axioms Catalan.restrictRootsOfUnity_bijective_of_primitive
#print axioms Catalan.residueRootsEquiv
#print axioms Catalan.residuePowerHom
#print axioms Catalan.exists_normalized_powerResidueChar
#print axioms Catalan.exists_normalized_primeResidueChar
#print axioms Catalan.exists_inverse_normalized_primeResidueChar
#print axioms Catalan.prime_ne_residue_characteristic
#print axioms Catalan.exists_primeResidueGaussSum_quotients
#print axioms Catalan.primeResidueGaussSum_data_of_pow_eq_one
#print axioms Catalan.exists_inverse_normalized_primeResidueGaussSum
#print axioms Catalan.Stickelberger.sum_inv_mul_pow
#print axioms Catalan.Stickelberger.sum_inv_mul_trace
#print axioms Catalan.Stickelberger.pow_eq_one_add_of_sub_one_sq_zero
#print axioms Catalan.Stickelberger.integralTraceGaussSum_first_order
#print axioms Catalan.Stickelberger.integralTraceGaussSum_add_uniformizer_mem_sq
#print axioms Catalan.Stickelberger.integralTraceGaussSum_emultiplicity_one
#print axioms Catalan.Stickelberger.exists_squareZero_residue_section
#print axioms Catalan.Stickelberger.residue_section_eq_of_pow_card_eq

#check @Catalan.Stickelberger.mul_digitSum_eq_mul_sum_mod
#print axioms Catalan.Stickelberger.mul_digitSum_eq_mul_sum_mod

-- Inverse Teichmüller family, section bridge, and tower arithmetic.
#check @Catalan.Stickelberger.exists_normalized_residueChar
#check @Catalan.Stickelberger.exists_teichmullerChar
#check @Catalan.Stickelberger.exists_invTeichmullerChar
#check @Catalan.Stickelberger.quotient_factor_sq_ker
#check @Catalan.Stickelberger.exists_residue_section_sq
#check @Catalan.Stickelberger.charP_quotient_of_mem
#check @Catalan.Stickelberger.charP_quotient_pow_of_mem
#check @Catalan.Stickelberger.absNorm_coprime_of_not_dvd
#check @Catalan.Stickelberger.isPrimitiveRoot_quotient_of_not_dvd
#check @Catalan.Stickelberger.invTeichmuller_pow_normalization
#check @Catalan.Stickelberger.integralTraceGaussSum_map
#check @Catalan.Stickelberger.integralTraceGaussSum_emultiplicity_one_of_teichmuller
#check @Catalan.Stickelberger.exists_invTeichmuller_gaussFamily_emultiplicity_one

#print axioms Catalan.Stickelberger.exists_normalized_residueChar
#print axioms Catalan.Stickelberger.exists_teichmullerChar
#print axioms Catalan.Stickelberger.exists_invTeichmullerChar
#print axioms Catalan.Stickelberger.quotient_factor_sq_ker
#print axioms Catalan.Stickelberger.exists_residue_section_sq
#print axioms Catalan.Stickelberger.charP_quotient_of_mem
#print axioms Catalan.Stickelberger.charP_quotient_pow_of_mem
#print axioms Catalan.Stickelberger.absNorm_coprime_of_not_dvd
#print axioms Catalan.Stickelberger.isPrimitiveRoot_quotient_of_not_dvd
#print axioms Catalan.Stickelberger.invTeichmuller_pow_normalization
#print axioms Catalan.Stickelberger.integralTraceGaussSum_map
#print axioms Catalan.Stickelberger.integralTraceGaussSum_emultiplicity_one_of_teichmuller
#print axioms Catalan.Stickelberger.exists_invTeichmuller_gaussFamily_emultiplicity_one

-- Gauss identities: zero index, Frobenius invariance, and complementary pairing.
#check @Catalan.Stickelberger.integralTraceGaussSum_trace_frobenius
#check @Catalan.Stickelberger.integralTraceGaussSum_pow_bijective
#check @Catalan.Stickelberger.integralTraceGaussSum_one
#check @Catalan.Stickelberger.integralTraceGaussSum_pow_char
#check @Catalan.Stickelberger.integralTraceGaussSum_mul_inv

#print axioms Catalan.Stickelberger.integralTraceGaussSum_trace_frobenius
#print axioms Catalan.Stickelberger.integralTraceGaussSum_pow_bijective
#print axioms Catalan.Stickelberger.integralTraceGaussSum_one
#print axioms Catalan.Stickelberger.integralTraceGaussSum_pow_char
#print axioms Catalan.Stickelberger.integralTraceGaussSum_mul_inv

-- Hensel lifting of the full root-of-unity group; tower statement.
#check @Catalan.Stickelberger.exists_isPrimitiveRoot_card_sub_one
#check @Catalan.Stickelberger.exists_primitiveRoot_of_henselian
#check @Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_henselian

#print axioms Catalan.Stickelberger.exists_isPrimitiveRoot_card_sub_one
#print axioms Catalan.Stickelberger.exists_primitiveRoot_of_henselian
#print axioms Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_henselian
#check @Catalan.Stickelberger.natCast_mem_sq_of_primitiveRoot
#check @Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_primitiveRoot
#print axioms Catalan.Stickelberger.natCast_mem_sq_of_primitiveRoot
#print axioms Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_primitiveRoot
#check @Catalan.Stickelberger.sub_one_mem_of_pow_eq_one
#check @Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_uniformizer
#print axioms Catalan.Stickelberger.sub_one_mem_of_pow_eq_one
#print axioms Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_uniformizer

-- Concrete Witt vector instance of the Hensel-lifting result.
#check @Catalan.Stickelberger.wittVector_span_eq_maximalIdeal
#check @Catalan.Stickelberger.wittVector_henselianLocalRing
#check @Catalan.Stickelberger.wittVector_isDedekindDomain
#check @Catalan.Stickelberger.wittVector_residue_hom
#check @Catalan.Stickelberger.wittVector_constantCoeff_eq_ghostComponent_zero
#check @Catalan.Stickelberger.Witt.exists_primitiveRoot_wittVector

#print axioms Catalan.Stickelberger.wittVector_span_eq_maximalIdeal
#print axioms Catalan.Stickelberger.wittVector_henselianLocalRing
#print axioms Catalan.Stickelberger.wittVector_isDedekindDomain
#print axioms Catalan.Stickelberger.wittVector_residue_hom
#print axioms Catalan.Stickelberger.wittVector_constantCoeff_eq_ghostComponent_zero
#print axioms Catalan.Stickelberger.Witt.exists_primitiveRoot_wittVector

-- General-ideal Gauss valuation and cyclotomic uniformizer.
#check @Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_uniformizer_ideal
#check @Catalan.Stickelberger.not_dvd_of_eq_pow_sub_one
#check @Catalan.Stickelberger.natCast_mem_of_liesOver
#check @Catalan.Stickelberger.finiteMultiplicity_span_natCast
#check @Catalan.Stickelberger.zeta_sub_one_mem_not_mem_sq

#print axioms Catalan.Stickelberger.exists_gaussFamily_emultiplicity_one_of_uniformizer_ideal
#print axioms Catalan.Stickelberger.not_dvd_of_eq_pow_sub_one
#print axioms Catalan.Stickelberger.natCast_mem_of_liesOver
#print axioms Catalan.Stickelberger.finiteMultiplicity_span_natCast
#print axioms Catalan.Stickelberger.zeta_sub_one_mem_not_mem_sq
#check @Catalan.Stickelberger.orderOf_natCast_pow_sub_one
#check @Catalan.Stickelberger.card_residue_of_cyclotomic
#check @Catalan.Stickelberger.cyclotomic_route_inputs
#check @Catalan.Stickelberger.exists_cyclotomic_gaussFamily_emultiplicity_one

#print axioms Catalan.Stickelberger.orderOf_natCast_pow_sub_one
#print axioms Catalan.Stickelberger.card_residue_of_cyclotomic
#print axioms Catalan.Stickelberger.cyclotomic_route_inputs
#print axioms Catalan.Stickelberger.exists_cyclotomic_gaussFamily_emultiplicity_one

/-! ### Gauss-sum identities, valuations, and ideal factorization -/

#check @Catalan.Stickelberger.integralTraceGaussSum_mul_jacobiSum
#check @Catalan.Stickelberger.gaussFamily_dvd_mul
#check @Catalan.Stickelberger.gaussFamily_zero
#check @Catalan.Stickelberger.gaussFamily_natCast_mul
#check @Catalan.Stickelberger.orderOf_eq_card_sub_one_of_inv_reduction
#check @Catalan.Stickelberger.gaussFamily_mul_complement
#check @Catalan.Stickelberger.multiplicity_span_natCast_eq
#check @Catalan.Stickelberger.emultiplicity_span_natCast_eq
#check @Catalan.Stickelberger.gaussFamily_emultiplicity_eq_digitSum
#check @Catalan.Stickelberger.exists_cyclotomic_gaussFamily_emultiplicity_eq_digitSum
#check @Catalan.Stickelberger.ideal_eq_of_emultiplicity_eq
#check @Catalan.Stickelberger.emultiplicity_span_eq_zero_of_notMem
#check @Catalan.Stickelberger.emultiplicity_prod_pow
#check @Catalan.Stickelberger.emultiplicity_eq_zero_of_ne
#check @Catalan.Stickelberger.span_eq_prod_pow_of_emultiplicity
#check @Catalan.ipow_pθ_eq_prod
#check @Catalan.idealUnit_eq_prod_pow
#check @Catalan.idealUnit_span_eq_principalIdeal
#check @Catalan.conjIdeal_isPrime
#check @Catalan.conjIdeal_ne_bot
#check @Catalan.ipow_pθ_eq_principalIdeal_of_emultiplicity

#print axioms Catalan.Stickelberger.integralTraceGaussSum_mul_jacobiSum
#print axioms Catalan.Stickelberger.gaussFamily_dvd_mul
#print axioms Catalan.Stickelberger.gaussFamily_zero
#print axioms Catalan.Stickelberger.gaussFamily_natCast_mul
#print axioms Catalan.Stickelberger.orderOf_eq_card_sub_one_of_inv_reduction
#print axioms Catalan.Stickelberger.gaussFamily_mul_complement
#print axioms Catalan.Stickelberger.multiplicity_span_natCast_eq
#print axioms Catalan.Stickelberger.emultiplicity_span_natCast_eq
#print axioms Catalan.Stickelberger.gaussFamily_emultiplicity_eq_digitSum
#print axioms Catalan.Stickelberger.exists_cyclotomic_gaussFamily_emultiplicity_eq_digitSum
#print axioms Catalan.Stickelberger.ideal_eq_of_emultiplicity_eq
#print axioms Catalan.Stickelberger.emultiplicity_span_eq_zero_of_notMem
#print axioms Catalan.Stickelberger.emultiplicity_prod_pow
#print axioms Catalan.Stickelberger.emultiplicity_eq_zero_of_ne
#print axioms Catalan.Stickelberger.span_eq_prod_pow_of_emultiplicity
#print axioms Catalan.ipow_pθ_eq_prod
#print axioms Catalan.idealUnit_eq_prod_pow
#print axioms Catalan.idealUnit_span_eq_principalIdeal
#print axioms Catalan.conjIdeal_isPrime
#print axioms Catalan.conjIdeal_ne_bot
#print axioms Catalan.ipow_pθ_eq_principalIdeal_of_emultiplicity

/-! ### Fiberwise ideal factorization and cyclotomic valuation transfer -/

#check @Catalan.Stickelberger.span_eq_prod_pow_of_emultiplicity_fiber
#check @Catalan.ipow_pθ_eq_principalIdeal_of_emultiplicity_fiber
#check @Catalan.Stickelberger.isCyclotomicExtension_tower
#check @Catalan.Stickelberger.emultiplicity_map_eq_ramificationIdx_mul
#check @Catalan.Stickelberger.exists_integerAut_map_eq_of_natCast_mem
#check @Catalan.Stickelberger.emultiplicity_eq_zero_of_not_conj

#print axioms Catalan.Stickelberger.span_eq_prod_pow_of_emultiplicity_fiber
#print axioms Catalan.ipow_pθ_eq_principalIdeal_of_emultiplicity_fiber
#print axioms Catalan.Stickelberger.isCyclotomicExtension_tower
#print axioms Catalan.Stickelberger.emultiplicity_map_eq_ramificationIdx_mul
#print axioms Catalan.Stickelberger.exists_integerAut_map_eq_of_natCast_mem
#print axioms Catalan.Stickelberger.emultiplicity_eq_zero_of_not_conj

/-! ### Gauss-sum Galois action and ramification indices -/

#check @Catalan.Stickelberger.integralTraceAddChar_pow
#check @Catalan.Stickelberger.integralTraceGaussSum_galois_twist
#check @Catalan.Stickelberger.integralTraceGaussSum_pow_fixed
#check @Catalan.Stickelberger.ramificationIdx_tower_eq

#print axioms Catalan.Stickelberger.integralTraceAddChar_pow
#print axioms Catalan.Stickelberger.integralTraceGaussSum_galois_twist
#print axioms Catalan.Stickelberger.integralTraceGaussSum_pow_fixed
#print axioms Catalan.Stickelberger.ramificationIdx_tower_eq

/-! ### Galois descent for Gauss-sum powers -/

#check @Catalan.Stickelberger.exists_algebraMap_eq_of_forall_fixed
#check @Catalan.Stickelberger.isIntegral_of_algebraMap_isIntegral
#check @Catalan.Stickelberger.exists_ringOfIntegers_of_forall_fixed
#check @Catalan.Stickelberger.exists_algebraMap_eq_of_pow_eq_one
#check @Catalan.Stickelberger.exists_pow_eq_of_isPrimitiveRoot
#check @Catalan.Stickelberger.gaussSum_pow_fixed_of_algEquiv
#check @Catalan.Stickelberger.exists_ringOfIntegers_gaussSum_pow
#check @Catalan.Stickelberger.exists_ringOfIntegers_of_pow_eq_one

#print axioms Catalan.Stickelberger.exists_algebraMap_eq_of_forall_fixed
#print axioms Catalan.Stickelberger.isIntegral_of_algebraMap_isIntegral
#print axioms Catalan.Stickelberger.exists_ringOfIntegers_of_forall_fixed
#print axioms Catalan.Stickelberger.exists_algebraMap_eq_of_pow_eq_one
#print axioms Catalan.Stickelberger.exists_pow_eq_of_isPrimitiveRoot
#print axioms Catalan.Stickelberger.gaussSum_pow_fixed_of_algEquiv
#print axioms Catalan.Stickelberger.exists_ringOfIntegers_gaussSum_pow
#print axioms Catalan.Stickelberger.exists_ringOfIntegers_of_pow_eq_one

/-! ### Cyclotomic subfields and multiplicity transport -/

#check @Catalan.Stickelberger.isCyclotomicExtension_intermediateField
#check @Catalan.Stickelberger.integralTraceGaussSum_ringHom_of_fixed_root
#check @Catalan.Stickelberger.emultiplicity_mulEquiv
#check @Catalan.Stickelberger.emultiplicity_ideal_map
#check @Catalan.Stickelberger.emultiplicity_ideal_map_span

#print axioms Catalan.Stickelberger.isCyclotomicExtension_intermediateField
#print axioms Catalan.Stickelberger.integralTraceGaussSum_ringHom_of_fixed_root
#print axioms Catalan.Stickelberger.emultiplicity_mulEquiv
#print axioms Catalan.Stickelberger.emultiplicity_ideal_map
#print axioms Catalan.Stickelberger.emultiplicity_ideal_map_span

/-! ### Orbit-sum valuation formula -/

#check @Catalan.Stickelberger.integralTraceGaussSum_pow_mul_inv_pow
#check @Catalan.Stickelberger.ringHom_apply_eq_pow_of_pow_eq_one
#check @Catalan.Stickelberger.ringHomComp_eq_pow_of_pow_eq_one
#check @Catalan.Stickelberger.enat_eq_natCast_of_natCast_mul_eq
#check @Catalan.Stickelberger.emultiplicity_eq_orbit_sum

#print axioms Catalan.Stickelberger.integralTraceGaussSum_pow_mul_inv_pow
#print axioms Catalan.Stickelberger.ringHom_apply_eq_pow_of_pow_eq_one
#print axioms Catalan.Stickelberger.ringHomComp_eq_pow_of_pow_eq_one
#print axioms Catalan.Stickelberger.enat_eq_natCast_of_natCast_mul_eq
#print axioms Catalan.Stickelberger.emultiplicity_eq_orbit_sum

/-! ### Complete Stickelberger assembly (2026-09-18) -/

#check @Catalan.Stickelberger.eq_of_map_eq_of_pow_eq_one
#check @Catalan.Stickelberger.exists_baseChar_eq_invTeichmuller_pow
#check @Catalan.exists_cyclotomic_tower_lift
#check @Catalan.conjIdeal_fiber_sum_eq_orbit_sum
#check @Catalan.Stickelberger.exists_descended_gaussSum_mul_eq
#check @Catalan.Stickelberger.descended_gaussSum_emultiplicity_eq_zero_of_not_conj
#check @Catalan.Stickelberger.emultiplicity_conjIdeal_eq_orbit_sum_of_gaussFamily
#check @Catalan.Stickelberger.exists_integralGaussSum_quotient_power
#check @Catalan.Stickelberger.isCyclotomicExtension_base_tower_of_dvd
#check @Catalan.Stickelberger.exists_prime_gauss_witnesses
#check @Catalan.prime_stickelberger_generator
#check @Catalan.stickelberger_annihilates

#print axioms Catalan.Stickelberger.eq_of_map_eq_of_pow_eq_one
#print axioms Catalan.Stickelberger.exists_baseChar_eq_invTeichmuller_pow
#print axioms Catalan.exists_cyclotomic_tower_lift
#print axioms Catalan.conjIdeal_fiber_sum_eq_orbit_sum
#print axioms Catalan.Stickelberger.exists_descended_gaussSum_mul_eq
#print axioms Catalan.Stickelberger.descended_gaussSum_emultiplicity_eq_zero_of_not_conj
#print axioms Catalan.Stickelberger.emultiplicity_conjIdeal_eq_orbit_sum_of_gaussFamily
#print axioms Catalan.Stickelberger.exists_integralGaussSum_quotient_power
#print axioms Catalan.Stickelberger.isCyclotomicExtension_base_tower_of_dvd
#print axioms Catalan.Stickelberger.exists_prime_gauss_witnesses
#print axioms Catalan.prime_stickelberger_generator
#print axioms Catalan.stickelberger_annihilates

/-! ### Linear logarithms, phase and prime-exponent reduction (2026-09-18) -/

#check @Catalan.log_one_sub_bound
#check @Catalan.norm_log_exp_le
#check @Catalan.linearLog
#check @Catalan.linearLog_zero
#check @Catalan.linearLog_add
#check @Catalan.linearLog_neg
#check @Catalan.linearLog_sub
#check @Catalan.norm_conj_zeta_div_int
#check @Catalan.conj_zeta_div_int_norm_lt_one
#check @Catalan.exp_linearLog
#check @Catalan.linearLog_bound
#check @Catalan.prop45_principal_log
#check @Catalan.augAlpha
#check @Catalan.alphaC
#check @Catalan.alphaC_zero
#check @Catalan.alphaC_add
#check @Catalan.alphaC_pow
#check @Catalan.phaseValue
#check @Catalan.exp_nat_mul_manual
#check @Catalan.phaseValue_pow
#check @Catalan.xi
#check @Catalan.xi_val
#check @Catalan.xi_zero
#check @Catalan.xi_add
#check @Catalan.xiHom
#check @Catalan.xi_neg
#check @Catalan.xi_sub
#check @Catalan.rootsOfUnity_eq_of_log_div_norm_lt
#check @Catalan.xi_small_log
#check @Catalan.xi_unique
#check @Catalan.xi_local_add
#check @Catalan.expm1_seven_fifths
#check @Catalan.even_degree_power_bound
#check @Catalan.small_ratio_le
#check @Catalan.five_pow_hundred
#check @Catalan.reduce_to_primes

#print axioms Catalan.log_one_sub_bound
#print axioms Catalan.norm_log_exp_le
#print axioms Catalan.linearLog
#print axioms Catalan.linearLog_zero
#print axioms Catalan.linearLog_add
#print axioms Catalan.linearLog_neg
#print axioms Catalan.linearLog_sub
#print axioms Catalan.norm_conj_zeta_div_int
#print axioms Catalan.conj_zeta_div_int_norm_lt_one
#print axioms Catalan.exp_linearLog
#print axioms Catalan.linearLog_bound
#print axioms Catalan.prop45_principal_log
#print axioms Catalan.augAlpha
#print axioms Catalan.alphaC
#print axioms Catalan.alphaC_zero
#print axioms Catalan.alphaC_add
#print axioms Catalan.alphaC_pow
#print axioms Catalan.phaseValue
#print axioms Catalan.exp_nat_mul_manual
#print axioms Catalan.phaseValue_pow
#print axioms Catalan.xi
#print axioms Catalan.xi_val
#print axioms Catalan.xi_zero
#print axioms Catalan.xi_add
#print axioms Catalan.xiHom
#print axioms Catalan.xi_neg
#print axioms Catalan.xi_sub
#print axioms Catalan.rootsOfUnity_eq_of_log_div_norm_lt
#print axioms Catalan.xi_small_log
#print axioms Catalan.xi_unique
#print axioms Catalan.xi_local_add
#print axioms Catalan.expm1_seven_fifths
#print axioms Catalan.even_degree_power_bound
#print axioms Catalan.small_ratio_le
#print axioms Catalan.five_pow_hundred
#print axioms Catalan.reduce_to_primes

/-! ### Numerical thresholds and phase separation (2026-09-18) -/

#check @Catalan.mihRadius
#check @Catalan.mihThreshold
#check @Catalan.h8_consequences
#check @Catalan.prop49_real_contradiction
#check @Catalan.root_phase_separation
#check @Catalan.prop42_real_contradiction
#check @Catalan.cor43_power_domination
#check @Catalan.pPrime
#check @Catalan.pPrime_pos
#check @Catalan.radius_ge_one
#check @Catalan.h9_implies_h8

#print axioms Catalan.mihRadius
#print axioms Catalan.mihThreshold
#print axioms Catalan.h8_consequences
#print axioms Catalan.prop49_real_contradiction
#print axioms Catalan.root_phase_separation
#print axioms Catalan.prop42_real_contradiction
#print axioms Catalan.cor43_power_domination
#print axioms Catalan.pPrime
#print axioms Catalan.pPrime_pos
#print axioms Catalan.radius_ge_one
#print axioms Catalan.h9_implies_h8

/-! ### Finite-place bounds for the radius-two argument (2026-09-18) -/

#check @Catalan.finitePlace_integral_le_one
#check @Catalan.finitePlace_le_of_dvd
#check @Catalan.finitePlace_eq_of_span_eq
#check @Catalan.finitePlace_root_distance_pow
#check @Catalan.finitePlace_root_difference_pow
#check @Catalan.prop42_power_difference
#check @Catalan.finite_power_near_one
#check @Catalan.finite_log_inverse_sum_le_of_lower
#check @Catalan.prop42_finite_lower
#check @Catalan.finite_inverse_sum_bound_for_cyclotomic
#check @Catalan.augAlpha_sub_one_ne_zero_of_size_two
#check @Catalan.prop42_nonarch_ge_one
#check @Catalan.prop42_finite_inverse_sum

#print axioms Catalan.finitePlace_integral_le_one
#print axioms Catalan.finitePlace_le_of_dvd
#print axioms Catalan.finitePlace_eq_of_span_eq
#print axioms Catalan.finitePlace_root_distance_pow
#print axioms Catalan.finitePlace_root_difference_pow
#print axioms Catalan.prop42_power_difference
#print axioms Catalan.finite_power_near_one
#print axioms Catalan.finite_log_inverse_sum_le_of_lower
#print axioms Catalan.prop42_finite_lower
#print axioms Catalan.finite_inverse_sum_bound_for_cyclotomic
#print axioms Catalan.augAlpha_sub_one_ne_zero_of_size_two
#print axioms Catalan.prop42_nonarch_ge_one
#print axioms Catalan.prop42_finite_inverse_sum

/-! ### Double Wieferich criterion -/

#check @Catalan.A1e.upow_base_div
#check @Catalan.A1e.actUnit_one
#check @Catalan.A1e.upow_actUnit_commute
#check @Catalan.A1e.upow_minusPart_eq
#check @Catalan.A1e.upow_minusPart_base
#check @Catalan.A1e.upow_pow_eq_one
#check @Catalan.A1e.iota_apply_zeta
#check @Catalan.A1e.minus_root_quotient
#check @Catalan.A1e.solution_primes_ne
#check @Catalan.A1e.lift_minus_one
#check @Catalan.A1e.wieferich_of_factorization
#check @Catalan.A1e.inverseConjugates_basis
#check @Catalan.A1e.inverseConjugates_dvd_coeff
#check @Catalan.A1e.testTheta_coefficient
#check @Catalan.A1e.iota_on_embeddings
#check @Catalan.A1e.torsion_order_bound
#check @Catalan.A1e.symmetry
#check @Catalan.A1e.one_add_pow_remainder
#check @Catalan.A1e.one_add_mul_pow_dvd
#check @Catalan.A1e.one_sub_pow_remainder
#check @Catalan.A1e.prod_one_sub_remainder
#check @Catalan.A1e.primary_of_frobenius_lift
#check @Catalan.A1e.integral_qth_root
#check @Catalan.A1e.kronecker_unit_pair
#check @Catalan.A1e.qth_root_of_bezout
#check @Catalan.A1e.qth_root_of_coprime
#check @Catalan.A1e.minusPart
#check @Catalan.A1e.testTheta
#check @Catalan.A1e.lambdaUnit
#check @Catalan.A1e.zetaInteger
#check @Catalan.A1e.inverseConjugate
#check @Catalan.A1e.liftCoefficient
#check @Catalan.A1e.liftProduct
#check @Catalan.A1e.liftLinear
#check @Catalan.A1e.theta_two_mem
#check @Catalan.A1e.super_cassels_in_field
#check @Catalan.A1e.super_cassels
#check @Catalan.A1e.one_sided_wieferich
#check @Catalan.double_wieferich
#check @Catalan.A1e.cyclotomic_frobenius_lift
#check @Catalan.A1e.exists_unit_mul_of_principalIdeal_eq
#check @Catalan.A1e.lambda_stick_generator
#check @Catalan.A1e.liftProduct_qth
#check @Catalan.A1e.kummer_unit_quotient
#check @Catalan.A1e.minus_stick_qth
#check @Catalan.A1e.liftProduct_expansion
#check @Catalan.A1e.liftProduct_mod_q
#check @Catalan.A1e.liftProduct_obstruction
#check @Catalan.A1e.liftCoefficient_one
#check @Catalan.A1e.square_dvd_x_from_obstruction

#print axioms Catalan.A1e.upow_base_div
#print axioms Catalan.A1e.actUnit_one
#print axioms Catalan.A1e.upow_actUnit_commute
#print axioms Catalan.A1e.upow_minusPart_eq
#print axioms Catalan.A1e.upow_minusPart_base
#print axioms Catalan.A1e.upow_pow_eq_one
#print axioms Catalan.A1e.iota_apply_zeta
#print axioms Catalan.A1e.minus_root_quotient
#print axioms Catalan.A1e.solution_primes_ne
#print axioms Catalan.A1e.lift_minus_one
#print axioms Catalan.A1e.wieferich_of_factorization
#print axioms Catalan.A1e.inverseConjugates_basis
#print axioms Catalan.A1e.inverseConjugates_dvd_coeff
#print axioms Catalan.A1e.testTheta_coefficient
#print axioms Catalan.A1e.iota_on_embeddings
#print axioms Catalan.A1e.torsion_order_bound
#print axioms Catalan.A1e.symmetry
#print axioms Catalan.A1e.one_add_pow_remainder
#print axioms Catalan.A1e.one_add_mul_pow_dvd
#print axioms Catalan.A1e.one_sub_pow_remainder
#print axioms Catalan.A1e.prod_one_sub_remainder
#print axioms Catalan.A1e.primary_of_frobenius_lift
#print axioms Catalan.A1e.integral_qth_root
#print axioms Catalan.A1e.kronecker_unit_pair
#print axioms Catalan.A1e.qth_root_of_bezout
#print axioms Catalan.A1e.qth_root_of_coprime
#print axioms Catalan.A1e.minusPart
#print axioms Catalan.A1e.testTheta
#print axioms Catalan.A1e.lambdaUnit
#print axioms Catalan.A1e.zetaInteger
#print axioms Catalan.A1e.inverseConjugate
#print axioms Catalan.A1e.liftCoefficient
#print axioms Catalan.A1e.liftProduct
#print axioms Catalan.A1e.liftLinear
#print axioms Catalan.A1e.theta_two_mem
#print axioms Catalan.A1e.super_cassels_in_field
#print axioms Catalan.A1e.super_cassels
#print axioms Catalan.A1e.one_sided_wieferich
#print axioms Catalan.double_wieferich
#print axioms Catalan.A1e.cyclotomic_frobenius_lift
#print axioms Catalan.A1e.exists_unit_mul_of_principalIdeal_eq
#print axioms Catalan.A1e.lambda_stick_generator
#print axioms Catalan.A1e.liftProduct_qth
#print axioms Catalan.A1e.kummer_unit_quotient
#print axioms Catalan.A1e.minus_stick_qth
#print axioms Catalan.A1e.liftProduct_expansion
#print axioms Catalan.A1e.liftProduct_mod_q
#print axioms Catalan.A1e.liftProduct_obstruction
#print axioms Catalan.A1e.liftCoefficient_one
#print axioms Catalan.A1e.square_dvd_x_from_obstruction

/-! ### Lebesgue classical case (2026-09-18) -/

#check @Catalan.Lebesgue.gaussian_imag_pow_even
#check @Catalan.Lebesgue.gaussian_imag_pow_odd_re
#check @Catalan.Lebesgue.gaussian_imag_pow_re
#check @Catalan.Lebesgue.gaussian_re_binomial
#check @Catalan.Lebesgue.gaussian_re_dvd_re_pow_odd
#check @Catalan.Lebesgue.gaussian_re_pow_mod_four_of_even_im
#check @Catalan.Lebesgue.lebesgue_solution_parity
#check @Catalan.Lebesgue.gaussian_conjugate_coprime_of_even
#check @Catalan.Lebesgue.gaussian_unit_pow_four
#check @Catalan.Lebesgue.gaussian_unit_pow_surjective
#check @Catalan.Lebesgue.gaussian_root_normalization
#check @Catalan.Lebesgue.lebesgue_even_term_order
#check @Catalan.Lebesgue.int_sum_ne_zero_of_unique_min_order
#check @Catalan.Lebesgue.gaussian_even_imag_real_ne_one
#check @Catalan.Lebesgue.exists_gaussian_root_of_solution
#check @Catalan.lebesgue_q_two

#print axioms Catalan.Lebesgue.gaussian_imag_pow_even
#print axioms Catalan.Lebesgue.gaussian_imag_pow_odd_re
#print axioms Catalan.Lebesgue.gaussian_imag_pow_re
#print axioms Catalan.Lebesgue.gaussian_re_binomial
#print axioms Catalan.Lebesgue.gaussian_re_dvd_re_pow_odd
#print axioms Catalan.Lebesgue.gaussian_re_pow_mod_four_of_even_im
#print axioms Catalan.Lebesgue.lebesgue_solution_parity
#print axioms Catalan.Lebesgue.gaussian_conjugate_coprime_of_even
#print axioms Catalan.Lebesgue.gaussian_unit_pow_four
#print axioms Catalan.Lebesgue.gaussian_unit_pow_surjective
#print axioms Catalan.Lebesgue.gaussian_root_normalization
#print axioms Catalan.Lebesgue.lebesgue_even_term_order
#print axioms Catalan.Lebesgue.int_sum_ne_zero_of_unique_min_order
#print axioms Catalan.Lebesgue.gaussian_even_imag_real_ne_one
#print axioms Catalan.Lebesgue.exists_gaussian_root_of_solution
#print axioms Catalan.lebesgue_q_two

/-! ### Euler square–cube case (2026-09-18) -/

#check @Catalan.Euler.sq_of_nonneg_coprime_product
#check @Catalan.Euler.sq_sub_sq_eq_one
#check @Catalan.Euler.euler_factors
#check @Catalan.Euler.euler_y_pos
#check @Catalan.Euler.sq_eq_quadratic
#check @Catalan.Euler.euler_three_square_factors
#check @Catalan.Euler.int_sq_ne_two
#check @Catalan.Euler.euler_three_dvd_y_add_one
#check @Catalan.Euler.pell_complete_int
#check @Catalan.Euler.euler_solution_pell
#check @Catalan.Euler.pellX
#check @Catalan.Euler.pellY
#check @Catalan.Euler.negative_pell_two_param
#check @Catalan.Euler.quartic_pell_three
#check @Catalan.Euler.quartic_pell_two
#check @Catalan.Euler.pell_identity
#check @Catalan.Euler.pell_complete
#check @Catalan.Euler.pell_x_double
#check @Catalan.Euler.pell_y_double
#check @Catalan.Euler.pell_x_odd
#check @Catalan.Euler.pell_y_odd
#check @Catalan.Euler.pell_x_odd_iff
#check @Catalan.Euler.pell_y_odd_iff
#check @Catalan.Euler.pell_x_eq_one_iff
#check @Catalan.Euler.pell_y_pos
#check @Catalan.Euler.pell_xy_coprime
#check @Catalan.Euler.pell_y_plus_one_twice_square_of_x_square_trivial
#check @Catalan.Euler.pell_x_square_index_zero
#check @Catalan.Euler.pell_y_plus_one_twice_square
#check @Catalan.euler_square_cube

#print axioms Catalan.Euler.sq_of_nonneg_coprime_product
#print axioms Catalan.Euler.sq_sub_sq_eq_one
#print axioms Catalan.Euler.euler_factors
#print axioms Catalan.Euler.euler_y_pos
#print axioms Catalan.Euler.sq_eq_quadratic
#print axioms Catalan.Euler.euler_three_square_factors
#print axioms Catalan.Euler.int_sq_ne_two
#print axioms Catalan.Euler.euler_three_dvd_y_add_one
#print axioms Catalan.Euler.pell_complete_int
#print axioms Catalan.Euler.euler_solution_pell
#print axioms Catalan.Euler.pellX
#print axioms Catalan.Euler.pellY
#print axioms Catalan.Euler.negative_pell_two_param
#print axioms Catalan.Euler.quartic_pell_three
#print axioms Catalan.Euler.quartic_pell_two
#print axioms Catalan.Euler.pell_identity
#print axioms Catalan.Euler.pell_complete
#print axioms Catalan.Euler.pell_x_double
#print axioms Catalan.Euler.pell_y_double
#print axioms Catalan.Euler.pell_x_odd
#print axioms Catalan.Euler.pell_y_odd
#print axioms Catalan.Euler.pell_x_odd_iff
#print axioms Catalan.Euler.pell_y_odd_iff
#print axioms Catalan.Euler.pell_x_eq_one_iff
#print axioms Catalan.Euler.pell_y_pos
#print axioms Catalan.Euler.pell_xy_coprime
#print axioms Catalan.Euler.pell_y_plus_one_twice_square_of_x_square_trivial
#print axioms Catalan.Euler.pell_x_square_index_zero
#print axioms Catalan.Euler.pell_y_plus_one_twice_square
#print axioms Catalan.euler_square_cube

/-! ### Ko–Chao square-base case (2026-09-18) -/

#check @Catalan.KoChao.square_base_oriented_factors
#check @Catalan.KoChao.gcd_sub_homogeneous_sum
#check @Catalan.KoChao.integer_square_gap
#check @Catalan.KoChao.oriented_factor_abs_lt
#check @Catalan.KoChao.oriented_difference_not_square
#check @Catalan.KoChao.oriented_square_identity
#check @Catalan.KoChao.square_base_positive_even
#check @Catalan.KoChao.square_base_q_dvd_x
#check @Catalan.KoChao.prime_dvd_or_square_of_pow_sub_pow_eq_sq
#check @Catalan.KoChao.oriented_second_congruence
#check @Catalan.KoChao.prime_eq_three_of_two_congruences
#check @Catalan.koChao_p_two

#print axioms Catalan.KoChao.square_base_oriented_factors
#print axioms Catalan.KoChao.gcd_sub_homogeneous_sum
#print axioms Catalan.KoChao.integer_square_gap
#print axioms Catalan.KoChao.oriented_factor_abs_lt
#print axioms Catalan.KoChao.oriented_difference_not_square
#print axioms Catalan.KoChao.oriented_square_identity
#print axioms Catalan.KoChao.square_base_positive_even
#print axioms Catalan.KoChao.square_base_q_dvd_x
#print axioms Catalan.KoChao.prime_dvd_or_square_of_pow_sub_pow_eq_sq
#print axioms Catalan.KoChao.oriented_second_congruence
#print axioms Catalan.KoChao.prime_eq_three_of_two_congruences
#print axioms Catalan.koChao_p_two

/-! ### Integer lattice-ball count (2026-09-18) -/

#check @Catalan.S
#check @Catalan.LatticeCount.countPolynomial
#check @Catalan.LatticeCount.finite_lattice_ball
#check @Catalan.LatticeCount.S_zero_dim
#check @Catalan.LatticeCount.countPolynomial_two
#check @Catalan.LatticeCount.countPolynomial_three
#check @Catalan.LatticeCount.countPolynomial_gt_two
#check @Catalan.LatticeCount.countPolynomial_gt_three
#check @Catalan.LatticeCount.S_succ_dim
#check @Catalan.LatticeCount.countPolynomial_zero_dim
#check @Catalan.LatticeCount.countPolynomial_succ_dim
#check @Catalan.LatticeCount.countPolynomial_gt
#check @Catalan.LatticeCount.countPolynomial_gt'
#check @Catalan.S_formula
#check @Catalan.S_gt
#check @Catalan.S_gt'
#check @Catalan.S_gt_three
#check @Catalan.S_gt_two

#print axioms Catalan.S
#print axioms Catalan.LatticeCount.countPolynomial
#print axioms Catalan.LatticeCount.finite_lattice_ball
#print axioms Catalan.LatticeCount.S_zero_dim
#print axioms Catalan.LatticeCount.countPolynomial_two
#print axioms Catalan.LatticeCount.countPolynomial_three
#print axioms Catalan.LatticeCount.countPolynomial_gt_two
#print axioms Catalan.LatticeCount.countPolynomial_gt_three
#print axioms Catalan.LatticeCount.S_succ_dim
#print axioms Catalan.LatticeCount.countPolynomial_zero_dim
#print axioms Catalan.LatticeCount.countPolynomial_succ_dim
#print axioms Catalan.LatticeCount.countPolynomial_gt
#print axioms Catalan.LatticeCount.countPolynomial_gt'
#print axioms Catalan.S_formula
#print axioms Catalan.S_gt
#print axioms Catalan.S_gt'
#print axioms Catalan.S_gt_three
#print axioms Catalan.S_gt_two

/-! ### Case 2 congruence arithmetic (2026-09-18) -/

#check @Catalan.small_five_wieferich_candidates
#check @Catalan.five_no_double_wieferich_small
#check @Catalan.mignotte_lower_bound
#check @Catalan.CaseTwo.not_modEq_one_of_large_weak_bound
#check @Catalan.CaseTwo.not_modEq_one_of_seven_weak_bound
#check @Catalan.CaseTwo.not_modEq_one_of_five_weak_bound
#check @Catalan.wieferich_lift_congruence

#print axioms Catalan.small_five_wieferich_candidates
#print axioms Catalan.five_no_double_wieferich_small
#print axioms Catalan.mignotte_lower_bound
#print axioms Catalan.CaseTwo.not_modEq_one_of_large_weak_bound
#print axioms Catalan.CaseTwo.not_modEq_one_of_seven_weak_bound
#print axioms Catalan.CaseTwo.not_modEq_one_of_five_weak_bound
#print axioms Catalan.wieferich_lift_congruence

/-! ### Minus generators and low conductors (2026-09-18) -/

#check @Catalan.θminus
#check @Catalan.ΘS_coeff
#check @Catalan.θminus_coeff
#check @Catalan.θminus_eq_minusPart
#check @Catalan.θminus_weight
#check @Catalan.MinusGenerators.floor_step_zero_or_one
#check @Catalan.MinusGenerators.complementary_floor_sum
#check @Catalan.θminus_coeff_eq_neg_one_or_one
#check @Catalan.θminus_size_eq
#check @Catalan.θminus_size_le
#check @Catalan.ΘS_mul_single
#check @Catalan.pθ_mul_single
#check @Catalan.stickSpan_mul_single
#check @Catalan.θminus_mem
#check @Catalan.θminus_small_three
#check @Catalan.θminus_small_five
#check @Catalan.θminus_small_seven
#check @Catalan.minus_element_ne_zero
#check @Catalan.minus_element_size
#check @Catalan.q_smul_mem_mihIdeal
#check @Catalan.θminus_mem_mihIdeal
#check @Catalan.small_minus_mem_mihAug
#check @Catalan.small_conductor_aug_witness

#print axioms Catalan.θminus
#print axioms Catalan.ΘS_coeff
#print axioms Catalan.θminus_coeff
#print axioms Catalan.θminus_eq_minusPart
#print axioms Catalan.θminus_weight
#print axioms Catalan.MinusGenerators.floor_step_zero_or_one
#print axioms Catalan.MinusGenerators.complementary_floor_sum
#print axioms Catalan.θminus_coeff_eq_neg_one_or_one
#print axioms Catalan.θminus_size_eq
#print axioms Catalan.θminus_size_le
#print axioms Catalan.ΘS_mul_single
#print axioms Catalan.pθ_mul_single
#print axioms Catalan.stickSpan_mul_single
#print axioms Catalan.θminus_mem
#print axioms Catalan.θminus_small_three
#print axioms Catalan.θminus_small_five
#print axioms Catalan.θminus_small_seven
#print axioms Catalan.minus_element_ne_zero
#print axioms Catalan.minus_element_size
#print axioms Catalan.q_smul_mem_mihIdeal
#print axioms Catalan.θminus_mem_mihIdeal
#print axioms Catalan.small_minus_mem_mihAug
#print axioms Catalan.small_conductor_aug_witness

/-! ### Integral minus span and character boundary reductions (2026-09-18) -/

#check @Catalan.minusLinearMap
#check @Catalan.minusGeneratorSpan
#check @Catalan.pθ_coeff
#check @Catalan.ΘS_one
#check @Catalan.minus_theta_reflection
#check @Catalan.theta_minus_spans_of_reflection
#check @Catalan.theta_minus_spans
#check @Catalan.LFunction_zero_ne_zero_of_prime_odd
#check @Catalan.LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero
#check @Catalan.odd_character_weighted_sum_ne_zero_of_hurwitz_zero
#check @Catalan.hurwitzZeta_zero_eq_sinZeta_one_div_pi
#check @Catalan.hurwitzZeta_zero_eq_sine_value_of_mem_Ioo
#check @Catalan.cauchySeq_unit_circle_log_partial_sums
#check @Catalan.tendsto_unit_circle_log_partial_sums

#print axioms Catalan.minusLinearMap
#print axioms Catalan.minusGeneratorSpan
#print axioms Catalan.pθ_coeff
#print axioms Catalan.ΘS_one
#print axioms Catalan.minus_theta_reflection
#print axioms Catalan.theta_minus_spans_of_reflection
#print axioms Catalan.theta_minus_spans
#print axioms Catalan.LFunction_zero_ne_zero_of_prime_odd
#print axioms Catalan.LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero
#print axioms Catalan.odd_character_weighted_sum_ne_zero_of_hurwitz_zero
#print axioms Catalan.hurwitzZeta_zero_eq_sinZeta_one_div_pi
#print axioms Catalan.hurwitzZeta_zero_eq_sine_value_of_mem_Ioo
#print axioms Catalan.cauchySeq_unit_circle_log_partial_sums
#print axioms Catalan.tendsto_unit_circle_log_partial_sums

/-! ### Hurwitz zero value and odd character nonvanishing (2026-09-18) -/

#check @Catalan.exp_two_pi_norm
#check @Catalan.exp_two_pi_ne_one
#check @Catalan.exp_two_pi_pow
#check @Catalan.unit_circle_dirichlet_tail_bound
#check @Catalan.tendsto_expZeta_one_partial_sums_of_tail_bound
#check @Catalan.arg_one_sub_exp_two_pi
#check @Catalan.log_one_sub_exp_two_pi_difference
#check @Catalan.tendsto_expZeta_one_partial_sums
#check @Catalan.expZeta_one_eq_neg_log
#check @Catalan.sinZeta_one_eq_of_mem_Ioo
#check @Catalan.hurwitzZeta_apply_zero_of_mem_Ioo
#check @Catalan.LFunction_zero_eq_neg_weighted_sum
#check @Catalan.odd_character_weighted_sum_ne_zero

#print axioms Catalan.exp_two_pi_norm
#print axioms Catalan.exp_two_pi_ne_one
#print axioms Catalan.exp_two_pi_pow
#print axioms Catalan.unit_circle_dirichlet_tail_bound
#print axioms Catalan.tendsto_expZeta_one_partial_sums_of_tail_bound
#print axioms Catalan.arg_one_sub_exp_two_pi
#print axioms Catalan.log_one_sub_exp_two_pi_difference
#print axioms Catalan.tendsto_expZeta_one_partial_sums
#print axioms Catalan.expZeta_one_eq_neg_log
#print axioms Catalan.sinZeta_one_eq_of_mem_Ioo
#print axioms Catalan.hurwitzZeta_apply_zero_of_mem_Ioo
#print axioms Catalan.LFunction_zero_eq_neg_weighted_sum
#print axioms Catalan.odd_character_weighted_sum_ne_zero

/-! ### Original theta-minus independence (2026-09-18) -/

#check @Catalan.MinusIndependence.ComplexRing
#check @Catalan.MinusIndependence.coeffCast
#check @Catalan.MinusIndependence.characterOnG
#check @Catalan.MinusIndependence.characterEval
#check @Catalan.MinusIndependence.complexPTheta
#check @Catalan.MinusIndependence.complexMinus
#check @Catalan.MinusIndependence.minusRange
#check @Catalan.MinusIndependence.halfUnit
#check @Catalan.MinusIndependence.halfVector
#check @Catalan.MinusIndependence.thetaVector
#check @Catalan.MinusIndependence.coeffCast_coeff
#check @Catalan.MinusIndependence.coeffCast_single
#check @Catalan.MinusIndependence.coeffCast_injective
#check @Catalan.unit_character_recovery
#check @Catalan.unit_character_transform_injective
#check @Catalan.MinusIndependence.characterOnG_sigma_inv
#check @Catalan.MinusIndependence.characterEval_coeff
#check @Catalan.MinusIndependence.characterEval_PTheta
#check @Catalan.MinusIndependence.characterEval_minus
#check @Catalan.MinusIndependence.characterEval_joint_injective
#check @Catalan.MinusIndependence.complexPTheta_mul_eq_zero
#check @Catalan.MinusIndependence.halfVector_coeff
#check @Catalan.MinusIndependence.halfVector_linearIndependent
#check @Catalan.MinusIndependence.halfVector_mem_minusRange
#check @Catalan.MinusIndependence.coeffCast_mem_theta_span
#check @Catalan.MinusIndependence.complexPTheta_mul_halfVector_mem_span
#check @Catalan.MinusIndependence.thetaVector_linearIndependent
#check @Catalan.θminus_linIndep

#print axioms Catalan.MinusIndependence.ComplexRing
#print axioms Catalan.MinusIndependence.coeffCast
#print axioms Catalan.MinusIndependence.characterOnG
#print axioms Catalan.MinusIndependence.characterEval
#print axioms Catalan.MinusIndependence.complexPTheta
#print axioms Catalan.MinusIndependence.complexMinus
#print axioms Catalan.MinusIndependence.minusRange
#print axioms Catalan.MinusIndependence.halfUnit
#print axioms Catalan.MinusIndependence.halfVector
#print axioms Catalan.MinusIndependence.thetaVector
#print axioms Catalan.MinusIndependence.coeffCast_coeff
#print axioms Catalan.MinusIndependence.coeffCast_single
#print axioms Catalan.MinusIndependence.coeffCast_injective
#print axioms Catalan.unit_character_recovery
#print axioms Catalan.unit_character_transform_injective
#print axioms Catalan.MinusIndependence.characterOnG_sigma_inv
#print axioms Catalan.MinusIndependence.characterEval_coeff
#print axioms Catalan.MinusIndependence.characterEval_PTheta
#print axioms Catalan.MinusIndependence.characterEval_minus
#print axioms Catalan.MinusIndependence.characterEval_joint_injective
#print axioms Catalan.MinusIndependence.complexPTheta_mul_eq_zero
#print axioms Catalan.MinusIndependence.halfVector_coeff
#print axioms Catalan.MinusIndependence.halfVector_linearIndependent
#print axioms Catalan.MinusIndependence.halfVector_mem_minusRange
#print axioms Catalan.MinusIndependence.coeffCast_mem_theta_span
#print axioms Catalan.MinusIndependence.complexPTheta_mul_halfVector_mem_span
#print axioms Catalan.MinusIndependence.thetaVector_linearIndependent
#print axioms Catalan.θminus_linIndep

-- Coefficient balls and explicit card-upper reductions.
#check @Catalan.size_zsmul
#check @Catalan.weight_zsmul
#check @Catalan.size_sum_le
#check @Catalan.weight_sum
#check @Catalan.thetaCombination
#check @Catalan.thetaCombination_injective
#check @Catalan.thetaCombination_weight
#check @Catalan.thetaCombination_size
#check @Catalan.thetaCombination_mem_mihIdeal
#check @Catalan.thetaCombination_mem_augBall
#check @Catalan.S_le_card_augBall
#check @Catalan.S_le_card_augBall_quotient
#check @Catalan.q_lt_four_sq_of_aug_card_upper
#check @Catalan.q_lt_180_of_aug_card_upper
#check @Catalan.q_lt_144_of_aug_card_upper
#check @Catalan.q_lt_four_sq_of_lattice_upper
#check @Catalan.q_lt_180_of_lattice_upper
#check @Catalan.q_lt_144_of_lattice_upper
#check @Catalan.quotient_radius_le
#check @Catalan.hyyro_implies_h8_one
#check @Catalan.hyyro_implies_h9
#check @Catalan.cassels_x_mod_one

#print axioms Catalan.size_zsmul
#print axioms Catalan.weight_zsmul
#print axioms Catalan.size_sum_le
#print axioms Catalan.weight_sum
#print axioms Catalan.thetaCombination
#print axioms Catalan.thetaCombination_injective
#print axioms Catalan.thetaCombination_weight
#print axioms Catalan.thetaCombination_size
#print axioms Catalan.thetaCombination_mem_mihIdeal
#print axioms Catalan.thetaCombination_mem_augBall
#print axioms Catalan.S_le_card_augBall
#print axioms Catalan.S_le_card_augBall_quotient
#print axioms Catalan.q_lt_four_sq_of_aug_card_upper
#print axioms Catalan.q_lt_180_of_aug_card_upper
#print axioms Catalan.q_lt_144_of_aug_card_upper
#print axioms Catalan.q_lt_four_sq_of_lattice_upper
#print axioms Catalan.q_lt_180_of_lattice_upper
#print axioms Catalan.q_lt_144_of_lattice_upper
#print axioms Catalan.quotient_radius_le
#print axioms Catalan.hyyro_implies_h8_one
#print axioms Catalan.hyyro_implies_h9
#print axioms Catalan.cassels_x_mod_one

#check @Catalan.augBall_eq_singleton_of_lt_two
#check @Catalan.card_aug_ball_le_of_q_eq_two

#print axioms Catalan.augBall_eq_singleton_of_lt_two
#print axioms Catalan.card_aug_ball_le_of_q_eq_two

-- Normalized heights, actual phase/card bounds and radius-two exclusion.
#check @Catalan.logHeight
#check @Catalan.logHeight_eq_normalized
#check @Catalan.height_pow
#check @Catalan.height_inv
#check @Catalan.height_sub_le
#check @Catalan.height_div_le
#check @Catalan.height_one
#check @Catalan.height_intCast
#check @Catalan.height_root_unity
#check @Catalan.height_projective_integral_le
#check @Catalan.height_liouville_complex
#check @Catalan.height_lt_of_local_bounds
#check @Catalan.upow_xmζ_eq_nat_prod
#check @Catalan.integral_upow_xmζ_of_nonneg
#check @Catalan.sum_coeff_toNat_eq_size
#check @Catalan.infinitePlace_upow_xmζ_le
#check @Catalan.prop44_height
#check @Catalan.prop47_height
#check @Catalan.phase_kernel
#check @Catalan.phase_injective_ball
#check @Catalan.card_aug_ball_le
#check @Catalan.prop42_reconstruct_height
#check @Catalan.prop42_arch_bound
#check @Catalan.prop42_height_lt
#check @Catalan.aug_two_eq_zero_of_h9
#check @Catalan.aug_two_eq_zero

#print axioms Catalan.logHeight
#print axioms Catalan.logHeight_eq_normalized
#print axioms Catalan.height_pow
#print axioms Catalan.height_inv
#print axioms Catalan.height_sub_le
#print axioms Catalan.height_div_le
#print axioms Catalan.height_one
#print axioms Catalan.height_intCast
#print axioms Catalan.height_root_unity
#print axioms Catalan.height_projective_integral_le
#print axioms Catalan.height_liouville_complex
#print axioms Catalan.height_lt_of_local_bounds
#print axioms Catalan.upow_xmζ_eq_nat_prod
#print axioms Catalan.integral_upow_xmζ_of_nonneg
#print axioms Catalan.sum_coeff_toNat_eq_size
#print axioms Catalan.infinitePlace_upow_xmζ_le
#print axioms Catalan.prop44_height
#print axioms Catalan.prop47_height
#print axioms Catalan.phase_kernel
#print axioms Catalan.phase_injective_ball
#print axioms Catalan.card_aug_ball_le
#print axioms Catalan.prop42_reconstruct_height
#print axioms Catalan.prop42_arch_bound
#print axioms Catalan.prop42_height_lt
#print axioms Catalan.aug_two_eq_zero_of_h9
#print axioms Catalan.aug_two_eq_zero

-- Original signed Case 2 and acyclic small-conductor assembly.
#check @Catalan.small_odd_prime_no_solution
#check @Catalan.nagell_p_three
#check @Catalan.q_lt_four_sq
#check @Catalan.q_lt_180_of_p_seven
#check @Catalan.q_lt_144_of_p_five
#check @Catalan.solution_symm
#check @Catalan.case_two

#print axioms Catalan.small_odd_prime_no_solution
#print axioms Catalan.nagell_p_three
#print axioms Catalan.q_lt_four_sq
#print axioms Catalan.q_lt_180_of_p_seven
#print axioms Catalan.q_lt_144_of_p_five
#print axioms Catalan.solution_symm
#print axioms Catalan.case_two

-- Unit-radical field and primary residue obstruction.
#check @Catalan.A3.instFiniteDimensionalF
#check @Catalan.A3.instNumberFieldF
#check @Catalan.A3.instFiniteDimensionalB
#check @Catalan.A3.instNumberFieldB
#check @Catalan.Semisimple.groupRing_ideal_mul_self
#check @Catalan.Semisimple.groupRing_ideal_pow_eq_self
#check @Catalan.Semisimple.groupRing_ideal_mul_eq_inf
#check @Catalan.A3.finiteDimensional_Msub
#check @Catalan.A3.numberField_Msub
#check @Catalan.A3.isCyclotomicExtension_Bsub
#check @Catalan.A3.isGalois_Bsub
#check @Catalan.A3.isGalois_Msub
#check @Catalan.Primary.square_dvd_pow_sub_pow
#check @Catalan.Primary.prime_dvd_of_dvd_pow
#check @Catalan.Primary.primaryPolynomial
#check @Catalan.Primary.primaryPolynomial_natDegree_lt
#check @Catalan.Primary.primaryPolynomial_coeff_pred
#check @Catalan.Primary.primaryPolynomial_identity
#check @Catalan.Primary.primaryPolynomial_natDegree
#check @Catalan.Primary.primaryPolynomial_monic
#check @Catalan.Primary.powerBasis_dvd_aeval_coeff
#check @Catalan.Primary.not_dvd_primaryPolynomial_eval
#check @Catalan.Primary.zeta_sum_not_qth_mod_square

#print axioms Catalan.A3.instFiniteDimensionalF
#print axioms Catalan.A3.instNumberFieldF
#print axioms Catalan.A3.instFiniteDimensionalB
#print axioms Catalan.A3.instNumberFieldB
#print axioms Catalan.Semisimple.groupRing_ideal_mul_self
#print axioms Catalan.Semisimple.groupRing_ideal_pow_eq_self
#print axioms Catalan.Semisimple.groupRing_ideal_mul_eq_inf
#print axioms Catalan.A3.finiteDimensional_Msub
#print axioms Catalan.A3.numberField_Msub
#print axioms Catalan.A3.isCyclotomicExtension_Bsub
#print axioms Catalan.A3.isGalois_Bsub
#print axioms Catalan.A3.isGalois_Msub
#print axioms Catalan.Primary.square_dvd_pow_sub_pow
#print axioms Catalan.Primary.prime_dvd_of_dvd_pow
#print axioms Catalan.Primary.primaryPolynomial
#print axioms Catalan.Primary.primaryPolynomial_natDegree_lt
#print axioms Catalan.Primary.primaryPolynomial_coeff_pred
#print axioms Catalan.Primary.primaryPolynomial_identity
#print axioms Catalan.Primary.primaryPolynomial_natDegree
#print axioms Catalan.Primary.primaryPolynomial_monic
#print axioms Catalan.Primary.powerBasis_dvd_aeval_coeff
#print axioms Catalan.Primary.not_dvd_primaryPolynomial_eval
#print axioms Catalan.Primary.zeta_sum_not_qth_mod_square

-- Real-field structure and full circular/primary unit groups.
#check @Catalan.A3.isTotallyReal_F
#check @Catalan.A3.isAbelianGalois_F
#check @Catalan.A3.finrank_F
#check @Catalan.A3.gal_F_cyclic
#check @Catalan.A3.card_gal_F
#check @Catalan.Circular.exists_ratio_unit
#check @Catalan.UnitQuotient.qPowers
#check @Catalan.UnitQuotient.ModSquare
#check @Catalan.UnitQuotient.modSquareUnit
#check @Catalan.UnitQuotient.primaryUnits
#check @Catalan.UnitQuotient.mem_primaryUnits_iff
#check @Catalan.UnitQuotient.qPowers_le_primaryUnits
#check @Catalan.UnitQuotient.primaryUnits_map
#check @Catalan.UnitQuotient.primaryUnits_map_equiv_iff
#check @Catalan.Circular.unitAction
#check @Catalan.Circular.unitAction_coe
#check @Catalan.Circular.circularUnits
#check @Catalan.Circular.primaryCircularUnits
#check @Catalan.Circular.exists_zeta_sum_circular
#check @Catalan.Circular.primaryCircularUnits_ne
#check @Catalan.Circular.circularUnits_stable
#check @Catalan.Circular.primaryCircularUnits_stable

#print axioms Catalan.A3.isTotallyReal_F
#print axioms Catalan.A3.isAbelianGalois_F
#print axioms Catalan.A3.finrank_F
#print axioms Catalan.A3.gal_F_cyclic
#print axioms Catalan.A3.card_gal_F
#print axioms Catalan.Circular.exists_ratio_unit
#print axioms Catalan.UnitQuotient.qPowers
#print axioms Catalan.UnitQuotient.ModSquare
#print axioms Catalan.UnitQuotient.modSquareUnit
#print axioms Catalan.UnitQuotient.primaryUnits
#print axioms Catalan.UnitQuotient.mem_primaryUnits_iff
#print axioms Catalan.UnitQuotient.qPowers_le_primaryUnits
#print axioms Catalan.UnitQuotient.primaryUnits_map
#print axioms Catalan.UnitQuotient.primaryUnits_map_equiv_iff
#print axioms Catalan.Circular.unitAction
#print axioms Catalan.Circular.unitAction_coe
#print axioms Catalan.Circular.circularUnits
#print axioms Catalan.Circular.primaryCircularUnits
#print axioms Catalan.Circular.exists_zeta_sum_circular
#print axioms Catalan.Circular.primaryCircularUnits_ne
#print axioms Catalan.Circular.circularUnits_stable
#print axioms Catalan.Circular.primaryCircularUnits_stable

-- Actual unit power representation, circular image filtration, and Dirichlet logarithms.
#check @Catalan.UnitQuotient.PowerQuotient
#check @Catalan.UnitQuotient.powerClass
#check @Catalan.UnitQuotient.powerQuotient_exponent
#check @Catalan.UnitQuotient.powerQuotientModule
#check @Catalan.UnitQuotient.powerMap
#check @Catalan.UnitQuotient.powerMap_apply
#check @Catalan.UnitQuotient.powerImage
#check @Catalan.UnitQuotient.mem_powerImage_iff
#check @Catalan.UnitQuotient.powerImage_inf_eq_iff
#check @Catalan.UnitQuotient.unitTorsionMap
#check @Catalan.UnitQuotient.torsion_le_qPowers
#check @Catalan.UnitQuotient.unitTorsionMap_bijective
#check @Catalan.UnitModule.unitRepresentation
#check @Catalan.UnitModule.UnitPowerModule
#check @Catalan.UnitModule.unitClass
#check @Catalan.UnitModule.unitClass_surjective
#check @Catalan.UnitModule.single_smul_unitClass
#check @Catalan.UnitModule.stableUnitImage
#check @Catalan.UnitModule.mem_stableUnitImage_iff
#check @Catalan.UnitModule.circularImage
#check @Catalan.UnitModule.primaryCircularImage
#check @Catalan.UnitModule.primaryCircularImage_le
#check @Catalan.UnitModule.primaryCircularImage_ne
#check @Catalan.UnitModule.primaryCircularImage_lt
#check @Catalan.UnitLog.fullLog
#check @Catalan.UnitLog.zeroSum
#check @Catalan.UnitLog.fullLog_one
#check @Catalan.UnitLog.fullLog_mul
#check @Catalan.UnitLog.fullLog_sum
#check @Catalan.UnitLog.fullLog_eq_zero_iff
#check @Catalan.UnitLog.fullLog_span
#check @Catalan.UnitLog.fullLog_unitAction

#print axioms Catalan.UnitQuotient.PowerQuotient
#print axioms Catalan.UnitQuotient.powerClass
#print axioms Catalan.UnitQuotient.powerQuotient_exponent
#print axioms Catalan.UnitQuotient.powerQuotientModule
#print axioms Catalan.UnitQuotient.powerMap
#print axioms Catalan.UnitQuotient.powerMap_apply
#print axioms Catalan.UnitQuotient.powerImage
#print axioms Catalan.UnitQuotient.mem_powerImage_iff
#print axioms Catalan.UnitQuotient.powerImage_inf_eq_iff
#print axioms Catalan.UnitQuotient.unitTorsionMap
#print axioms Catalan.UnitQuotient.torsion_le_qPowers
#print axioms Catalan.UnitQuotient.unitTorsionMap_bijective
#print axioms Catalan.UnitModule.unitRepresentation
#print axioms Catalan.UnitModule.UnitPowerModule
#print axioms Catalan.UnitModule.unitClass
#print axioms Catalan.UnitModule.unitClass_surjective
#print axioms Catalan.UnitModule.single_smul_unitClass
#print axioms Catalan.UnitModule.stableUnitImage
#print axioms Catalan.UnitModule.mem_stableUnitImage_iff
#print axioms Catalan.UnitModule.circularImage
#print axioms Catalan.UnitModule.primaryCircularImage
#print axioms Catalan.UnitModule.primaryCircularImage_le
#print axioms Catalan.UnitModule.primaryCircularImage_ne
#print axioms Catalan.UnitModule.primaryCircularImage_lt
#print axioms Catalan.UnitLog.fullLog
#print axioms Catalan.UnitLog.zeroSum
#print axioms Catalan.UnitLog.fullLog_one
#print axioms Catalan.UnitLog.fullLog_mul
#print axioms Catalan.UnitLog.fullLog_sum
#print axioms Catalan.UnitLog.fullLog_eq_zero_iff
#print axioms Catalan.UnitLog.fullLog_span
#print axioms Catalan.UnitLog.fullLog_unitAction

-- Actual integral unit actions and real/mod-q characteristic-polynomial transports.
#check @Catalan.UnitQuotient.powerQuotientModN
#check @Catalan.UnitQuotient.powerQuotientModN_apply
#check @Catalan.UnitQuotient.realUnitInclusion
#check @Catalan.UnitQuotient.realUnitPowerMap
#check @Catalan.UnitQuotient.realUnitPowerMap_bijective
#check @Catalan.UnitReduction.modNMap
#check @Catalan.UnitReduction.modNMap_apply
#check @Catalan.UnitReduction.modNMap_toMatrix
#check @Catalan.UnitReduction.modNModuleFree
#check @Catalan.UnitReduction.modNMap_charpoly
#check @Catalan.UnitLog.charpoly_eq_map_of_lattice_intertwining
#check @Catalan.UnitLog.logSpaceLift
#check @Catalan.UnitLog.logSpaceLift_mem
#check @Catalan.UnitLog.logSpaceEquiv
#check @Catalan.UnitLog.logSpaceEquiv_logEmbedding
#check @Catalan.UnitLog.placeEquiv
#check @Catalan.UnitLog.zeroSumAction
#check @Catalan.UnitLog.logRealAction
#check @Catalan.UnitLog.logRealAction_logEmbedding
#check @Catalan.UnitLog.gal_place_bijective
#check @Catalan.UnitLog.galPlaceEquiv
#check @Catalan.UnitLog.galPlaceEquiv_mul
#check @Catalan.UnitLog.groupZeroSum
#check @Catalan.UnitLog.regularZeroSumAction
#check @Catalan.UnitLog.regularZeroSumAction_apply
#check @Catalan.UnitLog.zeroSumRegularEquiv
#check @Catalan.UnitLog.zeroSumRegularEquiv_apply
#check @Catalan.UnitLog.zeroSumRegularEquiv_intertwining
#check @Catalan.UnitModule.UnitLattice
#check @Catalan.UnitModule.unitLatticeIntModule
#check @Catalan.UnitModule.integralUnitClass
#check @Catalan.UnitModule.torsionAction
#check @Catalan.UnitModule.torsionAction_apply
#check @Catalan.UnitModule.integralUnitRepresentation
#check @Catalan.UnitModule.integralUnitRepresentation_apply
#check @Catalan.UnitModule.integralUnitClass_surjective
#check @Catalan.UnitModule.unitTorsionMap_equivariant
#check @Catalan.UnitModule.logLatticeAction
#check @Catalan.UnitModule.logLatticeAction_intertwining
#check @Catalan.UnitModule.integralUnit_charpoly_real
#check @Catalan.UnitModule.unitPowerModuleFinite
#check @Catalan.UnitModule.unitReductionMap
#check @Catalan.UnitModule.unitReductionMap_apply
#check @Catalan.UnitModule.unitReductionMap_intertwining
#check @Catalan.UnitModule.logRegularEquiv
#check @Catalan.UnitModule.logRegularEquiv_intertwining
#check @Catalan.UnitModule.integralUnit_charpoly_regular
#check @Catalan.UnitModule.unitReductionMap_bijective
#check @Catalan.UnitModule.unitReductionEquiv
#check @Catalan.UnitModule.unitRepresentation_charpoly

#print axioms Catalan.UnitQuotient.powerQuotientModN
#print axioms Catalan.UnitQuotient.powerQuotientModN_apply
#print axioms Catalan.UnitQuotient.realUnitInclusion
#print axioms Catalan.UnitQuotient.realUnitPowerMap
#print axioms Catalan.UnitQuotient.realUnitPowerMap_bijective
#print axioms Catalan.UnitReduction.modNMap
#print axioms Catalan.UnitReduction.modNMap_apply
#print axioms Catalan.UnitReduction.modNMap_toMatrix
#print axioms Catalan.UnitReduction.modNModuleFree
#print axioms Catalan.UnitReduction.modNMap_charpoly
#print axioms Catalan.UnitLog.charpoly_eq_map_of_lattice_intertwining
#print axioms Catalan.UnitLog.logSpaceLift
#print axioms Catalan.UnitLog.logSpaceLift_mem
#print axioms Catalan.UnitLog.logSpaceEquiv
#print axioms Catalan.UnitLog.logSpaceEquiv_logEmbedding
#print axioms Catalan.UnitLog.placeEquiv
#print axioms Catalan.UnitLog.zeroSumAction
#print axioms Catalan.UnitLog.logRealAction
#print axioms Catalan.UnitLog.logRealAction_logEmbedding
#print axioms Catalan.UnitLog.gal_place_bijective
#print axioms Catalan.UnitLog.galPlaceEquiv
#print axioms Catalan.UnitLog.galPlaceEquiv_mul
#print axioms Catalan.UnitLog.groupZeroSum
#print axioms Catalan.UnitLog.regularZeroSumAction
#print axioms Catalan.UnitLog.regularZeroSumAction_apply
#print axioms Catalan.UnitLog.zeroSumRegularEquiv
#print axioms Catalan.UnitLog.zeroSumRegularEquiv_apply
#print axioms Catalan.UnitLog.zeroSumRegularEquiv_intertwining
#print axioms Catalan.UnitModule.UnitLattice
#print axioms Catalan.UnitModule.unitLatticeIntModule
#print axioms Catalan.UnitModule.integralUnitClass
#print axioms Catalan.UnitModule.torsionAction
#print axioms Catalan.UnitModule.torsionAction_apply
#print axioms Catalan.UnitModule.integralUnitRepresentation
#print axioms Catalan.UnitModule.integralUnitRepresentation_apply
#print axioms Catalan.UnitModule.integralUnitClass_surjective
#print axioms Catalan.UnitModule.unitTorsionMap_equivariant
#print axioms Catalan.UnitModule.logLatticeAction
#print axioms Catalan.UnitModule.logLatticeAction_intertwining
#print axioms Catalan.UnitModule.integralUnit_charpoly_real
#print axioms Catalan.UnitModule.unitPowerModuleFinite
#print axioms Catalan.UnitModule.unitReductionMap
#print axioms Catalan.UnitModule.unitReductionMap_apply
#print axioms Catalan.UnitModule.unitReductionMap_intertwining
#print axioms Catalan.UnitModule.logRegularEquiv
#print axioms Catalan.UnitModule.logRegularEquiv_intertwining
#print axioms Catalan.UnitModule.integralUnit_charpoly_regular
#print axioms Catalan.UnitModule.unitReductionMap_bijective
#print axioms Catalan.UnitModule.unitReductionEquiv
#print axioms Catalan.UnitModule.unitRepresentation_charpoly

-- Actual generator geometric-sum characteristic polynomial and signed solution adapters.
#check @Catalan.UnitLog.cyclicShift
#check @Catalan.UnitLog.cyclicShift_charpoly
#check @Catalan.UnitLog.cyclicZeroSum
#check @Catalan.UnitLog.cyclicZeroSumShift
#check @Catalan.UnitLog.cyclicZeroSumShift_apply
#check @Catalan.UnitLog.cyclicZeroSumShift_charpoly
#check @Catalan.UnitLog.exists_place_cycle_equiv
#check @Catalan.UnitLog.cycleZeroSumEquiv
#check @Catalan.UnitLog.cycleZeroSumEquiv_intertwining
#check @Catalan.UnitLog.logRealAction_charpoly_of_generator
#check @Catalan.UnitReduction.geometricSum_squarefree
#check @Catalan.UnitModule.cyclotomicGal_cyclic
#check @Catalan.UnitModule.exists_cyclotomic_generator
#check @Catalan.UnitModule.cyclotomicPlace_card
#check @Catalan.UnitModule.integralUnit_charpoly_of_generator
#check @Catalan.UnitModule.not_dvd_half_pred_of_not_modEq_one
#check @Catalan.UnitModule.not_dvd_place_card_of_solution
#check @Catalan.UnitModule.unit_charpoly_of_generator
#check @Catalan.UnitModule.unit_charpoly_halfdegree
#check @Catalan.UnitModule.unit_generator_charpoly_squarefree
#check @Catalan.UnitModule.unit_generator_isSemisimple
#check @Catalan.UnitModule.unit_generator_charpoly_squarefree_of_solution
#check @Catalan.UnitModule.unit_generator_isSemisimple_of_solution

#print axioms Catalan.UnitLog.cyclicShift
#print axioms Catalan.UnitLog.cyclicShift_charpoly
#print axioms Catalan.UnitLog.cyclicZeroSum
#print axioms Catalan.UnitLog.cyclicZeroSumShift
#print axioms Catalan.UnitLog.cyclicZeroSumShift_apply
#print axioms Catalan.UnitLog.cyclicZeroSumShift_charpoly
#print axioms Catalan.UnitLog.exists_place_cycle_equiv
#print axioms Catalan.UnitLog.cycleZeroSumEquiv
#print axioms Catalan.UnitLog.cycleZeroSumEquiv_intertwining
#print axioms Catalan.UnitLog.logRealAction_charpoly_of_generator
#print axioms Catalan.UnitReduction.geometricSum_squarefree
#print axioms Catalan.UnitModule.cyclotomicGal_cyclic
#print axioms Catalan.UnitModule.exists_cyclotomic_generator
#print axioms Catalan.UnitModule.cyclotomicPlace_card
#print axioms Catalan.UnitModule.integralUnit_charpoly_of_generator
#print axioms Catalan.UnitModule.not_dvd_half_pred_of_not_modEq_one
#print axioms Catalan.UnitModule.not_dvd_place_card_of_solution
#print axioms Catalan.UnitModule.unit_charpoly_of_generator
#print axioms Catalan.UnitModule.unit_charpoly_halfdegree
#print axioms Catalan.UnitModule.unit_generator_charpoly_squarefree
#print axioms Catalan.UnitModule.unit_generator_isSemisimple
#print axioms Catalan.UnitModule.unit_generator_charpoly_squarefree_of_solution
#print axioms Catalan.UnitModule.unit_generator_isSemisimple_of_solution

-- Actual cyclic vector and unit group-ring module cyclicity.
#check @Catalan.UnitReduction.exists_cyclic_vector_of_squarefree_charpoly
#check @Catalan.UnitReduction.representation_cyclic_of_polynomial_cyclic
#check @Catalan.UnitModule.unit_module_cyclic
#check @Catalan.UnitModule.unit_module_cyclic_of_solution

#print axioms Catalan.UnitReduction.exists_cyclic_vector_of_squarefree_charpoly
#print axioms Catalan.UnitReduction.representation_cyclic_of_polynomial_cyclic
#print axioms Catalan.UnitModule.unit_module_cyclic
#print axioms Catalan.UnitModule.unit_module_cyclic_of_solution

-- Actual norm/plus annihilator, circular-image filtration, and plus-ideal duality.
#check @Catalan.UnitReduction.minpoly_eq_charpoly_of_polynomial_cyclic
#check @Catalan.UnitReduction.cyclic_group_algebra_aeval_surjective
#check @Catalan.UnitReduction.annihilator_sup_eq_top_of_cyclic_prod
#check @Catalan.UnitReduction.annihilator_prod_eq_mul_of_cyclic_prod
#check @Catalan.UnitReduction.representation_annihilator_eq_span_minpoly
#check @Catalan.UnitReduction.submodule_cyclic_of_semisimple
#check @Catalan.UnitReduction.annihilator_quotient_sup_of_cyclic_semisimple
#check @Catalan.UnitReduction.annihilator_eq_mul_quotient_of_cyclic_semisimple
#check @Catalan.UnitReduction.groupNorm
#check @Catalan.UnitReduction.groupNorm_eq_sum_powers
#check @Catalan.UnitReduction.span_geometric_eq_norm_pair
#check @Catalan.UnitReduction.three_step_annihilator_pairwise
#check @Catalan.UnitReduction.three_step_annihilator_product
#check @Catalan.UnitReduction.semisimple_ideal_double_annihilator
#check @Catalan.UnitReduction.semisimple_ideal_annihilator_mul
#check @Catalan.UnitReduction.annihilator_span_one_add_involution
#check @Catalan.UnitModule.gal_generator_order
#check @Catalan.UnitModule.generator_half_eq_iota
#check @Catalan.UnitModule.cyclotomicGalCommGroup
#check @Catalan.UnitModule.cyclotomicGal_card
#check @Catalan.UnitModule.not_dvd_gal_card_of_solution
#check @Catalan.UnitModule.unitPower_semisimple
#check @Catalan.UnitModule.normPlusIdeal
#check @Catalan.UnitModule.unit_generator_minpoly
#check @Catalan.UnitModule.unit_annihilator_eq_normPlus
#check @Catalan.UnitModule.unit_annihilator_eq_normPlus_of_solution
#check @Catalan.UnitModule.topUnitAnn
#check @Catalan.UnitModule.middleUnitAnn
#check @Catalan.UnitModule.bottomUnitAnn
#check @Catalan.UnitModule.unit_filtration_pairwise_of_solution
#check @Catalan.UnitModule.unit_filtration_product_of_solution
#check @Catalan.UnitModule.middleUnitAnn_ne_top
#check @Catalan.UnitModule.iota_square
#check @Catalan.UnitModule.plusAugIdeal
#check @Catalan.UnitModule.plusAugIdeal_annihilator
#check @Catalan.UnitModule.plusAugIdeal_annihilator_of_solution
#check @Catalan.UnitModule.plusAug_unit_annihilator_of_solution

#print axioms Catalan.UnitReduction.minpoly_eq_charpoly_of_polynomial_cyclic
#print axioms Catalan.UnitReduction.cyclic_group_algebra_aeval_surjective
#print axioms Catalan.UnitReduction.annihilator_sup_eq_top_of_cyclic_prod
#print axioms Catalan.UnitReduction.annihilator_prod_eq_mul_of_cyclic_prod
#print axioms Catalan.UnitReduction.representation_annihilator_eq_span_minpoly
#print axioms Catalan.UnitReduction.submodule_cyclic_of_semisimple
#print axioms Catalan.UnitReduction.annihilator_quotient_sup_of_cyclic_semisimple
#print axioms Catalan.UnitReduction.annihilator_eq_mul_quotient_of_cyclic_semisimple
#print axioms Catalan.UnitReduction.groupNorm
#print axioms Catalan.UnitReduction.groupNorm_eq_sum_powers
#print axioms Catalan.UnitReduction.span_geometric_eq_norm_pair
#print axioms Catalan.UnitReduction.three_step_annihilator_pairwise
#print axioms Catalan.UnitReduction.three_step_annihilator_product
#print axioms Catalan.UnitReduction.semisimple_ideal_double_annihilator
#print axioms Catalan.UnitReduction.semisimple_ideal_annihilator_mul
#print axioms Catalan.UnitReduction.annihilator_span_one_add_involution
#print axioms Catalan.UnitModule.gal_generator_order
#print axioms Catalan.UnitModule.generator_half_eq_iota
#print axioms Catalan.UnitModule.cyclotomicGalCommGroup
#print axioms Catalan.UnitModule.cyclotomicGal_card
#print axioms Catalan.UnitModule.not_dvd_gal_card_of_solution
#print axioms Catalan.UnitModule.unitPower_semisimple
#print axioms Catalan.UnitModule.normPlusIdeal
#print axioms Catalan.UnitModule.unit_generator_minpoly
#print axioms Catalan.UnitModule.unit_annihilator_eq_normPlus
#print axioms Catalan.UnitModule.unit_annihilator_eq_normPlus_of_solution
#print axioms Catalan.UnitModule.topUnitAnn
#print axioms Catalan.UnitModule.middleUnitAnn
#print axioms Catalan.UnitModule.bottomUnitAnn
#print axioms Catalan.UnitModule.unit_filtration_pairwise_of_solution
#print axioms Catalan.UnitModule.unit_filtration_product_of_solution
#print axioms Catalan.UnitModule.middleUnitAnn_ne_top
#print axioms Catalan.UnitModule.iota_square
#print axioms Catalan.UnitModule.plusAugIdeal
#print axioms Catalan.UnitModule.plusAugIdeal_annihilator
#print axioms Catalan.UnitModule.plusAugIdeal_annihilator_of_solution
#print axioms Catalan.UnitModule.plusAug_unit_annihilator_of_solution

-- Actual real-field units, dual projective vectors, and Kummer base injection.
#check @Catalan.UnitQuotient.unitTorsionMap_bijective_of_torsion_le
#check @Catalan.UnitModule.unitReductionMap_bijective_of_torsion_le
#check @Catalan.UnitModule.unitRepresentation_charpoly_of_torsion_le
#check @Catalan.UnitQuotient.real_units_pow_injective
#check @Catalan.UnitQuotient.real_torsion_le_qPowers
#check @Catalan.A3.finrank_B_lt
#check @Catalan.A3.coprime_q_finrank_B
#check @Catalan.UnitReduction.dual_charpoly_eq
#check @Catalan.UnitReduction.representation_dual_charpoly
#check @Catalan.UnitReduction.cyclic_geometric_projective_rigidity
#check @Catalan.UnitModule.real_unitReductionMap_bijective
#check @Catalan.UnitModule.real_unitRepresentation_charpoly
#check @Catalan.UnitModule.real_unit_charpoly_of_generator
#check @Catalan.UnitModule.real_unit_minpoly_of_generator
#check @Catalan.UnitQuotient.field_qth_root_of_coprime_degree
#check @Catalan.UnitQuotient.unit_qth_root_of_field_qth_root
#check @Catalan.A3.F_infinitePlace_card
#check @Catalan.A3.F_unit_charpoly
#check @Catalan.A3.F_unit_dual_charpoly
#check @Catalan.A3.F_unit_dual_cyclic
#check @Catalan.A3.F_unit_dual_minpoly
#check @Catalan.A3.F_unit_dual_projective_generator
#check @Catalan.UnitQuotient.unitFieldMap
#check @Catalan.UnitQuotient.unitFieldPowerMap
#check @Catalan.UnitQuotient.unitFieldPowerMap_injective
#check @Catalan.A3.F_unit_powerMap_B_injective

#print axioms Catalan.UnitQuotient.unitTorsionMap_bijective_of_torsion_le
#print axioms Catalan.UnitModule.unitReductionMap_bijective_of_torsion_le
#print axioms Catalan.UnitModule.unitRepresentation_charpoly_of_torsion_le
#print axioms Catalan.UnitQuotient.real_units_pow_injective
#print axioms Catalan.UnitQuotient.real_torsion_le_qPowers
#print axioms Catalan.A3.finrank_B_lt
#print axioms Catalan.A3.coprime_q_finrank_B
#print axioms Catalan.UnitReduction.dual_charpoly_eq
#print axioms Catalan.UnitReduction.representation_dual_charpoly
#print axioms Catalan.UnitReduction.cyclic_geometric_projective_rigidity
#print axioms Catalan.UnitModule.real_unitReductionMap_bijective
#print axioms Catalan.UnitModule.real_unitRepresentation_charpoly
#print axioms Catalan.UnitModule.real_unit_charpoly_of_generator
#print axioms Catalan.UnitModule.real_unit_minpoly_of_generator
#print axioms Catalan.UnitQuotient.field_qth_root_of_coprime_degree
#print axioms Catalan.UnitQuotient.unit_qth_root_of_field_qth_root
#print axioms Catalan.A3.F_infinitePlace_card
#print axioms Catalan.A3.F_unit_charpoly
#print axioms Catalan.A3.F_unit_dual_charpoly
#print axioms Catalan.A3.F_unit_dual_cyclic
#print axioms Catalan.A3.F_unit_dual_minpoly
#print axioms Catalan.A3.F_unit_dual_projective_generator
#print axioms Catalan.UnitQuotient.unitFieldMap
#print axioms Catalan.UnitQuotient.unitFieldPowerMap
#print axioms Catalan.UnitQuotient.unitFieldPowerMap_injective
#print axioms Catalan.A3.F_unit_powerMap_B_injective

-- Actual multi-unit Kummer pairing and absolute M stability.
#check @Catalan.A3.isGalois_Msub_rat
#check @Catalan.Kummer.aut_fixed_of_pow_eq_one
#check @Catalan.Kummer.root_ratio_independent
#check @Catalan.Kummer.root_ratio_aut_mul
#check @Catalan.Kummer.rootsOfUnityCoordinate
#check @Catalan.Kummer.rootsOfUnityCoordinate_symm_nat
#check @Catalan.A3.kummerZeta
#check @Catalan.A3.kummerZeta_spec
#check @Catalan.A3.kummerZetaM
#check @Catalan.A3.kummerZetaM_spec
#check @Catalan.A3.exists_unitRoot_M
#check @Catalan.A3.unitRoot
#check @Catalan.A3.unitRoot_pow
#check @Catalan.A3.unitRoot_ne_zero
#check @Catalan.A3.unitRoots_algHom_ext
#check @Catalan.A3.instAlgebraBsubMsub
#check @Catalan.A3.instModuleBsubMsub
#check @Catalan.A3.instScalarTowerFBsubMsub
#check @Catalan.A3.instScalarTowerBsubMsubOmega
#check @Catalan.A3.algebraMap_Bsub_Msub_coe
#check @Catalan.A3.finiteDimensional_Msub_over_B
#check @Catalan.A3.isGalois_Msub_over_B
#check @Catalan.A3.kummerValue
#check @Catalan.A3.kummerValue_val
#check @Catalan.A3.kummerValue_eq_one_iff
#check @Catalan.A3.kummerValue_mul_left
#check @Catalan.A3.kummerValue_mul_right
#check @Catalan.A3.kummerValue_one_right
#check @Catalan.A3.kummerValue_one_left
#check @Catalan.A3.kummerPairingHom
#check @Catalan.A3.kummerPairingHom_injective
#check @Catalan.A3.unit_qth_root_of_all_aut_fix_unitRoot
#check @Catalan.A3.kummerZetaUnitM
#check @Catalan.A3.kummerZetaUnitM_spec
#check @Catalan.A3.kummerCoordinate
#check @Catalan.A3.kummerQuotientValue
#check @Catalan.A3.kummerFunctional
#check @Catalan.A3.kummerFunctional_apply
#check @Catalan.A3.kummerFunctional_apply_eq_zero_iff
#check @Catalan.A3.kummerFunctional_one
#check @Catalan.A3.kummerFunctional_mul
#check @Catalan.A3.kummerDualHom
#check @Catalan.A3.kummerDualHom_injective
#check @Catalan.A3.kummerFunctional_right_nondegenerate
#check @Catalan.A3.kummerGalCommGroup
#check @Catalan.A3.kummerGal_pow_eq_one
#check @Catalan.A3.kummerGalModule
#check @Catalan.A3.kummerPairing
#check @Catalan.A3.kummerPairing_apply
#check @Catalan.A3.kummerPairing_isPerfect
#check @Catalan.A3.kummerDualEquiv
#check @Catalan.A3.kummerDualEquiv_apply
#check @Catalan.A3.exists_kummer_aut_of_functional

#print axioms Catalan.A3.isGalois_Msub_rat
#print axioms Catalan.Kummer.aut_fixed_of_pow_eq_one
#print axioms Catalan.Kummer.root_ratio_independent
#print axioms Catalan.Kummer.root_ratio_aut_mul
#print axioms Catalan.Kummer.rootsOfUnityCoordinate
#print axioms Catalan.Kummer.rootsOfUnityCoordinate_symm_nat
#print axioms Catalan.A3.kummerZeta
#print axioms Catalan.A3.kummerZeta_spec
#print axioms Catalan.A3.kummerZetaM
#print axioms Catalan.A3.kummerZetaM_spec
#print axioms Catalan.A3.exists_unitRoot_M
#print axioms Catalan.A3.unitRoot
#print axioms Catalan.A3.unitRoot_pow
#print axioms Catalan.A3.unitRoot_ne_zero
#print axioms Catalan.A3.unitRoots_algHom_ext
#print axioms Catalan.A3.instAlgebraBsubMsub
#print axioms Catalan.A3.instModuleBsubMsub
#print axioms Catalan.A3.instScalarTowerFBsubMsub
#print axioms Catalan.A3.instScalarTowerBsubMsubOmega
#print axioms Catalan.A3.algebraMap_Bsub_Msub_coe
#print axioms Catalan.A3.finiteDimensional_Msub_over_B
#print axioms Catalan.A3.isGalois_Msub_over_B
#print axioms Catalan.A3.kummerValue
#print axioms Catalan.A3.kummerValue_val
#print axioms Catalan.A3.kummerValue_eq_one_iff
#print axioms Catalan.A3.kummerValue_mul_left
#print axioms Catalan.A3.kummerValue_mul_right
#print axioms Catalan.A3.kummerValue_one_right
#print axioms Catalan.A3.kummerValue_one_left
#print axioms Catalan.A3.kummerPairingHom
#print axioms Catalan.A3.kummerPairingHom_injective
#print axioms Catalan.A3.unit_qth_root_of_all_aut_fix_unitRoot
#print axioms Catalan.A3.kummerZetaUnitM
#print axioms Catalan.A3.kummerZetaUnitM_spec
#print axioms Catalan.A3.kummerCoordinate
#print axioms Catalan.A3.kummerQuotientValue
#print axioms Catalan.A3.kummerFunctional
#print axioms Catalan.A3.kummerFunctional_apply
#print axioms Catalan.A3.kummerFunctional_apply_eq_zero_iff
#print axioms Catalan.A3.kummerFunctional_one
#print axioms Catalan.A3.kummerFunctional_mul
#print axioms Catalan.A3.kummerDualHom
#print axioms Catalan.A3.kummerDualHom_injective
#print axioms Catalan.A3.kummerFunctional_right_nondegenerate
#print axioms Catalan.A3.kummerGalCommGroup
#print axioms Catalan.A3.kummerGal_pow_eq_one
#print axioms Catalan.A3.kummerGalModule
#print axioms Catalan.A3.kummerPairing
#print axioms Catalan.A3.kummerPairing_apply
#print axioms Catalan.A3.kummerPairing_isPerfect
#print axioms Catalan.A3.kummerDualEquiv
#print axioms Catalan.A3.kummerDualEquiv_apply
#print axioms Catalan.A3.exists_kummer_aut_of_functional

#check @Catalan.A3.isGalois_Bsub_rat
#print axioms Catalan.A3.isGalois_Bsub_rat

-- Actual Kummer covariance, M centralizers and unramified H witnesses.
#check @Catalan.Kummer.rootsOfUnityCoordinate_aut
#check @Catalan.Kummer.conjugateOver
#check @Catalan.Kummer.conjugateOver_apply
#check @Catalan.Kummer.conjugateOver_restrictScalars
#check @Catalan.Kummer.conjugateOver_eq_self_of_commute
#check @Catalan.Kummer.rootCoordinateScalar
#check @Catalan.Kummer.rootCoordinateScalar_one
#check @Catalan.Kummer.rootCoordinateScalar_trans
#check @Catalan.Kummer.isUnit_rootCoordinateScalar
#check @Catalan.A3.inertiaTrivial_iff_isUnramifiedAt
#check @Catalan.A3.restrictToF
#check @Catalan.A3.restrictToF_commutes
#check @Catalan.A3.restrictToF_inv
#check @Catalan.A3.restrictToF_unitAction
#check @Catalan.A3.conjugateKummer
#check @Catalan.A3.conjugateKummer_apply
#check @Catalan.A3.conjugateKummer_eq_self_of_commute
#check @Catalan.A3.isUnramifiedAtInfinitePlaces_of_odd_exponent
#check @Catalan.A3.cyclotomicScalar
#check @Catalan.A3.cyclotomicScalar_isUnit
#check @Catalan.A3.cyclotomicScalar_ne_zero
#check @Catalan.A3.kummerValue_conjugate
#check @Catalan.A3.kummerFunctional_conjugate_apply
#check @Catalan.A3.kummerFunctional_conjugate
#check @Catalan.A3.commuting_kummerFunctional_eigen
#check @Catalan.Kummer.rootCoordinateScalar_eq_one_iff
#check @Catalan.A3.unramifiedAbelianQ_finitePlaces
#check @Catalan.A3.unramifiedAbelianQ_infinitePlaces
#check @Catalan.A3.unramifiedAbelianQ_of_unramifiedAtFinitePlaces
#check @Catalan.A3.fixes_B_of_restrictToF_eq_one_of_zeta_fixed
#check @Catalan.A3.cyclotomicScalar_eq_one_iff
#check @Catalan.A3.abs_pow_eq_one_of_restrictToF_eq_one_of_scalar_eq_one
#check @Catalan.A3.exists_kummer_centralizer_element
#check @Catalan.A3.isGalois_Hsub
#check @Catalan.A3.Hsub_gal_pow_eq_one
#check @Catalan.A3.Hsub_gal_mul_comm

#print axioms Catalan.Kummer.rootsOfUnityCoordinate_aut
#print axioms Catalan.Kummer.conjugateOver
#print axioms Catalan.Kummer.conjugateOver_apply
#print axioms Catalan.Kummer.conjugateOver_restrictScalars
#print axioms Catalan.Kummer.conjugateOver_eq_self_of_commute
#print axioms Catalan.Kummer.rootCoordinateScalar
#print axioms Catalan.Kummer.rootCoordinateScalar_one
#print axioms Catalan.Kummer.rootCoordinateScalar_trans
#print axioms Catalan.Kummer.isUnit_rootCoordinateScalar
#print axioms Catalan.A3.inertiaTrivial_iff_isUnramifiedAt
#print axioms Catalan.A3.restrictToF
#print axioms Catalan.A3.restrictToF_commutes
#print axioms Catalan.A3.restrictToF_inv
#print axioms Catalan.A3.restrictToF_unitAction
#print axioms Catalan.A3.conjugateKummer
#print axioms Catalan.A3.conjugateKummer_apply
#print axioms Catalan.A3.conjugateKummer_eq_self_of_commute
#print axioms Catalan.A3.isUnramifiedAtInfinitePlaces_of_odd_exponent
#print axioms Catalan.A3.cyclotomicScalar
#print axioms Catalan.A3.cyclotomicScalar_isUnit
#print axioms Catalan.A3.cyclotomicScalar_ne_zero
#print axioms Catalan.A3.kummerValue_conjugate
#print axioms Catalan.A3.kummerFunctional_conjugate_apply
#print axioms Catalan.A3.kummerFunctional_conjugate
#print axioms Catalan.A3.commuting_kummerFunctional_eigen
#print axioms Catalan.Kummer.rootCoordinateScalar_eq_one_iff
#print axioms Catalan.A3.unramifiedAbelianQ_finitePlaces
#print axioms Catalan.A3.unramifiedAbelianQ_infinitePlaces
#print axioms Catalan.A3.unramifiedAbelianQ_of_unramifiedAtFinitePlaces
#print axioms Catalan.A3.fixes_B_of_restrictToF_eq_one_of_zeta_fixed
#print axioms Catalan.A3.cyclotomicScalar_eq_one_iff
#print axioms Catalan.A3.abs_pow_eq_one_of_restrictToF_eq_one_of_scalar_eq_one
#print axioms Catalan.A3.exists_kummer_centralizer_element
#print axioms Catalan.A3.isGalois_Hsub
#print axioms Catalan.A3.Hsub_gal_pow_eq_one
#print axioms Catalan.A3.Hsub_gal_mul_comm

-- ClassFieldTheory entrypoints used by the prime-selection argument.
#check @GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField
#print axioms GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField
#check @GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldFiniteDimensionalOverOriginal
#print axioms GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldFiniteDimensionalOverOriginal
#check @GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal
#print axioms GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal
#check @GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsAbelianGaloisOverOriginal
#print axioms GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsAbelianGaloisOverOriginal
#check @GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_finrank_over_original_eq_classNumber
#print axioms GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_finrank_over_original_eq_classNumber
#check @GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_isEverywhereUnramified
#print axioms GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField_isEverywhereUnramified
#check @GlobalClassFieldTheory.GlobalClassFields.arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal
#print axioms GlobalClassFieldTheory.GlobalClassFields.arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal
#check @GlobalClassFieldTheory.GlobalClassFields.arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal_idele
#print axioms GlobalClassFieldTheory.GlobalClassFields.arithmeticSmallHilbertClassFieldGaloisEquivClassGroupOverOriginal_idele
#check @GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldGaloisEquivClassGroup_finitePlacePrimeArtin
#print axioms GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldGaloisEquivClassGroup_finitePlacePrimeArtin
#check @GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
#print axioms GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
#check @GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_inv
#print axioms GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_inv
#check @GlobalClassFieldTheory.GlobalClassFields.orderOf_arithmeticFinitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
#print axioms GlobalClassFieldTheory.GlobalClassFields.orderOf_arithmeticFinitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
#check @GlobalClassFieldTheory.Cohomology.cyclic_prime_power_infinite_fullDecompositionPlaces
#print axioms GlobalClassFieldTheory.Cohomology.cyclic_prime_power_infinite_fullDecompositionPlaces

-- Actual H/T finiteness and compatible restrictions.
#check @Catalan.A3.instAlgebraHsubT
#print axioms Catalan.A3.instAlgebraHsubT
#check @Catalan.A3.instModuleHsubT
#print axioms Catalan.A3.instModuleHsubT
#check @Catalan.A3.instAlgebraMsubT
#print axioms Catalan.A3.instAlgebraMsubT
#check @Catalan.A3.instModuleMsubT
#print axioms Catalan.A3.instModuleMsubT
#check @Catalan.A3.instAlgebraBsubT
#print axioms Catalan.A3.instAlgebraBsubT
#check @Catalan.A3.instModuleBsubT
#print axioms Catalan.A3.instModuleBsubT
#check @Catalan.A3.instScalarTowerFHsubT
#print axioms Catalan.A3.instScalarTowerFHsubT
#check @Catalan.A3.instScalarTowerFMsubT
#print axioms Catalan.A3.instScalarTowerFMsubT
#check @Catalan.A3.instScalarTowerFBsubT
#print axioms Catalan.A3.instScalarTowerFBsubT
#check @Catalan.A3.instScalarTowerBsubMsubT
#print axioms Catalan.A3.instScalarTowerBsubMsubT
#check @Catalan.A3.instScalarTowerHsubTOmega
#print axioms Catalan.A3.instScalarTowerHsubTOmega
#check @Catalan.A3.instScalarTowerMsubTOmega
#print axioms Catalan.A3.instScalarTowerMsubTOmega
#check @Catalan.A3.instScalarTowerBsubTOmega
#print axioms Catalan.A3.instScalarTowerBsubTOmega
#check @Catalan.A3.algebraMap_Hsub_T_coe
#print axioms Catalan.A3.algebraMap_Hsub_T_coe
#check @Catalan.A3.algebraMap_Msub_T_coe
#print axioms Catalan.A3.algebraMap_Msub_T_coe
#check @Catalan.A3.algebraMap_Bsub_T_coe
#print axioms Catalan.A3.algebraMap_Bsub_T_coe
#check @Catalan.A3.isGalois_Tsub_over_F
#print axioms Catalan.A3.isGalois_Tsub_over_F
#check @Catalan.A3.isGalois_Tsub_over_B
#print axioms Catalan.A3.isGalois_Tsub_over_B
#check @Catalan.FieldTower.sup_algHom_ext
#print axioms Catalan.FieldTower.sup_algHom_ext
#check @Catalan.A3.inertiaTrivial_of_restrictions
#print axioms Catalan.A3.inertiaTrivial_of_restrictions
#check @Catalan.A3.finrank_dvd_classNumber_of_everywhereUnramified
#print axioms Catalan.A3.finrank_dvd_classNumber_of_everywhereUnramified
#check @Catalan.A3.unramifiedAbelianQ_finrank_dvd_classNumber
#print axioms Catalan.A3.unramifiedAbelianQ_finrank_dvd_classNumber
#check @Catalan.A3.unramifiedAbelianQ_sup
#print axioms Catalan.A3.unramifiedAbelianQ_sup
#check @Catalan.FieldTower.sSup_mem_of_bounded_finrank
#print axioms Catalan.FieldTower.sSup_mem_of_bounded_finrank
#check @Catalan.FieldTower.finiteDimensional_sSup_of_bounded_finrank
#print axioms Catalan.FieldTower.finiteDimensional_sSup_of_bounded_finrank
#check @Catalan.A3.T_gal_pow_eq_one
#print axioms Catalan.A3.T_gal_pow_eq_one
#check @Catalan.A3.T_gal_mul_comm
#print axioms Catalan.A3.T_gal_mul_comm
#check @Catalan.A3.exists_T_lift
#print axioms Catalan.A3.exists_T_lift
#check @Catalan.A3.unramifiedAbelianQ_bot
#print axioms Catalan.A3.unramifiedAbelianQ_bot
#check @Catalan.A3.unramifiedAbelianQ_Hsub
#print axioms Catalan.A3.unramifiedAbelianQ_Hsub
#check @Catalan.A3.finiteDimensional_Hsub
#print axioms Catalan.A3.finiteDimensional_Hsub
#check @Catalan.A3.numberField_Hsub
#print axioms Catalan.A3.numberField_Hsub
#check @Catalan.A3.Hsub_finrank_dvd_classNumber
#print axioms Catalan.A3.Hsub_finrank_dvd_classNumber
#check @Catalan.A3.finiteDimensional_T_over_F
#print axioms Catalan.A3.finiteDimensional_T_over_F
#check @Catalan.A3.finiteDimensional_T_over_B
#print axioms Catalan.A3.finiteDimensional_T_over_B
#check @Catalan.A3.numberField_T
#print axioms Catalan.A3.numberField_T

#check @Catalan.A3.exists_selector
#print axioms Catalan.A3.exists_selector

#check @Catalan.A3.Hsub_finrank_prime_pow
#print axioms Catalan.A3.Hsub_finrank_prime_pow
#check @Catalan.A3.Hsub_Bsub_linearDisjoint
#print axioms Catalan.A3.Hsub_Bsub_linearDisjoint
#check @Catalan.A3.Hsub_inf_Bsub
#print axioms Catalan.A3.Hsub_inf_Bsub

-- Actual conjugate witnesses and absolute H/T Galois.
#check @Catalan.A3.galEquivOfFieldEquivs
#print axioms Catalan.A3.galEquivOfFieldEquivs
#check @Catalan.A3.galEquivOfFieldEquivs_apply
#print axioms Catalan.A3.galEquivOfFieldEquivs_apply
#check @Catalan.A3.inertiaTrivial_of_equiv_equiv
#print axioms Catalan.A3.inertiaTrivial_of_equiv_equiv
#check @Catalan.A3.conjugateIntermediateField_exists
#print axioms Catalan.A3.conjugateIntermediateField_exists
#check @Catalan.A3.unramifiedAbelianQ_of_equiv_equiv
#print axioms Catalan.A3.unramifiedAbelianQ_of_equiv_equiv
#check @Catalan.A3.unramifiedAbelianQ_conjugate_exists
#print axioms Catalan.A3.unramifiedAbelianQ_conjugate_exists
#check @Catalan.A3.isGalois_Hsub_rat
#print axioms Catalan.A3.isGalois_Hsub_rat
#check @Catalan.A3.isGalois_T_rat
#print axioms Catalan.A3.isGalois_T_rat
#check @Catalan.GroupTheory.cyclic_subgroup_eq_zpowers_of_centralizer_exponent
#print axioms Catalan.GroupTheory.cyclic_subgroup_eq_zpowers_of_centralizer_exponent

-- Original DensityInput and actual arithmetic Frobenius.
#check @Catalan.A3.exists_arithmeticFrob_at_unramified_prime
#print axioms Catalan.A3.exists_arithmeticFrob_at_unramified_prime
#check @Catalan.A3.preservesPrime_iff_mem_stabilizer
#print axioms Catalan.A3.preservesPrime_iff_mem_stabilizer
#check @Catalan.A3.preservesPrime_iff_mem_zpowers_of_arithmeticFrob
#print axioms Catalan.A3.preservesPrime_iff_mem_zpowers_of_arithmeticFrob
#check @Catalan.A3.fixedField_fullDecomposition_infinite
#print axioms Catalan.A3.fixedField_fullDecomposition_infinite
#check @Catalan.A3.preservesPrime_of_mem_finitePlaceDecompositionGroup
#print axioms Catalan.A3.preservesPrime_of_mem_finitePlaceDecompositionGroup
#check @Catalan.A3.rational_natGenerator_below_mem
#print axioms Catalan.A3.rational_natGenerator_below_mem
#check @Catalan.A3.finite_places_above_natSet
#print axioms Catalan.A3.finite_places_above_natSet
#check @Catalan.A3.arithmeticFrob_nonzero_power_of_prime_centralizer
#print axioms Catalan.A3.arithmeticFrob_nonzero_power_of_prime_centralizer
#check @Catalan.A3.exists_unramified_preserved_prime
#print axioms Catalan.A3.exists_unramified_preserved_prime
#check @Catalan.A3.exists_arithmeticFrob_nonzero_power
#print axioms Catalan.A3.exists_arithmeticFrob_nonzero_power
#check @Catalan.densityInput
#print axioms Catalan.densityInput

-- Runge finite coefficients and actual class-group quotient of H.
#check @Catalan.Runge.D
#print axioms Catalan.Runge.D
#check @Catalan.Runge.binomRat
#print axioms Catalan.Runge.binomRat
#check @Catalan.Runge.errorBound
#print axioms Catalan.Runge.errorBound
#check @Catalan.Runge.EvenCoefficients
#print axioms Catalan.Runge.EvenCoefficients
#check @Catalan.Runge.rungeCoeff
#print axioms Catalan.Runge.rungeCoeff
#check @Catalan.Runge.rungeApprox
#print axioms Catalan.Runge.rungeApprox
#check @Catalan.Runge.binomRat_nat_div_eq_casselsCoeff
#print axioms Catalan.Runge.binomRat_nat_div_eq_casselsCoeff
#check @Catalan.Runge.D_sum_le
#print axioms Catalan.Runge.D_sum_le
#check @Catalan.Runge.runge_coeff_integral
#print axioms Catalan.Runge.runge_coeff_integral
#check @Catalan.Runge.D_bounds
#print axioms Catalan.Runge.D_bounds
#check @Catalan.Runge.runge_numeric
#print axioms Catalan.Runge.runge_numeric
#check @Catalan.Runge.error_lt_one
#print axioms Catalan.Runge.error_lt_one
#check @Catalan.Runge.runge_coeff_residue
#print axioms Catalan.Runge.runge_coeff_residue
#check @Catalan.Runge.small_conjugates_zero
#print axioms Catalan.Runge.small_conjugates_zero
#check @Catalan.A3.classGroupArtinOfEverywhereUnramified
#print axioms Catalan.A3.classGroupArtinOfEverywhereUnramified
#check @Catalan.A3.classGroupArtinOfEverywhereUnramified_surjective
#print axioms Catalan.A3.classGroupArtinOfEverywhereUnramified_surjective
#check @Catalan.A3.classGroupToHGal
#print axioms Catalan.A3.classGroupToHGal
#check @Catalan.A3.classGroupToHGal_surjective
#print axioms Catalan.A3.classGroupToHGal_surjective
#check @Catalan.A3.classGroupToHGal_pow
#print axioms Catalan.A3.classGroupToHGal_pow
#check @Catalan.A3.classGroupModQToHGal
#print axioms Catalan.A3.classGroupModQToHGal
#check @Catalan.A3.classGroupModQToHGal_mk
#print axioms Catalan.A3.classGroupModQToHGal_mk
#check @Catalan.A3.classGroupModQToHGal_surjective
#print axioms Catalan.A3.classGroupModQToHGal_surjective
#check @Catalan.FieldTower.exists_intermediateField_of_galois_power_quotient
#print axioms Catalan.FieldTower.exists_intermediateField_of_galois_power_quotient
#check @Catalan.A3.exists_unramifiedAbelianQ_model
#print axioms Catalan.A3.exists_unramifiedAbelianQ_model
#check @Catalan.A3.exists_unramifiedAbelianQ_classQuotient_degree
#print axioms Catalan.A3.exists_unramifiedAbelianQ_classQuotient_degree
#check @Catalan.A3.classGroupModQToHGal_injective
#print axioms Catalan.A3.classGroupModQToHGal_injective
#check @Catalan.A3.classGroupModQEquivHGal
#print axioms Catalan.A3.classGroupModQEquivHGal
#check @Catalan.A3.classGroupModQEquivHGal_mk
#print axioms Catalan.A3.classGroupModQEquivHGal_mk
#check @Catalan.A3.classGroupToHGal_eq_one_iff
#print axioms Catalan.A3.classGroupToHGal_eq_one_iff
#check @Catalan.A3.classGroupToHGal_ker
#print axioms Catalan.A3.classGroupToHGal_ker

#check @Catalan.Runge.binomRat_eq_choose
#print axioms Catalan.Runge.binomRat_eq_choose
#check @Catalan.Runge.hasSum_binomRat_mul_pow
#print axioms Catalan.Runge.hasSum_binomRat_mul_pow

#check @Catalan.A3.classGroupArtinOfEverywhereUnramified_idele
#print axioms Catalan.A3.classGroupArtinOfEverywhereUnramified_idele

-- Full Runge analytic estimate and normalized coefficient obstruction.
#check @Catalan.Runge.sum_bounded_eq_piAntidiag
#print axioms Catalan.Runge.sum_bounded_eq_piAntidiag
#check @Catalan.Runge.binomialProductCoeff
#print axioms Catalan.Runge.binomialProductCoeff
#check @Catalan.Runge.map_rungeCoeff_eq_binomialProductCoeff
#print axioms Catalan.Runge.map_rungeCoeff_eq_binomialProductCoeff
#check @Catalan.Runge.field_pow_injective
#print axioms Catalan.Runge.field_pow_injective
#check @Catalan.Runge.iota_upow_eq_self_of_even
#print axioms Catalan.Runge.iota_upow_eq_self_of_even
#check @Catalan.Runge.root_im_eq_zero_of_even
#print axioms Catalan.Runge.root_im_eq_zero_of_even
#check @Catalan.Runge.binomialProduct_positive_real
#print axioms Catalan.Runge.binomialProduct_positive_real
#check @Catalan.Runge.norm_binomialProductCoeff_le_multichoose
#print axioms Catalan.Runge.norm_binomialProductCoeff_le_multichoose
#check @Catalan.Runge.hasSum_binomialProductCoeff
#print axioms Catalan.Runge.hasSum_binomialProductCoeff
#check @Catalan.Runge.scale_tail_eq_errorBound
#print axioms Catalan.Runge.scale_tail_eq_errorBound
#check @Catalan.Runge.map_rungeApprox
#print axioms Catalan.Runge.map_rungeApprox
#check @Catalan.Runge.rungeFunction
#print axioms Catalan.Runge.rungeFunction
#check @Catalan.Runge.norm_embedding_zeta_conj
#print axioms Catalan.Runge.norm_embedding_zeta_conj
#check @Catalan.Runge.rungeFunction_positive_real
#print axioms Catalan.Runge.rungeFunction_positive_real
#check @Catalan.Runge.rungeFunction_pow
#print axioms Catalan.Runge.rungeFunction_pow
#check @Catalan.Runge.root_pow_eq_scaled_rungeFunction_pow
#print axioms Catalan.Runge.root_pow_eq_scaled_rungeFunction_pow
#check @Catalan.Runge.root_eq_scaled_rungeFunction
#print axioms Catalan.Runge.root_eq_scaled_rungeFunction
#check @Catalan.Runge.multichoose_tail_le
#print axioms Catalan.Runge.multichoose_tail_le
#check @Catalan.Runge.norm_series_tail_le
#print axioms Catalan.Runge.norm_series_tail_le
#check @Catalan.Runge.rungeCoeff_norm_le
#print axioms Catalan.Runge.rungeCoeff_norm_le
#check @Catalan.Runge.hasSum_rungeCoeff
#print axioms Catalan.Runge.hasSum_rungeCoeff
#check @Catalan.Runge.runge_estimate
#print axioms Catalan.Runge.runge_estimate
#check @Catalan.Runge.cyclotomic_prime_dvd_of_dvd_pow
#print axioms Catalan.Runge.cyclotomic_prime_dvd_of_dvd_pow
#check @Catalan.Runge.isReduced_cyclotomic_quotient
#print axioms Catalan.Runge.isReduced_cyclotomic_quotient
#check @Catalan.Runge.dvd_coeff_of_dvd_zeta_sum
#print axioms Catalan.Runge.dvd_coeff_of_dvd_zeta_sum
#check @Catalan.Runge.D_strictMono
#print axioms Catalan.Runge.D_strictMono
#check @Catalan.Runge.integral_rungeApprox
#print axioms Catalan.Runge.integral_rungeApprox
#check @Catalan.Runge.scaled_root_eq_rungeApprox
#print axioms Catalan.Runge.scaled_root_eq_rungeApprox
#check @Catalan.Runge.reduceFull
#print axioms Catalan.Runge.reduceFull
#check @Catalan.Runge.reduceFull_eq_zero_iff
#print axioms Catalan.Runge.reduceFull_eq_zero_iff
#check @Catalan.Runge.integral_leadingCoeff_of_scaled_root
#print axioms Catalan.Runge.integral_leadingCoeff_of_scaled_root
#check @Catalan.Runge.runge_normalized
#print axioms Catalan.Runge.runge_normalized

#check @Catalan.Runge.cassels_growth
#print axioms Catalan.Runge.cassels_growth
#check @Catalan.Runge.reduceFull_eq_iff_exists_nsmul
#print axioms Catalan.Runge.reduceFull_eq_iff_exists_nsmul
#check @Catalan.Runge.upow_nsmul
#print axioms Catalan.Runge.upow_nsmul
#check @Catalan.Runge.root_of_reduceFull_eq
#print axioms Catalan.Runge.root_of_reduceFull_eq
#check @Catalan.Runge.root_of_reduceFull_eq_or_neg
#print axioms Catalan.Runge.root_of_reduceFull_eq_or_neg
#check @Catalan.Runge.exists_bounded_even_lift
#print axioms Catalan.Runge.exists_bounded_even_lift
#check @Catalan.Runge.even_weight_of_mem_plusAugIdeal
#print axioms Catalan.Runge.even_weight_of_mem_plusAugIdeal
#check @Catalan.Runge.normalize_full_relation
#print axioms Catalan.Runge.normalize_full_relation
#check @Catalan.Runge.runge_full_injective
#print axioms Catalan.Runge.runge_full_injective
#check @Catalan.Runge.runge_full_injective_of_solution
#print axioms Catalan.Runge.runge_full_injective_of_solution
#check @Catalan.Runge.reduceFull_surjective
#print axioms Catalan.Runge.reduceFull_surjective
#check @Catalan.Runge.runge_of_mem_plusAugIdeal
#print axioms Catalan.Runge.runge_of_mem_plusAugIdeal
#check @Catalan.Runge.reduce_mihIdeal_inf_plusAug_eq_bot
#print axioms Catalan.Runge.reduce_mihIdeal_inf_plusAug_eq_bot
#check @Catalan.Runge.reduce_mihIdeal_inf_plusAug_eq_bot_of_solution
#print axioms Catalan.Runge.reduce_mihIdeal_inf_plusAug_eq_bot_of_solution
#check @Catalan.A3.exists_cyclic_kummer_centralizer_element
#print axioms Catalan.A3.exists_cyclic_kummer_centralizer_element

#check @Catalan.A3.TGalCommGroup
#print axioms Catalan.A3.TGalCommGroup
#check @Catalan.A3.HGalCommGroup
#print axioms Catalan.A3.HGalCommGroup
#check @Catalan.A3.TGalModule
#print axioms Catalan.A3.TGalModule
#check @Catalan.A3.HGalModule
#print axioms Catalan.A3.HGalModule
#check @Catalan.A3.restrictTToM
#print axioms Catalan.A3.restrictTToM
#check @Catalan.A3.restrictTToH
#print axioms Catalan.A3.restrictTToH
#check @Catalan.A3.restrictTToM_commutes
#print axioms Catalan.A3.restrictTToM_commutes
#check @Catalan.A3.restrictTToH_commutes
#print axioms Catalan.A3.restrictTToH_commutes
#check @Catalan.A3.TToMLinear
#print axioms Catalan.A3.TToMLinear
#check @Catalan.A3.TToHLinear
#print axioms Catalan.A3.TToHLinear
#check @Catalan.A3.TToMLinear_surjective
#print axioms Catalan.A3.TToMLinear_surjective
#check @Catalan.A3.selector_of_T_lift
#print axioms Catalan.A3.selector_of_T_lift
#check @Catalan.A3.selector_conjugate
#print axioms Catalan.A3.selector_conjugate
#check @Catalan.A3.exists_T_lift_H
#print axioms Catalan.A3.exists_T_lift_H
#check @Catalan.A3.kummer_conjugates_span
#print axioms Catalan.A3.kummer_conjugates_span
#check @Catalan.A3.restrictAbsoluteTToM
#print axioms Catalan.A3.restrictAbsoluteTToM
#check @Catalan.A3.restrictAbsoluteTToM_commutes
#print axioms Catalan.A3.restrictAbsoluteTToM_commutes
#check @Catalan.A3.restrictAbsoluteTToM_surjective
#print axioms Catalan.A3.restrictAbsoluteTToM_surjective
#check @Catalan.A3.conjugateT
#print axioms Catalan.A3.conjugateT
#check @Catalan.A3.conjugateT_apply
#print axioms Catalan.A3.conjugateT_apply
#check @Catalan.A3.conjugateT_restrictScalars
#print axioms Catalan.A3.conjugateT_restrictScalars
#check @Catalan.A3.restrictTToM_conjugate
#print axioms Catalan.A3.restrictTToM_conjugate
#check @Catalan.A3.selector_conjugateT
#print axioms Catalan.A3.selector_conjugateT
#check @Catalan.A3.conjugateT_inv_cancel
#print axioms Catalan.A3.conjugateT_inv_cancel
#check @Catalan.A3.conjugateKummer_inv_cancel
#print axioms Catalan.A3.conjugateKummer_inv_cancel
#check @Catalan.A3.TToHLinear_surjective
#print axioms Catalan.A3.TToHLinear_surjective
#check @Catalan.A3.selectorVectors
#print axioms Catalan.A3.selectorVectors
#check @Catalan.A3.selectors_span
#print axioms Catalan.A3.selectors_span
#check @Catalan.A3.classGroupModQLinearEquivHGal
#print axioms Catalan.A3.classGroupModQLinearEquivHGal
#check @Catalan.A3.classGroupModQLinearEquivHGal_powerClass
#print axioms Catalan.A3.classGroupModQLinearEquivHGal_powerClass
#check @Catalan.A3.selectors_H_span
#print axioms Catalan.A3.selectors_H_span
#check @Catalan.A3.selectorClassVectors
#print axioms Catalan.A3.selectorClassVectors
#check @Catalan.A3.selectorClassVectors_span
#print axioms Catalan.A3.selectorClassVectors_span

#check @Catalan.A3.classGroupArtinOfEverywhereUnramified_prime
#print axioms Catalan.A3.classGroupArtinOfEverywhereUnramified_prime
#check @Catalan.A3.chosenFinitePlace_unramified_of_finitePlaces
#print axioms Catalan.A3.chosenFinitePlace_unramified_of_finitePlaces
#check @Catalan.A3.primeArtin_zpowers_of_unramified
#print axioms Catalan.A3.primeArtin_zpowers_of_unramified
#check @Catalan.A3.preservesPrime_iff_mem_zpowers_primeArtin
#print axioms Catalan.A3.preservesPrime_iff_mem_zpowers_primeArtin
#check @Catalan.A3.card_quotient_under_of_arithmeticFrob_fixes
#print axioms Catalan.A3.card_quotient_under_of_arithmeticFrob_fixes
#check @Catalan.A3.relativeFrob_congruence_of_rationalFrob_compatible
#print axioms Catalan.A3.relativeFrob_congruence_of_rationalFrob_compatible
#check @Catalan.A3.integerAutSMulCommClass
#print axioms Catalan.A3.integerAutSMulCommClass
#check @Catalan.A3.preservesPrime_iff_mem_zpowers_of_nativeFrob
#print axioms Catalan.A3.preservesPrime_iff_mem_zpowers_of_nativeFrob
#check @Catalan.A3.zpowers_nativeFrob_eq_zpowers_primeArtin
#print axioms Catalan.A3.zpowers_nativeFrob_eq_zpowers_primeArtin
#check @Catalan.A3.classGroupToHGal_prime_zpowers_of_rationalFrob
#print axioms Catalan.A3.classGroupToHGal_prime_zpowers_of_rationalFrob
#check @Catalan.A3.exists_H_prime_class_of_rationalFrob
#print axioms Catalan.A3.exists_H_prime_class_of_rationalFrob
#check @Catalan.A3.exists_prime_class_of_selector_avoiding
#print axioms Catalan.A3.exists_prime_class_of_selector_avoiding

#check @Catalan.A3.exists_residueHom_to_zmod
#print axioms Catalan.A3.exists_residueHom_to_zmod
#check @Catalan.A3.exists_cyclic_selector_family
#print axioms Catalan.A3.exists_cyclic_selector_family
#check @Catalan.A3.unit_class_eq_zero_of_cyclic_functional
#print axioms Catalan.A3.unit_class_eq_zero_of_cyclic_functional
#check @Catalan.A3.unit_class_eq_zero_of_conjugate_cyclic_functional
#print axioms Catalan.A3.unit_class_eq_zero_of_conjugate_cyclic_functional
#check @Catalan.Kummer.exists_integralUnit_of_field_root
#print axioms Catalan.Kummer.exists_integralUnit_of_field_root
#check @Catalan.Kummer.integral_root_fixed_of_residue_power
#print axioms Catalan.Kummer.integral_root_fixed_of_residue_power
#check @Catalan.Kummer.residue_power_map_tower
#print axioms Catalan.Kummer.residue_power_map_tower
#check @Catalan.Kummer.residue_power_iff_of_surjective
#print axioms Catalan.Kummer.residue_power_iff_of_surjective
#check @Catalan.A3.cyclicPrimeClasses
#print axioms Catalan.A3.cyclicPrimeClasses
#check @Catalan.A3.exists_cyclic_prime_class_generators
#print axioms Catalan.A3.exists_cyclic_prime_class_generators
#check @Catalan.A3.kummerFunctional_zero_of_residue_power
#print axioms Catalan.A3.kummerFunctional_zero_of_residue_power
#check @Catalan.Kummer.prime_dvd_residue_card_sub_one
#print axioms Catalan.Kummer.prime_dvd_residue_card_sub_one
#check @Catalan.A3.unit_qth_power_of_cyclic_prime_residues
#print axioms Catalan.A3.unit_qth_power_of_cyclic_prime_residues
#check @Catalan.A3.q_dvd_ell_sub_one_of_B_frobenius
#print axioms Catalan.A3.q_dvd_ell_sub_one_of_B_frobenius
#check @Catalan.A3.separatingPrimeClasses
#print axioms Catalan.A3.separatingPrimeClasses
#check @Catalan.A3.separatingPrimeClasses_span
#print axioms Catalan.A3.separatingPrimeClasses_span

#check @Catalan.A3.real_prime_congruence
#print axioms Catalan.A3.real_prime_congruence
#check @Catalan.A3.exists_residue_power_coordinate
#print axioms Catalan.A3.exists_residue_power_coordinate
#check @Catalan.Residue.sumZero
#print axioms Catalan.Residue.sumZero
#check @Catalan.Residue.inverseOrbitMap
#print axioms Catalan.Residue.inverseOrbitMap
#check @Catalan.Residue.mem_sumZero
#print axioms Catalan.Residue.mem_sumZero
#check @Catalan.Residue.inverseOrbitMap_apply
#print axioms Catalan.Residue.inverseOrbitMap_apply
#check @Catalan.Residue.inverseOrbitMap_equivariant
#print axioms Catalan.Residue.inverseOrbitMap_equivariant
#check @Catalan.Residue.inverseOrbitMap_range_eq_sumZero
#print axioms Catalan.Residue.inverseOrbitMap_range_eq_sumZero
#check @Catalan.A3.F_unit_finrank_add_one
#print axioms Catalan.A3.F_unit_finrank_add_one
#check @Catalan.A3.F_unit_norm_zero
#print axioms Catalan.A3.F_unit_norm_zero
#check @Catalan.A3.unitResidueFunctional
#print axioms Catalan.A3.unitResidueFunctional
#check @Catalan.A3.unitResidueCoordinates
#print axioms Catalan.A3.unitResidueCoordinates
#check @Catalan.A3.unitResidueCoordinates_powerClass
#print axioms Catalan.A3.unitResidueCoordinates_powerClass
#check @Catalan.A3.unitResidueCoordinates_equivariant
#print axioms Catalan.A3.unitResidueCoordinates_equivariant
#check @Catalan.A3.unitResidueCoordinates_injective
#print axioms Catalan.A3.unitResidueCoordinates_injective
#check @Catalan.A3.unitResidueCoordinates_range
#print axioms Catalan.A3.unitResidueCoordinates_range
#check @Catalan.A3.exists_unit_augmentation_coordinates
#print axioms Catalan.A3.exists_unit_augmentation_coordinates
#check @Catalan.A3.augmentationPrimeClasses
#print axioms Catalan.A3.augmentationPrimeClasses
#check @Catalan.A3.augmentationPrimeClasses_span
#print axioms Catalan.A3.augmentationPrimeClasses_span
#check @Catalan.Thaine.hilbert90_cyclic
#print axioms Catalan.Thaine.hilbert90_cyclic

#check @Catalan.UnitModule.integralUnitPow
#print axioms Catalan.UnitModule.integralUnitPow
#check @Catalan.UnitModule.map_integralUnitPow
#print axioms Catalan.UnitModule.map_integralUnitPow
#check @Catalan.UnitModule.integralUnitPow_zero
#print axioms Catalan.UnitModule.integralUnitPow_zero
#check @Catalan.UnitModule.integralUnitPow_add
#print axioms Catalan.UnitModule.integralUnitPow_add
#check @Catalan.UnitModule.integralUnitPow_single
#print axioms Catalan.UnitModule.integralUnitPow_single
#check @Catalan.UnitModule.powerClass_integralUnitPow
#print axioms Catalan.UnitModule.powerClass_integralUnitPow
#check @Catalan.Residue.coordinate_zpow
#print axioms Catalan.Residue.coordinate_zpow
#check @Catalan.Residue.coordinate_eq_iff_power_error
#print axioms Catalan.Residue.coordinate_eq_iff_power_error
#check @Catalan.Residue.inverseOrbitMap_algebra_action
#print axioms Catalan.Residue.inverseOrbitMap_algebra_action
#check @Catalan.Residue.inverseOrbitMap_canonical_action
#print axioms Catalan.Residue.inverseOrbitMap_canonical_action
#check @Catalan.Thaine.real_model_transport
#print axioms Catalan.Thaine.real_model_transport
#check @Catalan.Thaine.auxiliaryRoot
#print axioms Catalan.Thaine.auxiliaryRoot
#check @Catalan.Thaine.auxiliary_cyclic_generator
#print axioms Catalan.Thaine.auxiliary_cyclic_generator
#check @Catalan.A3.unitResidueCoordinates_integralUnitPow
#print axioms Catalan.A3.unitResidueCoordinates_integralUnitPow
#check @Catalan.A3.unit_residue_exponents_of_canonical
#print axioms Catalan.A3.unit_residue_exponents_of_canonical
#check @Catalan.A3.exists_unit_residue_exponent_generator
#print axioms Catalan.A3.exists_unit_residue_exponent_generator
#check @Catalan.Thaine.auxiliary_integral_hilbert90
#print axioms Catalan.Thaine.auxiliary_integral_hilbert90
#check @Catalan.Thaine.primitiveRoot_sub_one_isUnit
#print axioms Catalan.Thaine.primitiveRoot_sub_one_isUnit
#check @Catalan.Thaine.primitive_roots_difference_isUnit
#print axioms Catalan.Thaine.primitive_roots_difference_isUnit
#check @Catalan.Thaine.exists_mixed_epsilon_unit
#print axioms Catalan.Thaine.exists_mixed_epsilon_unit

#check @Catalan.Thaine.normalizedHalf
#print axioms Catalan.Thaine.normalizedHalf
#check @Catalan.Thaine.normalizedHalf_congruence
#print axioms Catalan.Thaine.normalizedHalf_congruence
#check @Catalan.Thaine.normalizedHalf_root
#print axioms Catalan.Thaine.normalizedHalf_root
#check @Catalan.Thaine.normalizedEpsilon
#print axioms Catalan.Thaine.normalizedEpsilon
#check @Catalan.Thaine.normalizedCircularValue
#print axioms Catalan.Thaine.normalizedCircularValue
#check @Catalan.Thaine.normalizedCircularValue_eq
#print axioms Catalan.Thaine.normalizedCircularValue_eq
#check @Catalan.Thaine.exists_normalized_epsilon_unit
#print axioms Catalan.Thaine.exists_normalized_epsilon_unit
#check @Catalan.Thaine.norm_cyclotomic_sub
#print axioms Catalan.Thaine.norm_cyclotomic_sub
#check @Catalan.Thaine.norm_mixed_epsilon
#print axioms Catalan.Thaine.norm_mixed_epsilon
#check @Catalan.Thaine.mixedExtension
#print axioms Catalan.Thaine.mixedExtension
#check @Catalan.Thaine.mixedPRoot
#print axioms Catalan.Thaine.mixedPRoot
#check @Catalan.Thaine.mixedEllRoot
#print axioms Catalan.Thaine.mixedEllRoot
#check @Catalan.Thaine.mixedExtensionFiniteDimensional
#print axioms Catalan.Thaine.mixedExtensionFiniteDimensional
#check @Catalan.Thaine.mixedExtensionNumberField
#print axioms Catalan.Thaine.mixedExtensionNumberField
#check @Catalan.Thaine.mixedExtension_isCyclotomic
#print axioms Catalan.Thaine.mixedExtension_isCyclotomic
#check @Catalan.Thaine.mixedExtension_finrank
#print axioms Catalan.Thaine.mixedExtension_finrank
#check @Catalan.Thaine.exists_mixed_involution
#print axioms Catalan.Thaine.exists_mixed_involution
#check @Catalan.Thaine.exists_integral_unit_of_field_image
#print axioms Catalan.Thaine.exists_integral_unit_of_field_image
#check @Catalan.Thaine.epsilon_inverse_root
#print axioms Catalan.Thaine.epsilon_inverse_root
#check @Catalan.Thaine.epsilon_pair_inverse_root
#print axioms Catalan.Thaine.epsilon_pair_inverse_root
#check @Catalan.Thaine.epsilon_norm_factor_eq_one
#print axioms Catalan.Thaine.epsilon_norm_factor_eq_one
#check @Catalan.Thaine.normalizedPair
#print axioms Catalan.Thaine.normalizedPair
#check @Catalan.Thaine.normalizedEpsilon_map
#print axioms Catalan.Thaine.normalizedEpsilon_map
#check @Catalan.Thaine.normalizedPair_map
#print axioms Catalan.Thaine.normalizedPair_map
#check @Catalan.Thaine.normalizedPair_inverse_root
#print axioms Catalan.Thaine.normalizedPair_inverse_root
#check @Catalan.Thaine.normalizedCircularValue_inverse_root
#print axioms Catalan.Thaine.normalizedCircularValue_inverse_root
#check @Catalan.Thaine.normalizedPair_fixed
#print axioms Catalan.Thaine.normalizedPair_fixed
#check @Catalan.Thaine.exists_normalized_pair_unit
#print axioms Catalan.Thaine.exists_normalized_pair_unit
#check @Catalan.Thaine.exists_auxiliary_normalized_unit
#print axioms Catalan.Thaine.exists_auxiliary_normalized_unit
#check @Catalan.Thaine.exists_normalized_circular_unit
#print axioms Catalan.Thaine.exists_normalized_circular_unit
#check @Catalan.Thaine.mixedPrimeField
#print axioms Catalan.Thaine.mixedPrimeField
#check @Catalan.Thaine.mixedPrimeGenerator
#print axioms Catalan.Thaine.mixedPrimeGenerator
#check @Catalan.Thaine.mixedPrimeField_finrank
#print axioms Catalan.Thaine.mixedPrimeField_finrank
#check @Catalan.Thaine.mixedExtension_overPrime_isCyclotomic
#print axioms Catalan.Thaine.mixedExtension_overPrime_isCyclotomic
#check @Catalan.Thaine.mixedExtension_overPrime_finrank
#print axioms Catalan.Thaine.mixedExtension_overPrime_finrank
#check @Catalan.Thaine.mixedPrime_norm_compat
#print axioms Catalan.Thaine.mixedPrime_norm_compat
#check @Catalan.Thaine.normalizedEpsilon_norm_one
#print axioms Catalan.Thaine.normalizedEpsilon_norm_one
#check @Catalan.Thaine.normalizedPair_norm_one
#print axioms Catalan.Thaine.normalizedPair_norm_one
#check @Catalan.Thaine.normalized_epsilon_residue
#print axioms Catalan.Thaine.normalized_epsilon_residue
#check @Catalan.Thaine.normalized_pair_residue
#print axioms Catalan.Thaine.normalized_pair_residue
#check @Catalan.Thaine.auxiliary_normalized_unit_norm_one
#print axioms Catalan.Thaine.auxiliary_normalized_unit_norm_one
#check @Catalan.Thaine.exists_auxiliary_norm_one_unit
#print axioms Catalan.Thaine.exists_auxiliary_norm_one_unit
#check @Catalan.Thaine.exists_real_circular_unit
#print axioms Catalan.Thaine.exists_real_circular_unit
#check @Catalan.Thaine.auxiliary_normalized_unit_residue
#print axioms Catalan.Thaine.auxiliary_normalized_unit_residue
#check @Catalan.Thaine.exists_auxiliary_unit_for_generator
#print axioms Catalan.Thaine.exists_auxiliary_unit_for_generator
#check @Catalan.Thaine.realCircularUnits
#print axioms Catalan.Thaine.realCircularUnits
#check @Catalan.Thaine.exists_real_circular_generator
#print axioms Catalan.Thaine.exists_real_circular_generator
#check @Catalan.Thaine.auxiliary_norm_unit
#print axioms Catalan.Thaine.auxiliary_norm_unit
#check @Catalan.Thaine.exists_circular_hilbert90_data
#print axioms Catalan.Thaine.exists_circular_hilbert90_data

#check @Catalan.Thaine.isCyclotomicExtension_Bsub_self_rat
#print axioms Catalan.Thaine.isCyclotomicExtension_Bsub_self_rat
#check @Catalan.Thaine.real_prime_ramification_one
#print axioms Catalan.Thaine.real_prime_ramification_one
#check @Catalan.Thaine.prime_root_ramification_uniformizer
#print axioms Catalan.Thaine.prime_root_ramification_uniformizer
#check @Catalan.Thaine.principal_ideal_fixed_of_integral_coboundary
#print axioms Catalan.Thaine.principal_ideal_fixed_of_integral_coboundary
#check @Catalan.Thaine.principal_ideal_fixed_of_cyclic_coboundary
#print axioms Catalan.Thaine.principal_ideal_fixed_of_cyclic_coboundary
#check @Catalan.Thaine.principal_multiplicity_constant_of_cyclic_coboundary
#print axioms Catalan.Thaine.principal_multiplicity_constant_of_cyclic_coboundary
#check @Catalan.Thaine.cyclotomic_inertia_trivial_away
#print axioms Catalan.Thaine.cyclotomic_inertia_trivial_away
#check @Catalan.Thaine.cyclotomic_isUnramifiedAt_away
#print axioms Catalan.Thaine.cyclotomic_isUnramifiedAt_away
#check @Catalan.Thaine.inertia_and_unique_prime_of_ramification_degree
#print axioms Catalan.Thaine.inertia_and_unique_prime_of_ramification_degree
#check @Catalan.Thaine.residue_card_eq_of_inertia_one
#print axioms Catalan.Thaine.residue_card_eq_of_inertia_one
#check @Catalan.Thaine.auxiliaryIntegerRoot
#print axioms Catalan.Thaine.auxiliaryIntegerRoot
#check @Catalan.Thaine.auxiliaryUniformizer
#print axioms Catalan.Thaine.auxiliaryUniformizer
#check @Catalan.Thaine.auxiliaryUniformizerRatio
#print axioms Catalan.Thaine.auxiliaryUniformizerRatio
#check @Catalan.Thaine.auxiliaryUniformizer_ne_zero
#print axioms Catalan.Thaine.auxiliaryUniformizer_ne_zero
#check @Catalan.Thaine.auxiliaryUniformizer_action
#print axioms Catalan.Thaine.auxiliaryUniformizer_action
#check @Catalan.Thaine.auxiliaryUniformizerRatio_residue
#print axioms Catalan.Thaine.auxiliaryUniformizerRatio_residue
#check @Catalan.Thaine.all_integral_automorphisms_trivial_mod_prime
#print axioms Catalan.Thaine.all_integral_automorphisms_trivial_mod_prime
#check @Catalan.Thaine.residue_coboundary_of_uniformizer_decomposition
#print axioms Catalan.Thaine.residue_coboundary_of_uniformizer_decomposition
#check @Catalan.Thaine.auxiliary_unramified_away
#print axioms Catalan.Thaine.auxiliary_unramified_away
#check @Catalan.Thaine.auxiliary_prime_ramification
#print axioms Catalan.Thaine.auxiliary_prime_ramification
#check @Catalan.Thaine.auxiliary_prime_fiber
#print axioms Catalan.Thaine.auxiliary_prime_fiber
#check @Catalan.Thaine.exists_auxiliary_prime_of_norm_eq
#print axioms Catalan.Thaine.exists_auxiliary_prime_of_norm_eq
#check @Catalan.Thaine.exists_residue_extension_of_inertia_one
#print axioms Catalan.Thaine.exists_residue_extension_of_inertia_one
#check @Catalan.Thaine.exists_auxiliary_residue_hom
#print axioms Catalan.Thaine.exists_auxiliary_residue_hom

#check @Catalan.Thaine.exists_localized_action_and_residue
#print axioms Catalan.Thaine.exists_localized_action_and_residue
#check @Catalan.Thaine.heightOneLocalizationDvr
#print axioms Catalan.Thaine.heightOneLocalizationDvr
#check @Catalan.Thaine.local_addVal_eq_emultiplicity
#print axioms Catalan.Thaine.local_addVal_eq_emultiplicity
#check @Catalan.Thaine.irreducible_of_addVal_one
#print axioms Catalan.Thaine.irreducible_of_addVal_one
#check @Catalan.Thaine.exists_unit_decomposition_of_addVal_one
#print axioms Catalan.Thaine.exists_unit_decomposition_of_addVal_one
#check @Catalan.Thaine.residue_coboundary_eq_pow_multiplicity
#print axioms Catalan.Thaine.residue_coboundary_eq_pow_multiplicity
#check @Catalan.Thaine.exists_auxiliary_residue_hom_with_multiplicity
#print axioms Catalan.Thaine.exists_auxiliary_residue_hom_with_multiplicity
#check @Catalan.Thaine.exists_circular_invariant_principal_data
#print axioms Catalan.Thaine.exists_circular_invariant_principal_data

#check @Catalan.Thaine.multiplicity_relNorm_eq_finsum
#print axioms Catalan.Thaine.multiplicity_relNorm_eq_finsum
#check @Catalan.Thaine.multiplicity_eq_of_invariant_same_fiber
#print axioms Catalan.Thaine.multiplicity_eq_of_invariant_same_fiber
#check @Catalan.Thaine.class_power_eq_finsum_multiplicity
#print axioms Catalan.Thaine.class_power_eq_finsum_multiplicity
#check @Catalan.Thaine.multiplicity_relNorm_eq_degree_mul_of_unramified
#print axioms Catalan.Thaine.multiplicity_relNorm_eq_degree_mul_of_unramified
#check @Catalan.Thaine.multiplicity_relNorm_eq_of_unique_inertia_one
#print axioms Catalan.Thaine.multiplicity_relNorm_eq_of_unique_inertia_one
#check @Catalan.Thaine.multiplicity_hasFiniteSupport
#print axioms Catalan.Thaine.multiplicity_hasFiniteSupport
#check @Catalan.Thaine.principal_class_finsum_eq_zero
#print axioms Catalan.Thaine.principal_class_finsum_eq_zero
#check @Catalan.Thaine.auxiliary_norm_multiplicity_dvd_away
#print axioms Catalan.Thaine.auxiliary_norm_multiplicity_dvd_away
#check @Catalan.Thaine.auxiliary_norm_multiplicity_at
#print axioms Catalan.Thaine.auxiliary_norm_multiplicity_at
#check @Catalan.Thaine.exists_circular_class_relation
#print axioms Catalan.Thaine.exists_circular_class_relation

#check @Catalan.Thaine.inertiaDeg_int_eq_one_of_card
#print axioms Catalan.Thaine.inertiaDeg_int_eq_one_of_card
#check @Catalan.Thaine.real_prime_stabilizer_eq_bot
#print axioms Catalan.Thaine.real_prime_stabilizer_eq_bot
#check @Catalan.Thaine.exists_real_prime_orbit_equiv
#print axioms Catalan.Thaine.exists_real_prime_orbit_equiv
#check @Catalan.Thaine.residue_map_conjugate
#print axioms Catalan.Thaine.residue_map_conjugate
#check @Catalan.Thaine.conjugate_prime_eq_idealAct
#print axioms Catalan.Thaine.conjugate_prime_eq_idealAct
#check @Catalan.Thaine.exists_ordinary_class_action
#print axioms Catalan.Thaine.exists_ordinary_class_action
#check @Catalan.Thaine.finsum_reindex_subtype_equiv
#print axioms Catalan.Thaine.finsum_reindex_subtype_equiv
#check @Catalan.Thaine.groupAlgebraOfFunction
#print axioms Catalan.Thaine.groupAlgebraOfFunction
#check @Catalan.Thaine.groupAlgebraOfFunction_coeff
#print axioms Catalan.Thaine.groupAlgebraOfFunction_coeff
#check @Catalan.Thaine.groupAlgebraOfFunction_action
#print axioms Catalan.Thaine.groupAlgebraOfFunction_action
#check @Catalan.Thaine.ordinaryClassAction
#print axioms Catalan.Thaine.ordinaryClassAction
#check @Catalan.Thaine.ordinaryClassAction_mk
#print axioms Catalan.Thaine.ordinaryClassAction_mk
#check @Catalan.Thaine.classRepresentation
#print axioms Catalan.Thaine.classRepresentation
#check @Catalan.Thaine.classRepresentation_powerClass
#print axioms Catalan.Thaine.classRepresentation_powerClass
#check @Catalan.Thaine.classRepresentation_prime
#print axioms Catalan.Thaine.classRepresentation_prime
#check @Catalan.Thaine.twice_unitResidueCoordinate_of_residue_power
#print axioms Catalan.Thaine.twice_unitResidueCoordinate_of_residue_power
#check @Catalan.Thaine.exists_circular_orbit_relation
#print axioms Catalan.Thaine.exists_circular_orbit_relation
#check @Catalan.Thaine.circularCoordinateGalFintype
#print axioms Catalan.Thaine.circularCoordinateGalFintype
#check @Catalan.Thaine.circular_coordinates_annihilate_prime
#print axioms Catalan.Thaine.circular_coordinates_annihilate_prime

#check @Catalan.Thaine.galois_prime_norm_product
#print axioms Catalan.Thaine.galois_prime_norm_product
#check @Catalan.Thaine.prime_class_span_top
#print axioms Catalan.Thaine.prime_class_span_top
#check @Catalan.Thaine.integralCoordinateGalFintype
#print axioms Catalan.Thaine.integralCoordinateGalFintype
#check @Catalan.Thaine.integralUnit_coordinate_element
#print axioms Catalan.Thaine.integralUnit_coordinate_element
#check @Catalan.Thaine.realUnitAnnihilator
#print axioms Catalan.Thaine.realUnitAnnihilator
#check @Catalan.Thaine.realUnitAnnihilator_iff_circular_powerClass
#print axioms Catalan.Thaine.realUnitAnnihilator_iff_circular_powerClass
#check @Catalan.Thaine.classNormGalFintype
#print axioms Catalan.Thaine.classNormGalFintype
#check @Catalan.Thaine.classRepresentation_norm_prime_eq_zero
#print axioms Catalan.Thaine.classRepresentation_norm_prime_eq_zero
#check @Catalan.Thaine.classRepresentation_norm_eq_zero
#print axioms Catalan.Thaine.classRepresentation_norm_eq_zero
#check @Catalan.Thaine.classRepresentation_groupNorm_eq_zero
#print axioms Catalan.Thaine.classRepresentation_groupNorm_eq_zero
#check @Catalan.Thaine.real_unit_annihilator_kills_prime
#print axioms Catalan.Thaine.real_unit_annihilator_kills_prime
#check @Catalan.Thaine.real_unit_annihilator_kills_class_quotient
#print axioms Catalan.Thaine.real_unit_annihilator_kills_class_quotient

#check @Catalan.Thaine.literalFullCyclotomic
#print axioms Catalan.Thaine.literalFullCyclotomic
#check @Catalan.Thaine.literalRealAbelian
#print axioms Catalan.Thaine.literalRealAbelian
#check @Catalan.Thaine.literalRealUnitMap
#print axioms Catalan.Thaine.literalRealUnitMap
#check @Catalan.Thaine.literalRealPowerMap
#print axioms Catalan.Thaine.literalRealPowerMap
#check @Catalan.Thaine.literalFullCircularUnits
#print axioms Catalan.Thaine.literalFullCircularUnits
#check @Catalan.Thaine.literalFullCircularUnits_eq
#print axioms Catalan.Thaine.literalFullCircularUnits_eq
#check @Catalan.Thaine.literalRestriction
#print axioms Catalan.Thaine.literalRestriction
#check @Catalan.Thaine.literalRestriction_commutes
#print axioms Catalan.Thaine.literalRestriction_commutes
#check @Catalan.Thaine.literalRestrictionRing
#print axioms Catalan.Thaine.literalRestrictionRing
#check @Catalan.Thaine.full_real_circular_powerImage
#print axioms Catalan.Thaine.full_real_circular_powerImage
#check @Catalan.Thaine.literal_real_unit_powerMap_injective
#print axioms Catalan.Thaine.literal_real_unit_powerMap_injective
#check @Catalan.Thaine.literal_real_unit_action_compat
#print axioms Catalan.Thaine.literal_real_unit_action_compat
#check @Catalan.Thaine.literal_integralUnitPow_compat
#print axioms Catalan.Thaine.literal_integralUnitPow_compat
#check @Catalan.Thaine.fullAnnihilatorCyclotomic
#print axioms Catalan.Thaine.fullAnnihilatorCyclotomic
#check @Catalan.Thaine.literalFullUnitAnnihilator
#print axioms Catalan.Thaine.literalFullUnitAnnihilator
#check @Catalan.Thaine.unitClass_integralUnitPow
#print axioms Catalan.Thaine.unitClass_integralUnitPow
#check @Catalan.Thaine.literalFullUnitAnnihilator_iff_module_annihilator
#print axioms Catalan.Thaine.literalFullUnitAnnihilator_iff_module_annihilator
#check @Catalan.Thaine.literalClassRepresentation
#print axioms Catalan.Thaine.literalClassRepresentation
#check @Catalan.Thaine.literalClassRepresentation_reduce
#print axioms Catalan.Thaine.literalClassRepresentation_reduce
#check @Catalan.Thaine.literalFullUnitAnnihilator_restrict
#print axioms Catalan.Thaine.literalFullUnitAnnihilator_restrict
#check @Catalan.Thaine.fullThaineCyclotomic
#print axioms Catalan.Thaine.fullThaineCyclotomic
#check @Catalan.Thaine.literalFullUnitAnnihilator_kills_class_quotient
#print axioms Catalan.Thaine.literalFullUnitAnnihilator_kills_class_quotient
#check @Catalan.Thaine.literal_full_circular_annihilator_kills_class_quotient
#print axioms Catalan.Thaine.literal_full_circular_annihilator_kills_class_quotient

-- Integral class action and whole-q-primary good lift.
#check @Catalan.Thaine.exists_uniform_primary_exponent
#print axioms Catalan.Thaine.exists_uniform_primary_exponent
#check @Catalan.Thaine.exists_primary_action_nilpotence
#print axioms Catalan.Thaine.exists_primary_action_nilpotence
#check @Catalan.Thaine.exists_large_frobenius_fixed_power
#print axioms Catalan.Thaine.exists_large_frobenius_fixed_power
#check @Catalan.Thaine.integralClassRepresentation
#print axioms Catalan.Thaine.integralClassRepresentation
#check @Catalan.Thaine.integralClassRepresentation_apply
#print axioms Catalan.Thaine.integralClassRepresentation_apply
#check @Catalan.Thaine.powerClass_integralClassRepresentation
#print axioms Catalan.Thaine.powerClass_integralClassRepresentation
#check @Catalan.Thaine.integralClassRepresentation_image_nsmul
#print axioms Catalan.Thaine.integralClassRepresentation_image_nsmul
#check @Catalan.Thaine.primaryGroupRingFinite
#print axioms Catalan.Thaine.primaryGroupRingFinite
#check @Catalan.Thaine.primaryGroupRingCharP
#print axioms Catalan.Thaine.primaryGroupRingCharP
#check @Catalan.Thaine.groupRing_isReduced
#print axioms Catalan.Thaine.groupRing_isReduced
#check @Catalan.Thaine.exists_good_primary_power
#print axioms Catalan.Thaine.exists_good_primary_power
#check @Catalan.Thaine.literalIntegerClassAction
#print axioms Catalan.Thaine.literalIntegerClassAction
#check @Catalan.Thaine.literalIntegerClassAction_single
#print axioms Catalan.Thaine.literalIntegerClassAction_single
#check @Catalan.Thaine.literalIntegerClassAction_powerClass
#print axioms Catalan.Thaine.literalIntegerClassAction_powerClass
#check @Catalan.Thaine.literalIntegerClassAction_image_nsmul
#print axioms Catalan.Thaine.literalIntegerClassAction_image_nsmul
#check @Catalan.Thaine.primaryLiftCyclotomic
#print axioms Catalan.Thaine.primaryLiftCyclotomic
#check @Catalan.Thaine.primaryLiftGalComm
#print axioms Catalan.Thaine.primaryLiftGalComm
#check @Catalan.Thaine.literal_full_gal_card_not_dvd
#print axioms Catalan.Thaine.literal_full_gal_card_not_dvd
#check @Catalan.Thaine.literal_full_annihilator_good_primary_lift
#print axioms Catalan.Thaine.literal_full_annihilator_good_primary_lift
#check @Catalan.Thaine.literal_full_annihilator_kills_q_torsion
#print axioms Catalan.Thaine.literal_full_annihilator_kills_q_torsion

-- Literal lambda ideals and plus unit powers.
#check @Catalan.Thaine.normMapsCyclotomic
#print axioms Catalan.Thaine.normMapsCyclotomic
#check @Catalan.Thaine.literalFieldUnitMap
#print axioms Catalan.Thaine.literalFieldUnitMap
#check @Catalan.Thaine.literalNormMap
#print axioms Catalan.Thaine.literalNormMap
#check @Catalan.Thaine.literalNormMap_apply
#print axioms Catalan.Thaine.literalNormMap_apply
#check @Catalan.Thaine.literalLambdaNorm
#print axioms Catalan.Thaine.literalLambdaNorm
#check @Catalan.Thaine.literalLambdaNorm_apply
#print axioms Catalan.Thaine.literalLambdaNorm_apply
#check @Catalan.Thaine.literal_field_action_compat
#print axioms Catalan.Thaine.literal_field_action_compat
#check @Catalan.Thaine.literal_field_upow_compat
#print axioms Catalan.Thaine.literal_field_upow_compat
#check @Catalan.Thaine.literal_field_integral_unit
#print axioms Catalan.Thaine.literal_field_integral_unit
#check @Catalan.Thaine.integralClassRepresentation_mk_ipow
#print axioms Catalan.Thaine.integralClassRepresentation_mk_ipow
#check @Catalan.Thaine.upow_eq_unit_mul_pow_of_class_annihilation
#print axioms Catalan.Thaine.upow_eq_unit_mul_pow_of_class_annihilation
#check @Catalan.Thaine.quadraticNormCyclotomic
#print axioms Catalan.Thaine.quadraticNormCyclotomic
#check @Catalan.Thaine.literal_full_real_finrank
#print axioms Catalan.Thaine.literal_full_real_finrank
#check @Catalan.Thaine.literal_iota_fixes_real
#print axioms Catalan.Thaine.literal_iota_fixes_real
#check @Catalan.Thaine.literal_norm_eq_mul_iota
#print axioms Catalan.Thaine.literal_norm_eq_mul_iota
#check @Catalan.Thaine.classUnitPowerCyclotomic
#print axioms Catalan.Thaine.classUnitPowerCyclotomic
#check @Catalan.Thaine.literal_annihilator_unit_power
#print axioms Catalan.Thaine.literal_annihilator_unit_power
#check @Catalan.Thaine.normLambdaCyclotomic
#print axioms Catalan.Thaine.normLambdaCyclotomic
#check @Catalan.Thaine.literal_lambda_norm_ideal
#print axioms Catalan.Thaine.literal_lambda_norm_ideal
#check @Catalan.Thaine.literal_lambda_norm_principal_power
#print axioms Catalan.Thaine.literal_lambda_norm_principal_power
#check @Catalan.Thaine.normPowersCyclotomic
#print axioms Catalan.Thaine.normPowersCyclotomic
#check @Catalan.Thaine.normPowersGalComm
#print axioms Catalan.Thaine.normPowersGalComm
#check @Catalan.Thaine.literalNormMap_eq_mul_iota
#print axioms Catalan.Thaine.literalNormMap_eq_mul_iota
#check @Catalan.Thaine.literal_norm_upow_compat
#print axioms Catalan.Thaine.literal_norm_upow_compat
#check @Catalan.Thaine.lambdaPowerCyclotomic
#print axioms Catalan.Thaine.lambdaPowerCyclotomic
#check @Catalan.Thaine.literal_lambda_norm_unit_power
#print axioms Catalan.Thaine.literal_lambda_norm_unit_power
#check @Catalan.Thaine.literal_lambda_plus_unit_power
#print axioms Catalan.Thaine.literal_lambda_plus_unit_power

-- Original circular powers and symmetrized q-square congruence.
#check @Catalan.Thaine.circularizeGalComm
#print axioms Catalan.Thaine.circularizeGalComm
#check @Catalan.Thaine.topUnitAnn_integralUnitPow
#print axioms Catalan.Thaine.topUnitAnn_integralUnitPow
#check @Catalan.Thaine.circularize_unit_powers
#print axioms Catalan.Thaine.circularize_unit_powers
#check @Catalan.Thaine.raw_pi_circular_power
#print axioms Catalan.Thaine.raw_pi_circular_power
#check @Catalan.Thaine.symmetrizedRootFactor
#print axioms Catalan.Thaine.symmetrizedRootFactor
#check @Catalan.Thaine.symmetrizedRootFactor_coe
#print axioms Catalan.Thaine.symmetrizedRootFactor_coe
#check @Catalan.Thaine.symmetrizedRootFactor_congruent_one
#print axioms Catalan.Thaine.symmetrizedRootFactor_congruent_one
#check @Catalan.Thaine.symmetrizedRootFactor_congruent_one_of_solution
#print axioms Catalan.Thaine.symmetrizedRootFactor_congruent_one_of_solution
#check @Catalan.Thaine.plusCircularLiftGalComm
#print axioms Catalan.Thaine.plusCircularLiftGalComm
#check @Catalan.Thaine.exists_plus_topAnn_lift
#print axioms Catalan.Thaine.exists_plus_topAnn_lift
#check @Catalan.Thaine.circular_power_of_reduceFull_eq
#print axioms Catalan.Thaine.circular_power_of_reduceFull_eq
#check @Catalan.Thaine.literalCircularPowerCyclotomic
#print axioms Catalan.Thaine.literalCircularPowerCyclotomic
#check @Catalan.Thaine.literalCircularPowerGalComm
#print axioms Catalan.Thaine.literalCircularPowerGalComm
#check @Catalan.Thaine.literal_lambda_plus_circular_power
#print axioms Catalan.Thaine.literal_lambda_plus_circular_power
#check @Catalan.Thaine.rootCircularPowerCyclotomic
#print axioms Catalan.Thaine.rootCircularPowerCyclotomic
#check @Catalan.Thaine.rootCircularPowerGalComm
#print axioms Catalan.Thaine.rootCircularPowerGalComm
#check @Catalan.Thaine.literal_xm_zeta_plus_circular_power
#print axioms Catalan.Thaine.literal_xm_zeta_plus_circular_power
#check @Catalan.Thaine.literal_xm_zeta_circular_power
#print axioms Catalan.Thaine.literal_xm_zeta_circular_power
#check @Catalan.Thaine.literal_xm_zeta_circular_power_of_solution
#print axioms Catalan.Thaine.literal_xm_zeta_circular_power_of_solution

-- Primary localization, Runge contradiction, and complete original Catalan goals.
#check @Catalan.Thaine.primaryDenominators
#print axioms Catalan.Thaine.primaryDenominators
#check @Catalan.Thaine.primaryLocalization
#print axioms Catalan.Thaine.primaryLocalization
#check @Catalan.Thaine.primaryLocalizationIsLocalization
#print axioms Catalan.Thaine.primaryLocalizationIsLocalization
#check @Catalan.Thaine.primaryLocalizationClosed
#print axioms Catalan.Thaine.primaryLocalizationClosed
#check @Catalan.Thaine.primaryLocalizationResidue
#print axioms Catalan.Thaine.primaryLocalizationResidue
#check @Catalan.Thaine.primaryLocalizationResidue_algebraMap
#print axioms Catalan.Thaine.primaryLocalizationResidue_algebraMap
#check @Catalan.Thaine.exists_unit_of_power_in_integrally_closed
#print axioms Catalan.Thaine.exists_unit_of_power_in_integrally_closed
#check @Catalan.Thaine.bottomPowerGalComm
#print axioms Catalan.Thaine.bottomPowerGalComm
#check @Catalan.Thaine.bottomUnitAnn_integralUnitPow
#print axioms Catalan.Thaine.bottomUnitAnn_integralUnitPow
#check @Catalan.Thaine.pure_power_of_primary_powers
#print axioms Catalan.Thaine.pure_power_of_primary_powers
#check @Catalan.Thaine.primary_of_localized_unit_power
#print axioms Catalan.Thaine.primary_of_localized_unit_power
#check @Catalan.Thaine.exists_primary_localized_upow
#print axioms Catalan.Thaine.exists_primary_localized_upow
#check @Catalan.Thaine.ideal_triple_product_ne_bot
#print axioms Catalan.Thaine.ideal_triple_product_ne_bot
#check @Catalan.Thaine.primary_of_upow_eq_unit_mul_pow
#print axioms Catalan.Thaine.primary_of_upow_eq_unit_mul_pow
#check @Catalan.Thaine.literalPrimaryPowerCyclotomic
#print axioms Catalan.Thaine.literalPrimaryPowerCyclotomic
#check @Catalan.Thaine.literalPrimaryPowerGalComm
#print axioms Catalan.Thaine.literalPrimaryPowerGalComm
#check @Catalan.Thaine.literal_xm_zeta_primary_power
#print axioms Catalan.Thaine.literal_xm_zeta_primary_power
#check @Catalan.Thaine.literal_xm_zeta_primary_power_of_solution
#print axioms Catalan.Thaine.literal_xm_zeta_primary_power_of_solution
#check @Catalan.Thaine.literalPurePowerCyclotomic
#print axioms Catalan.Thaine.literalPurePowerCyclotomic
#check @Catalan.Thaine.literalPurePowerGalComm
#print axioms Catalan.Thaine.literalPurePowerGalComm
#check @Catalan.Thaine.literal_xm_zeta_pure_power_of_solution
#print axioms Catalan.Thaine.literal_xm_zeta_pure_power_of_solution
#check @Catalan.Thaine.odd_primes_no_solution_of_large
#print axioms Catalan.Thaine.odd_primes_no_solution_of_large
#check @Catalan.Thaine.prime_classification_of_odd_impossible
#print axioms Catalan.Thaine.prime_classification_of_odd_impossible
#check @Catalan.Thaine.natural_classification_of_prime
#print axioms Catalan.Thaine.natural_classification_of_prime
#check @Catalan.Thaine.literalRungeCyclotomic
#print axioms Catalan.Thaine.literalRungeCyclotomic
#check @Catalan.Thaine.literalRungeGalComm
#print axioms Catalan.Thaine.literalRungeGalComm
#check @Catalan.Thaine.literal_plus_top_bottom_eq_bot
#print axioms Catalan.Thaine.literal_plus_top_bottom_eq_bot
#check @Catalan.Thaine.literal_large_odd_primes_no_solution
#print axioms Catalan.Thaine.literal_large_odd_primes_no_solution
#check @Catalan.mihailescu_odd_primes
#print axioms Catalan.mihailescu_odd_primes
#check @Catalan.case_one
#print axioms Catalan.case_one
#check @Catalan.prime_exponent_classification
#print axioms Catalan.prime_exponent_classification
#check @Catalan.catalan_int
#print axioms Catalan.catalan_int
#check @Catalan.catalans_conjecture
#print axioms Catalan.catalans_conjecture
#check @Catalan.q_lt_three_sq
#print axioms Catalan.q_lt_three_sq

#check @Catalan.catalan_int_signed
#print axioms Catalan.catalan_int_signed

#check @Catalan.JSP.statement
#print axioms Catalan.JSP.statement
