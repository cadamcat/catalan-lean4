module

public import Catalan.Density.FStructure

/-!
# `Catalan.Density.RealPrimeCongruence`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

private lemma primitive_reduction_ne_one
    (R E : Type*) [CommRing R] [IsDomain R] [Field E]
    (f : R →+* E) (n : ℕ) (hn : 1 < n) (hnE : (n : E) ≠ 0)
    (z : R) (hz : IsPrimitiveRoot z n) : f z ≠ 1 := by
  intro hred
  have hsum : (Finset.range n).sum (fun i => z ^ i) = 0 := by
    have h := geom_sum_mul z n
    rw [hz.pow_eq_one, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (hz.ne_one hn))
  have h := congrArg f hsum
  apply hnE
  simpa only [map_sum, map_pow, hred, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h

private lemma eq_or_inv_of_trace_eq
    (E : Type*) [Field E] (a b : E) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + a⁻¹ = b + b⁻¹) : a = b ∨ a = b⁻¹ := by
  have hfactor : (a - b) * (a - b⁻¹) = 0 := by
    calc
      _ = a * (a + a⁻¹ - (b + b⁻¹)) := by field_simp; ring
      _ = 0 := by rw [h, sub_self, mul_zero]
  exact (mul_eq_zero.mp hfactor).imp sub_eq_zero.mp sub_eq_zero.mp

lemma real_prime_congruence
    (p ell : ℕ) (hp : p.Prime) (hell : ell.Prime) (hpell : p ≠ ell)
    (v : HeightOneSpectrum (𝓞 (F p)))
    (hcard : Nat.card (𝓞 (F p) ⧸ v.asIdeal) = ell) :
    (ell ≡ 1 [MOD p]) ∨ (ell + 1 ≡ 0 [MOD p]) := by
  classical
  let realPrimePNeZero : NeZero p := ⟨hp.ne_zero⟩
  let realPrimeEllFact : Fact ell.Prime := ⟨hell⟩
  let realPrimeOmegaAlgebraic : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  let E : IntermediateField (F p) Omega := IntermediateField.adjoin (F p) {primitiveRoot p}
  let realPrimeFiniteE : FiniteDimensional (F p) E := by
    dsimp only [E]
    apply IntermediateField.finiteDimensional_adjoin
    intro x _
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral.tower_top
  let realPrimeNumberFieldE : NumberField E := NumberField.of_module_finite (F p) E
  let z : E := ⟨primitiveRoot p, IntermediateField.subset_adjoin (F p) _ (by simp)⟩
  have hz : IsPrimitiveRoot z p := by
    apply IsPrimitiveRoot.coe_submonoidClass_iff.mp
    exact primitiveRoot_spec p hp.pos
  let zO : 𝓞 E := hz.toInteger
  let ziO : 𝓞 E := hz.inv.toInteger
  have hzO : IsPrimitiveRoot zO p := hz.toInteger_isPrimitiveRoot
  have hprod : zO * ziO = 1 := by
    apply RingOfIntegers.coe_injective
    change z * z⁻¹ = 1
    exact mul_inv_cancel₀ (hz.ne_zero hp.ne_zero)
  let t : F p := ⟨primitiveRoot p + (primitiveRoot p)⁻¹,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have htInt : IsIntegral ℤ t := by
    apply (isIntegral_algebraMap_iff (algebraMap (F p) Omega).injective).mp
    change IsIntegral ℤ (primitiveRoot p + (primitiveRoot p)⁻¹)
    exact ((primitiveRoot_spec p hp.pos).isIntegral hp.pos).add
      ((primitiveRoot_spec p hp.pos).inv.isIntegral hp.pos)
  let tO : 𝓞 (F p) := ⟨t, htInt⟩
  have htrace : algebraMap (𝓞 (F p)) (𝓞 E) tO = zO + ziO := by
    apply RingOfIntegers.coe_injective
    apply (algebraMap E Omega).injective
    rfl
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  let realPrimePMaximal : P.IsMaximal := hPmax
  let realPrimePLiesOver : P.LiesOver v.asIdeal := hPover
  let R := 𝓞 (F p) ⧸ v.asIdeal
  let S := 𝓞 E ⧸ P
  let realPrimeBaseField : Field R := Ideal.Quotient.field v.asIdeal
  let realPrimeTopField : Field S := Ideal.Quotient.field P
  let realPrimeResidueAlgebra : Algebra R S := inferInstance
  let realPrimeFiniteBase : Finite R := Nat.finite_of_card_ne_zero (hcard ▸ hell.ne_zero)
  let realPrimeFintypeBase : Fintype R := Fintype.ofFinite R
  have hcard' : Fintype.card R = ell := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hellR : (ell : R) = 0 := by
    simpa only [hcard'] using Nat.cast_card_eq_zero R
  have hellS : (ell : S) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap R S) hellR
  let realPrimeCharS : CharP S ell := (CharP.charP_iff_prime_eq_zero hell).mpr hellS
  have hpS : (p : S) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime S hp hpell.symm
  let red : 𝓞 E →+* S := Ideal.Quotient.mk P
  let b : S := red zO
  have hbpow : b ^ p = 1 := by
    dsimp only [b]
    rw [← map_pow, hzO.pow_eq_one, map_one]
  have hbne : b ≠ 1 := primitive_reduction_ne_one (𝓞 E) S red p hp.one_lt hpS zO hzO
  have hbprim : IsPrimitiveRoot b p := isPrimitiveRoot_of_mem_nthRootsFinset hp
    ((Polynomial.mem_nthRootsFinset hp.pos (1 : S)).mpr hbpow) hbne
  have hb0 : b ≠ 0 := hbprim.ne_zero hp.ne_zero
  have hzi : red ziO = b⁻¹ := by
    apply mul_left_cancel₀ hb0
    rw [mul_inv_cancel₀ hb0]
    change red zO * red ziO = 1
    rw [← map_mul, hprod, map_one]
  have htracebar : algebraMap R S (Ideal.Quotient.mk v.asIdeal tO) = b + b⁻¹ := by
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver P v.asIdeal, htrace, map_add, hzi]
  have htR : (Ideal.Quotient.mk v.asIdeal tO) ^ ell = Ideal.Quotient.mk v.asIdeal tO := by
    simpa only [Fintype.card_eq_nat_card, hcard] using
      FiniteField.pow_card (Ideal.Quotient.mk v.asIdeal tO)
  have htS : (b + b⁻¹) ^ ell = b + b⁻¹ := by
    have h := congrArg (algebraMap R S) htR
    simpa only [map_pow, htracebar] using h
  have htr : b ^ ell + (b ^ ell)⁻¹ = b + b⁻¹ := by
    rw [add_pow_char, inv_pow] at htS
    exact htS
  rcases eq_or_inv_of_trace_eq S (b ^ ell) b (pow_ne_zero ell hb0) hb0 htr with hpos | hneg
  · left
    have hpow : b ^ (ell - 1) = 1 := by
      apply mul_right_cancel₀ hb0
      rw [← pow_succ, Nat.sub_add_cancel hell.one_le, hpos, one_mul]
    exact ((Nat.modEq_iff_dvd' hell.one_le).mpr (hbprim.dvd_of_pow_eq_one (ell - 1) hpow)).symm
  · right
    have hpow : b ^ (ell + 1) = 1 := by rw [pow_succ, hneg, inv_mul_cancel₀ hb0]
    exact (hbprim.dvd_of_pow_eq_one (ell + 1) hpow).modEq_zero_nat

end Catalan.A3
