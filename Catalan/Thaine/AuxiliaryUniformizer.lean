import Catalan.Thaine.AuxiliaryIntegerData

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

def auxiliaryIntegerRoot (p ell : ℕ) [Fact ell.Prime] : 𝓞 (A3.Bsub p ell) :=
  (show IsPrimitiveRoot (auxiliaryRoot p ell) ell from
    IsPrimitiveRoot.coe_submonoidClass_iff.mp
      (A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos)).toInteger

def auxiliaryUniformizer (p ell : ℕ) [Fact ell.Prime] : 𝓞 (A3.Bsub p ell) :=
  auxiliaryIntegerRoot p ell - 1

def auxiliaryUniformizerRatio (p ell : ℕ) [Fact ell.Prime] (s : (ZMod ell)ˣ) :
    𝓞 (A3.Bsub p ell) :=
  ∑ i ∈ Finset.range (s : ZMod ell).val, auxiliaryIntegerRoot p ell ^ i

private lemma auxiliaryIntegerRoot_primitive (p ell : ℕ) [Fact ell.Prime] :
    IsPrimitiveRoot (auxiliaryIntegerRoot p ell) ell :=
  (IsPrimitiveRoot.coe_submonoidClass_iff.mp
    (A3.primitiveRoot_spec ell (Fact.out : ell.Prime).pos) :
      IsPrimitiveRoot (auxiliaryRoot p ell) ell).toInteger_isPrimitiveRoot

lemma auxiliaryUniformizer_ne_zero (p ell : ℕ) [Fact ell.Prime] :
    auxiliaryUniformizer p ell ≠ 0 :=
  sub_ne_zero.mpr ((auxiliaryIntegerRoot_primitive p ell).ne_one (Fact.out : ell.Prime).one_lt)

lemma auxiliaryUniformizer_action
    (p ell : ℕ) [Fact ell.Prime]
    (tau : A3.Bsub p ell ≃ₐ[A3.F p] A3.Bsub p ell) (s : (ZMod ell)ˣ)
    (htau : tau (auxiliaryRoot p ell) = auxiliaryRoot p ell ^ (s : ZMod ell).val) :
    A3.integralAut tau (auxiliaryUniformizer p ell) =
      auxiliaryUniformizer p ell * auxiliaryUniformizerRatio p ell s := by
  have htauO : A3.integralAut tau (auxiliaryIntegerRoot p ell) =
      auxiliaryIntegerRoot p ell ^ (s : ZMod ell).val := by
    apply RingOfIntegers.ext
    exact htau
  rw [auxiliaryUniformizer, map_sub, map_one, htauO, auxiliaryUniformizerRatio]
  exact (mul_geom_sum (auxiliaryIntegerRoot p ell) (s : ZMod ell).val).symm

lemma auxiliaryUniformizerRatio_residue
    (p ell : ℕ) [Fact ell.Prime] (s : (ZMod ell)ˣ)
    (P : HeightOneSpectrum (𝓞 (A3.Bsub p ell)))
    (hellP : (ell : 𝓞 (A3.Bsub p ell)) ∈ P.asIdeal) :
    auxiliaryUniformizerRatio p ell s ∉ P.asIdeal ∧
      Ideal.Quotient.mk P.asIdeal (auxiliaryUniformizerRatio p ell s) =
        ((s : ZMod ell).val : 𝓞 (A3.Bsub p ell) ⧸ P.asIdeal) := by
  let k := 𝓞 (A3.Bsub p ell) ⧸ P.asIdeal
  let instAuxiliaryRatioField : Field k := Ideal.Quotient.field P.asIdeal
  have instAuxiliaryRatioNeEll : NeZero ell := ⟨(Fact.out : ell.Prime).ne_zero⟩
  have hellzero : (ell : k) = 0 := by
    simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hellP)
  have instAuxiliaryRatioChar : CharP k ell :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : ell.Prime)).mpr hellzero
  have hpow : (Ideal.Quotient.mk P.asIdeal (auxiliaryIntegerRoot p ell)) ^ ell = 1 := by
    simpa only [map_pow, map_one] using congrArg (Ideal.Quotient.mk P.asIdeal)
      (auxiliaryIntegerRoot_primitive p ell).pow_eq_one
  have hrootbar : Ideal.Quotient.mk P.asIdeal (auxiliaryIntegerRoot p ell) = 1 := by
    have hzero : (Ideal.Quotient.mk P.asIdeal (auxiliaryIntegerRoot p ell) - 1) ^ ell = 0 := by
      rw [sub_pow_char, hpow]
      simp
    exact sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : ell.Prime).ne_zero).mp hzero)
  have hratio : Ideal.Quotient.mk P.asIdeal (auxiliaryUniformizerRatio p ell s) =
      ((s : ZMod ell).val : k) := by
    simp only [auxiliaryUniformizerRatio, map_sum, map_pow, hrootbar, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hspos : 0 < (s : ZMod ell).val := ZMod.val_pos.mpr s.ne_zero
  have hslt : (s : ZMod ell).val < ell := ZMod.val_lt _
  have hsne : ((s : ZMod ell).val : k) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt hspos hslt ((CharP.cast_eq_zero_iff k ell _).mp h)
  refine ⟨?_, hratio⟩
  intro hmem
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hratio] at hzero
  exact hsne hzero

end Catalan.Thaine
