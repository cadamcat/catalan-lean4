import Catalan.Cyclotomic.Ramification
import Mathlib.RingTheory.Norm.Basic

open NumberField Polynomial
noncomputable section
namespace Catalan

/-- Evaluation of the minimal polynomial computes the norm of a shifted power-basis generator. -/
lemma norm_algebraMap_sub_powerBasis_gen {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (b : PowerBasis R S) (x : R) :
    Algebra.norm R (algebraMap R S x - b.gen) = (minpoly R b.gen).eval x := by
  classical
  rw [Algebra.norm_eq_matrix_det b.basis, map_sub, AlgHom.commutes,
    ← charpoly_leftMulMatrix b, Matrix.eval_charpoly]
  rfl

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The signed integer norm of `x - ζ` is the prime cyclotomic polynomial evaluated at `x`. -/
lemma norm_x_sub_zeta (x : ℤ) :
    Algebra.norm ℤ ((x : 𝓞 K) - zetaConjInt p K 1) =
      ∑ i ∈ Finset.range p, x ^ i := by
  let : NeZero p := ⟨hp.out.ne_zero⟩
  rw [zetaConjInt_one]
  have h := norm_algebraMap_sub_powerBasis_gen (ζ_spec p K).integralPowerBasis x
  simp only [IsPrimitiveRoot.integralPowerBasis_gen, eq_intCast] at h
  rw [h]
  have hmin : minpoly ℤ (ζ_spec p K).toInteger = cyclotomic p ℤ := by
    rw [← RingOfIntegers.minpoly_coe]
    exact (cyclotomic_eq_minpoly (ζ_spec p K) hp.out.pos).symm
  rw [hmin, cyclotomic_prime]
  simp

lemma absNorm_span_x_sub_zeta (x : ℤ) :
    Ideal.absNorm (Ideal.span {(x : 𝓞 K) - zetaConjInt p K 1}) =
      (∑ i ∈ Finset.range p, x ^ i).natAbs := by
  rw [Ideal.absNorm_span_singleton, norm_x_sub_zeta p K]

end Catalan
