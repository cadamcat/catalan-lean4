import Catalan.Mihailescu.PhaseCore
import Catalan.Mihailescu.RadiusTwoArithmetic
import Catalan.Cyclotomic.Ramification

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField

lemma finitePlace_integral_le_one (K : Type*) [Field K] [NumberField K]
    (v : FinitePlace K) (a : 𝓞 K) : v (a : K) ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one K v.maximalIdeal a

lemma finitePlace_le_of_dvd (K : Type*) [Field K] [NumberField K]
    (v : FinitePlace K) (a b : 𝓞 K) (hab : a ∣ b) : v (b : K) ≤ v (a : K) := by
  obtain ⟨c, rfl⟩ := hab
  change v ((a : K) * (c : K)) ≤ v (a : K)
  rw [map_mul]
  exact mul_le_of_le_one_right (apply_nonneg v _) (finitePlace_integral_le_one K v c)

lemma finitePlace_eq_of_span_eq (K : Type*) [Field K] [NumberField K]
    (v : FinitePlace K) (a b : 𝓞 K)
    (hab : Ideal.span {a} = Ideal.span {b}) : v (a : K) = v (b : K) := by
  have h : Associated a b := Ideal.span_singleton_eq_span_singleton.mp hab
  exact le_antisymm (finitePlace_le_of_dvd K v b a h.symm.dvd)
    (finitePlace_le_of_dvd K v a b h.dvd)

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma finitePlace_root_distance_pow (v : FinitePlace K) (τ : G p K) :
    v (1 - τ (ζ p K)) ^ (p - 1) = v (p : K) := by
  have hz : IsPrimitiveRoot (τ (ζ p K)) p := (ζ_spec p K).map_of_injective τ.injective
  have hspan : Ideal.span {((hz.toInteger - 1) ^ (p - 1))} =
      Ideal.span {(p : 𝓞 K)} :=
    Ideal.span_singleton_eq_span_singleton.mpr
      (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hz)
  have h := finitePlace_eq_of_span_eq K v _ _ hspan
  change v ((τ (ζ p K) - 1) ^ (p - 1)) = v (p : K) at h
  rw [map_pow, ← neg_sub (1 : K) (τ (ζ p K)), map_neg_eq_map v] at h
  exact h

lemma finitePlace_root_difference_pow (hp2 : p ≠ 2) (v : FinitePlace K)
    (σ τ : G p K) (hst : σ ≠ τ) :
    v (τ (ζ p K) - σ (ζ p K)) ^ (p - 1) = v (p : K) := by
  have hspan : Ideal.span {(zetaConjInt p K τ - zetaConjInt p K σ) ^ (p - 1)} =
      Ideal.span {(p : 𝓞 K)} := by
    rw [← Ideal.span_singleton_pow, difference_ideal p K hp2 τ σ hst.symm,
      (ramifiedPrime_facts p K hp2).2.2.1]
  have h := finitePlace_eq_of_span_eq K v _ _ hspan
  change v ((τ (ζ p K) - σ (ζ p K)) ^ (p - 1)) = v (p : K) at h
  rwa [map_pow] at h

end Cyclotomic
end Catalan
