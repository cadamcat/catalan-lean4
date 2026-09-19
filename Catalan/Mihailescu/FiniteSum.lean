import Catalan.Mihailescu.FiniteLogSum
import Catalan.Mihailescu.FiniteValues
import Catalan.Mihailescu.PowerDifference
import Catalan.Cyclotomic.Augmentation
import Catalan.Mihailescu.FiniteLower

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField

lemma finite_inverse_sum_bound_for_cyclotomic
    (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (m : ℕ) (hm : 0 < m) (a : K) (ha : a ≠ 0)
    (hlower : ∀ v : FinitePlace K, (v (m : K)) ^ (1 / (p - 1 : ℝ)) ≤ v a) :
    (∑ᶠ v : FinitePlace K, Real.log (max (v a⁻¹) 1)) ≤ Real.log (m : ℝ) := by
  have hd : (0 : ℝ) < p - 1 := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  have h := finite_log_inverse_sum_le_of_lower K m hm (1 / (p - 1 : ℝ))
    (by positivity) a ha hlower
  rw [cyclotomic_degree p K, Nat.cast_sub hp.out.one_le, Nat.cast_one] at h
  simpa only [one_div, inv_mul_cancel₀ hd.ne', one_mul] using h

lemma augAlpha_sub_one_ne_zero_of_size_two
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (q : ℕ) [Fact q.Prime] (x : ℤ) (hp2 : p ≠ 2)
    (Θ : mihAug p K q x hp2) (hs : size p K Θ.val ≤ 2) (hΘ : Θ.val ≠ 0) :
    (((augAlpha p K q x hp2 Θ : Kˣ) : K) - 1) ≠ 0 := by
  obtain ⟨σ, τ, hst, hshape⟩ := aug_size_two_shape p K Θ.val Θ.property.2 hs hΘ
  have hnumI : zetaConjInt p K τ - zetaConjInt p K σ ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [difference_ideal p K hp2 τ σ hst.symm]
    exact (ramifiedPrime_facts p K hp2).2.1
  have hnum : τ (ζ p K) - σ (ζ p K) ≠ 0 := by
    intro h
    apply hnumI
    apply RingOfIntegers.ext
    exact h
  have hden : (x : K) - τ (ζ p K) ≠ 0 := by
    intro hzero
    apply x_sub_ζ_ne_zero p K x hp2
    simpa only [map_sub, map_intCast, map_zero, AlgEquiv.symm_apply_apply] using
      congrArg τ.symm hzero
  have heq := prop42_power_difference p K q x hp2 Θ σ τ hshape
  intro ha
  rw [sub_eq_zero.mp ha, one_pow, sub_self] at heq
  exact div_ne_zero hnum hden heq.symm

section RadiusTwo
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)

lemma prop42_nonarch_ge_one (hp2 : p ≠ 2) (hx1 : x ≡ 1 [ZMOD p])
    (Θ : mihAug p K q x hp2) (hs : size p K Θ.val ≤ 2) (hΘ : Θ.val ≠ 0)
    (v : FinitePlace K) :
    1 ≤ v (((augAlpha p K q x hp2 Θ : Kˣ) : K) - 1) := by
  have h := prop42_finite_lower p K q x hp2 Θ hs hΘ v
  simpa only [pPrime, if_pos hx1, Nat.cast_one, map_one, Real.one_rpow] using h

lemma prop42_finite_inverse_sum (hp2 : p ≠ 2)
    (Θ : mihAug p K q x hp2) (hs : size p K Θ.val ≤ 2) (hΘ : Θ.val ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log
      (max (v ((((augAlpha p K q x hp2 Θ : Kˣ) : K) - 1)⁻¹)) 1)) ≤
      Real.log (pPrime p x : ℝ) := by
  exact finite_inverse_sum_bound_for_cyclotomic p K (pPrime p x) (pPrime_pos p x) _
    (augAlpha_sub_one_ne_zero_of_size_two p K q x hp2 Θ hs hΘ)
    (fun v => prop42_finite_lower p K q x hp2 Θ hs hΘ v)

end RadiusTwo
end Catalan
