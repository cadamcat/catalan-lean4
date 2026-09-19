import Catalan.Mihailescu.Ideal

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance instPositiveProductsFintypeG : Fintype (G p K) := Fintype.ofFinite _

lemma upow_xmζ_eq_nat_prod (x : ℤ) (hp2 : p ≠ 2) (Θ : R p K)
    (hΘ : ∀ τ, 0 ≤ Θ.coeff τ) :
    ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K) =
      ∏ τ : G p K, ((x : K) - τ (ζ p K)) ^ (Θ.coeff τ).toNat := by
  rw [upow_fintype]
  change (Units.coeHom K) (∏ τ, actUnit p K τ (xmζ p K x hp2) ^ Θ.coeff τ) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro τ _
  change (((actUnit p K τ (xmζ p K x hp2)) ^ Θ.coeff τ : Kˣ) : K) = _
  rw [Units.val_zpow_eq_zpow_val, ← Int.toNat_of_nonneg (hΘ τ), zpow_natCast]
  congr 1
  change τ ((x : K) - ζ p K) = (x : K) - τ (ζ p K)
  simp only [map_sub, map_intCast]

lemma integral_upow_xmζ_of_nonneg (x : ℤ) (hp2 : p ≠ 2) (Θ : R p K)
    (hΘ : ∀ τ, 0 ≤ Θ.coeff τ) :
    IsIntegral ℤ ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K) := by
  rw [upow_xmζ_eq_nat_prod p K x hp2 Θ hΘ]
  apply IsIntegral.prod
  intro τ _
  exact ((isIntegral_intCast x).sub (integral_conj_zeta p K τ)).pow _

omit [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] in
lemma sum_coeff_toNat_eq_size (Θ : R p K) (hΘ : ∀ τ, 0 ≤ Θ.coeff τ) :
    (∑ τ : G p K, (Θ.coeff τ).toNat : ℕ) = (size p K Θ).toNat := by
  have hs : (∑ τ : G p K, (Θ.coeff τ).toNat : ℕ) = size p K Θ := by
    push_cast
    rw [size_eq_sum]
    apply Finset.sum_congr rfl
    intro τ _
    rw [Int.toNat_of_nonneg (hΘ τ), abs_of_nonneg (hΘ τ)]
  exact_mod_cast congrArg Int.toNat hs

lemma infinitePlace_upow_xmζ_le (x : ℤ) (hp2 : p ≠ 2) (Θ : R p K)
    (hΘ : ∀ τ, 0 ≤ Θ.coeff τ) (w : InfinitePlace K) :
    w ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K) ≤
      ((|x| : ℝ) + 1) ^ (size p K Θ).toNat := by
  rw [upow_xmζ_eq_nat_prod p K x hp2 Θ hΘ, map_prod]
  have hfactor (τ : G p K) : w ((x : K) - τ (ζ p K)) ≤ (|x| : ℝ) + 1 := by
    rw [← w.mk_embedding, InfinitePlace.apply]
    simp only [map_sub, map_intCast]
    simpa only [norm_conj_zeta, Complex.norm_intCast, Int.norm_eq_abs] using
      (norm_sub_le (x : ℂ) (w.embedding (τ (ζ p K))))
  calc
    (∏ τ : G p K, w (((x : K) - τ (ζ p K)) ^ (Θ.coeff τ).toNat)) ≤
        ∏ τ : G p K, ((|x| : ℝ) + 1) ^ (Θ.coeff τ).toNat := by
      apply Finset.prod_le_prod
      · intro τ _; positivity
      · intro τ _
        rw [map_pow]
        exact pow_le_pow_left₀ (apply_nonneg w _) (hfactor τ) _
    _ = ((|x| : ℝ) + 1) ^ (size p K Θ).toNat := by
      rw [Finset.prod_pow_eq_pow_sum, sum_coeff_toNat_eq_size p K Θ hΘ]

end Catalan
