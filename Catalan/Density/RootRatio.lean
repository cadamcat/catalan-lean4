module

public import Mathlib

/-!
# `Catalan.Density.RootRatio`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (n : ℕ) [NeZero n] (ζ : K) (hζ : IsPrimitiveRoot ζ n)
include hζ

lemma aut_fixed_of_pow_eq_one (σ : L ≃ₐ[K] L) (a : L) (ha : a ^ n = 1) :
    σ a = a := by
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n :=
    hζ.map_of_injective (algebraMap K L).injective
  obtain ⟨i, hi, hia⟩ := hζL.eq_pow_of_pow_eq_one ha
  rw [← hia, map_pow, σ.commutes, hia]

lemma root_ratio_independent (σ : L ≃ₐ[K] L) (r s : L)
    (hr : r ≠ 0) (hs : s ≠ 0) (hpow : r ^ n = s ^ n) :
    σ r / r = σ s / s := by
  have hquot : (r / s) ^ n = 1 := by
    rw [div_pow, hpow, div_self (pow_ne_zero n hs)]
  have hfix : σ (r / s) = r / s :=
    aut_fixed_of_pow_eq_one K L n ζ hζ σ (r / s) hquot
  have hdiv : σ r / σ s = r / s := by
    rw [← map_div₀, hfix]
  apply (div_eq_div_iff hr hs).2
  have hcross : σ r * s = r * σ s :=
    (div_eq_div_iff ((map_ne_zero σ).2 hs) hs).mp hdiv
  simpa [mul_comm] using hcross

lemma root_ratio_aut_mul (σ τ : L ≃ₐ[K] L) (r : L) (hr : r ≠ 0)
    (a : K) (hpow : r ^ n = algebraMap K L a) :
    (σ * τ) r / r = (σ r / r) * (τ r / r) := by
  have hA : algebraMap K L a ≠ 0 := by
    rw [← hpow]
    exact pow_ne_zero n hr
  have hτpow : (τ r) ^ n = algebraMap K L a := by
    rw [← map_pow, hpow, τ.commutes]
  have hquot : (τ r / r) ^ n = 1 := by
    rw [div_pow, hτpow, hpow, div_self hA]
  have hfix : σ (τ r / r) = τ r / r :=
    aut_fixed_of_pow_eq_one K L n ζ hζ σ (τ r / r) hquot
  calc
    (σ * τ) r / r = σ (τ r) / r := by rw [AlgEquiv.mul_apply]
    _ = (σ (τ r) / σ r) * (σ r / r) := by
      field_simp [(map_ne_zero σ).2 hr, hr]
    _ = σ (τ r / r) * (σ r / r) := by rw [map_div₀]
    _ = (τ r / r) * (σ r / r) := by rw [hfix]
    _ = (σ r / r) * (τ r / r) := by ring

end Catalan.Kummer
