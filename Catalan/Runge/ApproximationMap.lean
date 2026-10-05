module

public import Catalan.Runge.Definitions

/-!
# `Catalan.Runge.ApproximationMap`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.Runge

lemma scale_tail_eq_errorBound (q m : ℕ) (X : ℝ) (hX : 1 < X) :
    (q : ℝ) ^ D q m * X ^ m *
      (((2 * m).choose (m + 1) : ℝ) * (X⁻¹) ^ (m + 1) / (1 - X⁻¹) ^ (2 * m + 1)) =
      errorBound q m X := by
  have hX0 : X ≠ 0 := by linarith
  have hcancel : X ^ m * (X⁻¹) ^ (m + 1) = X⁻¹ := by
    rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hX0, one_pow, one_mul]
  calc
    _ = ((q : ℝ) ^ D q m * ((2 * m).choose (m + 1) : ℝ) *
        (X ^ m * (X⁻¹) ^ (m + 1))) / (1 - X⁻¹) ^ (2 * m + 1) := by ring
    _ = ((q : ℝ) ^ D q m * ((2 * m).choose (m + 1) : ℝ) * X⁻¹) /
        (1 - X⁻¹) ^ (2 * m + 1) := by rw [hcancel]
    _ = errorBound q m X := by
      simp only [errorBound, div_eq_mul_inv, mul_inv]
      ring

section Cyclotomic
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma map_rungeApprox (q : ℕ) (Theta : R p K) (m : ℕ) (x : ℤ) (hx : x ≠ 0)
    (τ : K →+* ℂ) :
    τ (rungeApprox p K q Theta m x) =
      (q : ℂ) ^ D q m * (x : ℂ) ^ m *
        ∑ k ∈ Finset.range (m + 1), τ (rungeCoeff p K q Theta k) * ((x : ℂ)⁻¹) ^ k := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  simp only [rungeApprox, map_mul, map_pow, map_natCast, map_sum, map_intCast]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Finset.mem_range_succ_iff.mp hk
  rw [pow_sub₀ (x : ℂ) hxC hkm, ← inv_pow]
  ring

end Cyclotomic
end Catalan.Runge
