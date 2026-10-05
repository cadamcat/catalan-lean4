module

public import Catalan.Height.Basic

/-!
# `Catalan.Height.Liouville`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
variable {L : Type*} [Field L] [NumberField L]

lemma height_liouville_complex (φ : L →+* ℂ)
    (hφ : (InfinitePlace.mk φ).IsComplex) (a : L) (ha : a ≠ 0) :
    Real.exp (-((Module.finrank ℚ L : ℝ) * logHeight a)) ≤ ‖φ a‖ ^ 2 := by
  classical
  have hlocal : ((InfinitePlace.mk φ).mult : ℝ) *
      Real.posLog ((InfinitePlace.mk φ) a⁻¹) ≤ Height.logHeight₁ a⁻¹ := by
    rw [NumberField.logHeight₁_eq]
    have harch : ((InfinitePlace.mk φ).mult : ℝ) *
        Real.posLog ((InfinitePlace.mk φ) a⁻¹) ≤
        ∑ w : InfinitePlace L, (w.mult : ℝ) * Real.posLog (w a⁻¹) :=
      Finset.single_le_sum (f := fun w : InfinitePlace L =>
        (w.mult : ℝ) * Real.posLog (w a⁻¹))
        (fun w _ => mul_nonneg (Nat.cast_nonneg w.mult) Real.posLog_nonneg)
        (Finset.mem_univ (InfinitePlace.mk φ))
    have hfin : 0 ≤ ∑ᶠ v : FinitePlace L, Real.posLog (v a⁻¹) :=
      finsum_nonneg fun _ => Real.posLog_nonneg
    exact harch.trans (le_add_of_nonneg_right hfin)
  rw [hφ.mult_eq_two, Nat.cast_ofNat, InfinitePlace.apply, map_inv₀, norm_inv,
    Height.logHeight₁_inv] at hlocal
  have hd : (Module.finrank ℚ L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ L).ne'
  have hnormalize : (Module.finrank ℚ L : ℝ) * logHeight a = Height.logHeight₁ a := by
    rw [logHeight_eq_normalized, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hlog : Real.log (‖φ a‖⁻¹) ≤ Real.posLog (‖φ a‖⁻¹) := le_max_right _ _
  rw [Real.log_inv] at hlog
  have hlower : -((Module.finrank ℚ L : ℝ) * logHeight a) ≤
      2 * Real.log ‖φ a‖ := by
    rw [hnormalize]
    linarith
  have hφa : φ a ≠ 0 := by
    intro hz
    exact ha (φ.injective (hz.trans (map_zero φ).symm))
  have hnorm : 0 < ‖φ a‖ := norm_pos_iff.mpr hφa
  calc
    Real.exp (-((Module.finrank ℚ L : ℝ) * logHeight a)) ≤
        Real.exp (2 * Real.log ‖φ a‖) := Real.exp_le_exp.mpr hlower
    _ = (Real.exp (Real.log ‖φ a‖)) ^ 2 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log ‖φ a‖) 2
    _ = ‖φ a‖ ^ 2 := by rw [Real.exp_log hnorm]

end Catalan
