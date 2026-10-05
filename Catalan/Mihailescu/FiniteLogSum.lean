module

public import Mathlib

/-!
# `Catalan.Mihailescu.FiniteLogSum`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan
open NumberField

lemma finite_log_inverse_sum_le_of_lower
    (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) (a : K) (ha : a ≠ 0)
    (hlower : ∀ v : FinitePlace K, (v (m : K)) ^ r ≤ v a) :
    (∑ᶠ v : FinitePlace K, Real.log (max (v a⁻¹) 1)) ≤
      r * (Module.finrank ℚ K : ℝ) * Real.log (m : ℝ) := by
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmp (v : FinitePlace K) : 0 < v (m : K) := FinitePlace.pos_iff.mpr hmK
  have hml (v : FinitePlace K) : v (m : K) ≤ 1 :=
    IsNonarchimedean.apply_natCast_le_one (map_zero_le v 1) (map_one v)
      (fun x y => FinitePlace.add_le v x y)
  have hpoint (v : FinitePlace K) :
      Real.log (max (v a⁻¹) 1) ≤ -r * Real.log (v (m : K)) := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos (hmp v) r) (hlower v)
    rw [Real.log_rpow (hmp v)] at hlog
    have hmLog : Real.log (v (m : K)) ≤ 0 := Real.log_nonpos (hmp v).le (hml v)
    by_cases hv : v a⁻¹ ≤ 1
    · rw [max_eq_right hv, Real.log_one]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hr) hmLog
    · rw [max_eq_left (le_of_not_ge hv), map_inv₀, Real.log_inv]
      linarith
  have hfa : Function.HasFiniteSupport
      (fun v : FinitePlace K => Real.log (max (v a⁻¹) 1)) := by
    apply (FinitePlace.hasFiniteMulSupport (inv_ne_zero ha)).subset
    intro v hv
    change v a⁻¹ ≠ 1
    intro h
    have hv' : Real.log (max (v a⁻¹) 1) ≠ 0 := hv
    exact hv' (by simp [h])
  have hfm : Function.HasFiniteSupport
      (fun v : FinitePlace K => -r * Real.log (v (m : K))) := by
    apply (FinitePlace.hasFiniteMulSupport hmK).subset
    intro v hv
    change v (m : K) ≠ 1
    intro h
    have hv' : -r * Real.log (v (m : K)) ≠ 0 := hv
    exact hv' (by simp [h])
  have hsum : (∑ᶠ v : FinitePlace K, Real.log (v (m : K))) =
      -(Module.finrank ℚ K : ℝ) * Real.log (m : ℝ) := by
    rw [← Real.log_finprod hmp, FinitePlace.prod_eq_inv_abs_norm hmK, Algebra.norm_natCast]
    simp [Real.log_inv, Real.log_pow]
  calc
    (∑ᶠ v : FinitePlace K, Real.log (max (v a⁻¹) 1)) ≤
        ∑ᶠ v : FinitePlace K, -r * Real.log (v (m : K)) :=
      finsum_le_finsum' hfa hfm hpoint
    _ = -r * (∑ᶠ v : FinitePlace K, Real.log (v (m : K))) :=
      (mul_finsum _ _).symm
    _ = r * (Module.finrank ℚ K : ℝ) * Real.log (m : ℝ) := by rw [hsum]; ring

end Catalan
