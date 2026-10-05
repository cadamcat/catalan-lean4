module

public import Mathlib

/-!
# `Catalan.CaseTwo.RadiusArithmetic`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan

lemma quotient_radius_le (p q : ℕ) (hp : 1 < p) :
    ((p : ℝ) - 1) * (q / (p - 1) ^ 2 : ℕ) ≤ (q : ℝ) / ((p : ℝ) - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hd : 0 < (p : ℝ) - 1 := by linarith
  have hn := Nat.div_mul_le_self q ((p - 1) ^ 2)
  have hr : (q / (p - 1) ^ 2 : ℕ) * (((p - 1 : ℕ) : ℝ) ^ 2) ≤ (q : ℝ) := by
    exact_mod_cast hn
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at hr
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hr]

end Catalan
